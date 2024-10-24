/*
 * For PostgreSQL Database Management System:
 * (formerly known as Postgres, then as Postgres95)
 *
 * Portions Copyright (c) 1996-2010, The PostgreSQL Global Development Group
 *
 * Portions Copyright (c) 1994, The Regents of the University of California
 *
 * Permission to use, copy, modify, and distribute this software and its documentation for any purpose,
 * without fee, and without a written agreement is hereby granted, provided that the above copyright notice
 * and this paragraph and the following two paragraphs appear in all copies.
 *
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY
 * OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING,
 * BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 * THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA
 * HAS NO OBLIGATIONS TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 */

#include "postgres.h"

#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "parser/parse_relation.h"
#include "rewrite/rewriteHandler.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rowsecurity.h"
#include "utils/acl.h"

#include "catalog/ag_label.h"
#include "commands/label_commands.h"
#include "executor/cypher_utils.h"
#include "utils/ag_cache.h"

static void sort_policies_by_name(List *policies);
static int row_security_policy_cmp(const ListCell *a, const ListCell *b);
static bool check_role_for_policy(ArrayType *policy_roles, Oid user_id);
static int get_rtindex_using_relid(List *rtable, Oid relid);

/*
 * Given the graph name and the label name, create a ResultRelInfo for the table
 * those two variables represent. Open the Indices too.
 */
ResultRelInfo *create_entity_result_rel_info(EState *estate, char *graph_name,
                                             char *label_name)
{
    RangeVar *rv = NULL;
    Relation label_relation = NULL;
    ResultRelInfo *resultRelInfo = NULL;
    ParseState *pstate = NULL;
    #if PG_VERSION_NUM >= 160000
    RangeTblEntry *rte = NULL;
    #endif
    int rri = 0;

    /* create a new parse state for this operation */
    pstate = make_parsestate(NULL);

    resultRelInfo = palloc(sizeof(ResultRelInfo));

    if (strlen(label_name) == 0)
    {
        rv = makeRangeVar(graph_name, AG_DEFAULT_LABEL_VERTEX, -1);
    }
    else
    {
        rv = makeRangeVar(graph_name, label_name, -1);
    }

    label_relation = parserOpenTable(pstate, rv, RowExclusiveLock);

    #if PG_VERSION_NUM >= 160000
    /*
     * Get the rte to determine the correct perminfoindex value. Some rtes
     * may have it set up, some created here (executor) may not.
     *
     * Note: The RTEPermissionInfo structure was added in PostgreSQL version 16.
     *
     * Note: We use the list_length because exec_rt_fetch starts at 1, not 0.
     *       Doing this gives us the last rte in the es_range_table list, which
     *       is the rte in question.
     *
     *       If the rte is created here and doesn't have a perminfoindex, we
     *       need to pass on a 0. Otherwise, later on GetResultRTEPermissionInfo
     *       will attempt to get the rte's RTEPermissionInfo data, which doesn't
     *       exist.
     *
     * TODO: Ideally, we should consider creating the RTEPermissionInfo data,
     *       but as this is just a read of the label relation, it is likely
     *       unnecessary.
     */
    rte = exec_rt_fetch(list_length(estate->es_range_table), estate);
    rri = (rte->perminfoindex == 0) ? 0 : list_length(estate->es_range_table);
    #else
    rri = list_length(estate->es_range_table);
    #endif

    /* initialize the resultRelInfo */
    InitResultRelInfo(resultRelInfo, label_relation, rri, NULL,
                      estate->es_instrument);

    /* open the indices */
    ExecOpenIndices(resultRelInfo, false);

    free_parsestate(pstate);

    return resultRelInfo;
}

/* close the result_rel_info and close all the indices */
void destroy_entity_result_rel_info(ResultRelInfo *result_rel_info)
{
    /* close the indices */
    ExecCloseIndices(result_rel_info);

    /* close the rel */
    table_close(result_rel_info->ri_RelationDesc, RowExclusiveLock);
}

TupleTableSlot *populate_vertex_tts(
    TupleTableSlot *elemTupleSlot, agtype_value *id, agtype_value *properties)
{
    bool properties_isnull;

    if (id == NULL)
    {
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("vertex id field cannot be NULL")));
    }

    properties_isnull = properties == NULL;

    elemTupleSlot->tts_values[vertex_tuple_id] = GRAPHID_GET_DATUM(id->val.int_value);
    elemTupleSlot->tts_isnull[vertex_tuple_id] = false;

    elemTupleSlot->tts_values[vertex_tuple_properties] =
        AGTYPE_P_GET_DATUM(agtype_value_to_agtype(properties));
    elemTupleSlot->tts_isnull[vertex_tuple_properties] = properties_isnull;

    return elemTupleSlot;
}

TupleTableSlot *populate_edge_tts(
    TupleTableSlot *elemTupleSlot, agtype_value *id, agtype_value *startid,
    agtype_value *endid, agtype_value *properties)
{
    bool properties_isnull;

    if (id == NULL)
    {
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("edge id field cannot be NULL")));
    }
    if (startid == NULL)
    {
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("edge start_id field cannot be NULL")));
    }

    if (endid == NULL)
    {
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("edge end_id field cannot be NULL")));
    }

    properties_isnull = properties == NULL;

    elemTupleSlot->tts_values[edge_tuple_id] =
        GRAPHID_GET_DATUM(id->val.int_value);
    elemTupleSlot->tts_isnull[edge_tuple_id] = false;

    elemTupleSlot->tts_values[edge_tuple_start_id] =
        GRAPHID_GET_DATUM(startid->val.int_value);
    elemTupleSlot->tts_isnull[edge_tuple_start_id] = false;

    elemTupleSlot->tts_values[edge_tuple_end_id] =
        GRAPHID_GET_DATUM(endid->val.int_value);
    elemTupleSlot->tts_isnull[edge_tuple_end_id] = false;

    elemTupleSlot->tts_values[edge_tuple_properties] =
        AGTYPE_P_GET_DATUM(agtype_value_to_agtype(properties));
    elemTupleSlot->tts_isnull[edge_tuple_properties] = properties_isnull;

    return elemTupleSlot;
}


/*
 * Find out if the entity still exists. This is for 'implicit' deletion
 * of an entity.
 */
bool entity_exists(EState *estate, Oid graph_oid, graphid id)
{
    label_cache_data *label;
    ScanKeyData scan_keys[1];
    TableScanDesc scan_desc;
    HeapTuple tuple;
    Relation rel;
    bool result = true;

    /*
     * Extract the label id from the graph id and get the table name
     * the entity is part of.
     */
    label = search_label_graph_oid_cache(graph_oid, GET_LABEL_ID(id));

    /* Setup the scan key to be the graphid */
    ScanKeyInit(&scan_keys[0], 1, BTEqualStrategyNumber,
                F_GRAPHIDEQ, GRAPHID_GET_DATUM(id));

    rel = table_open(label->relation, RowExclusiveLock);
    scan_desc = table_beginscan(rel, estate->es_snapshot, 1, scan_keys);

    tuple = heap_getnext(scan_desc, ForwardScanDirection);

    /*
     * If a single tuple was returned, the tuple is still valid, otherwise'
     * set to false.
     */
    if (!HeapTupleIsValid(tuple))
    {
        result = false;
    }

    table_endscan(scan_desc);
    table_close(rel, RowExclusiveLock);

    return result;
}

/*
 * Insert the edge/vertex tuple into the table and indices. Check that the
 * table's constraints have not been violated.
 *
 * This function defaults to, and flags for update, the currentCommandId. If
 * you need to pass a specific cid and avoid using the currentCommandId, use
 * insert_entity_tuple_cid instead.
 */
HeapTuple insert_entity_tuple(ResultRelInfo *resultRelInfo,
                              TupleTableSlot *elemTupleSlot,
                              EState *estate)
{
    return insert_entity_tuple_cid(resultRelInfo, elemTupleSlot, estate,
                                   GetCurrentCommandId(true));
}

/*
 * Insert the edge/vertex tuple into the table and indices. Check that the
 * table's constraints have not been violated.
 *
 * This function uses the passed cid for updates.
 */
HeapTuple insert_entity_tuple_cid(ResultRelInfo *resultRelInfo,
                                  TupleTableSlot *elemTupleSlot,
                                  EState *estate, CommandId cid)
{
    HeapTuple tuple = NULL;

    ExecStoreVirtualTuple(elemTupleSlot);
    tuple = ExecFetchSlotHeapTuple(elemTupleSlot, true, NULL);

    /* Check the constraints of the tuple */
    tuple->t_tableOid = RelationGetRelid(resultRelInfo->ri_RelationDesc);
    if (resultRelInfo->ri_RelationDesc->rd_att->constr != NULL)
    {
        ExecConstraints(resultRelInfo, elemTupleSlot, estate);
    }

    if (resultRelInfo->ri_WithCheckOptions)
    {
        ExecWithCheckOptions(WCO_RLS_INSERT_CHECK, resultRelInfo,
                             elemTupleSlot, estate);
    }

    /* Insert the tuple normally */
    table_tuple_insert(resultRelInfo->ri_RelationDesc, elemTupleSlot, cid, 0,
                       NULL);

    /* Insert index entries for the tuple */
    if (resultRelInfo->ri_NumIndices > 0)
    {
        #if PG_VERSION_NUM >= 160000
        ExecInsertIndexTuples(resultRelInfo, elemTupleSlot, estate,
                              false, false, NULL, NIL, false);
        #else
        ExecInsertIndexTuples(resultRelInfo, elemTupleSlot, estate,
                              false, false, NULL, NIL);
        #endif
    }

    return tuple;
}

static int get_rtindex_using_relid(List *rtable, Oid relid)
{
    ListCell *lc;
    int rt_index = 1;

    foreach (lc, rtable)
    {
        RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);

        if (rte->relid == relid)
        {
            return rt_index;
        }

        rt_index++;
    }

    return -1;
}

/*
 * WithCheckOptions are added during the rewrite phase, but since we 
 * have all queries with CMD_SELECT commandTag, they do not get added
 * for CREATE/SET/MERGE/DELETE cypher clauses. This function compensates
 * for that and adds the WithCheckOptions for the relation.
 */
void setup_wcos(ResultRelInfo *resultRelInfo, EState *estate,
                CustomScanState *node, CmdType cmd)
{
    List *permissive_policies;
    List *restrictive_policies;
    List *withCheckOptions = NIL;
    List *wcoExprs = NIL;
    ListCell *lc;
    Relation rel;
    Oid user_id;
    int rt_index;
    WCOKind wco_kind;
    bool hasSubLinks = false;
    RangeTblEntry *rte;
    #if PG_VERSION_NUM >= 160000
    RTEPermissionInfo *perminfo;
    #endif

    if (cmd == CMD_INSERT)
    {
        wco_kind = WCO_RLS_INSERT_CHECK;
    }
    else if (cmd == CMD_UPDATE)
    {
        wco_kind = WCO_RLS_UPDATE_CHECK;
    }
    else
    {
        ereport(ERROR,
                (errmsg_internal("unexpected command type for setup_wcos")));
    }

    rel = resultRelInfo->ri_RelationDesc;
    rt_index = get_rtindex_using_relid(estate->es_range_table, rel->rd_id);
    user_id = GetUserId();

    get_policies_for_relation(rel, cmd, user_id,
                              &permissive_policies,
                              &restrictive_policies);

    add_with_check_options(rel, rt_index,
                           wco_kind,
                           permissive_policies,
                           restrictive_policies,
                           &withCheckOptions,
                           &hasSubLinks,
                           false);

    rte = exec_rt_fetch(rt_index, estate);

    #if PG_VERSION_NUM >= 160000
    perminfo = getRTEPermissionInfo(estate->es_rteperminfos, rte);
    if (perminfo->requiredPerms & ACL_SELECT)
    #else
    if (rte->requiredPerms & ACL_SELECT)
    #endif
    {
        List *select_permissive_policies = NIL;
        List *select_restrictive_policies = NIL;

        get_policies_for_relation(rel, CMD_SELECT, user_id,
                                  &select_permissive_policies,
                                  &select_restrictive_policies);
        add_with_check_options(rel, rt_index,
                               wco_kind,
                               select_permissive_policies,
                               select_restrictive_policies,
                               &withCheckOptions,
                               &hasSubLinks,
                               true);
    }

    foreach(lc, withCheckOptions)
    {
        WithCheckOption *wco = lfirst_node(WithCheckOption, lc);
        ExprState *wcoExpr;

        if (!IsA(wco->qual, List))
        {
            wco->qual = (Node *) list_make1(wco->qual);
        }
        wcoExpr = ExecInitQual((List *) wco->qual,
                                (PlanState *) node);

        wcoExprs = lappend(wcoExprs, wcoExpr);
    }

    resultRelInfo->ri_WithCheckOptions = withCheckOptions;
    resultRelInfo->ri_WithCheckOptionExprs = wcoExprs;
}

/* 
 * Copied from src/backend/executor/row_security.c
 *
 * add_with_check_options
 *
 * Add WithCheckOptions of the specified kind to check that new records
 * added by an INSERT or UPDATE are consistent with the specified RLS
 * policies.  Normally new data must satisfy the WITH CHECK clauses from the
 * policies.  If a policy has no explicit WITH CHECK clause, its USING clause
 * is used instead.  In the special case of an UPDATE arising from an
 * INSERT ... ON CONFLICT DO UPDATE, existing records are first checked using
 * a WCO_RLS_CONFLICT_CHECK WithCheckOption, which always uses the USING
 * clauses from RLS policies.
 *
 * New WCOs are added to withCheckOptions, and hasSubLinks is set to true if
 * any of the check clauses added contain sublink subqueries.
 */
void
add_with_check_options(Relation rel,
                       int rt_index,
                       WCOKind kind,
                       List *permissive_policies,
                       List *restrictive_policies,
                       List **withCheckOptions,
                       bool *hasSubLinks,
                       bool force_using)
{
    ListCell   *item;
    List	   *permissive_quals = NIL;

#define QUAL_FOR_WCO(policy) \
    ( !force_using && \
        (policy)->with_check_qual != NULL ? \
        (policy)->with_check_qual : (policy)->qual )

    /*
     * First collect up the permissive policy clauses, similar to
     * add_security_quals.
     */
    foreach(item, permissive_policies)
    {
        RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);
        Expr	   *qual = QUAL_FOR_WCO(policy);

        if (qual != NULL)
        {
            permissive_quals = lappend(permissive_quals, copyObject(qual));
            *hasSubLinks |= policy->hassublinks;
        }
    }

    /*
     * There must be at least one permissive qual found or no rows are allowed
     * to be added.  This is the same as in add_security_quals.
     *
     * If there are no permissive_quals then we fall through and return a
     * single 'false' WCO, preventing all new rows.
     */
    if (permissive_quals != NIL)
    {
        /*
         * Add a single WithCheckOption for all the permissive policy clauses,
         * combining them together using OR.  This check has no policy name,
         * since if the check fails it means that no policy granted permission
         * to perform the update, rather than any particular policy being
         * violated.
         */
        WithCheckOption *wco;

        wco = makeNode(WithCheckOption);
        wco->kind = kind;
        wco->relname = pstrdup(RelationGetRelationName(rel));
        wco->polname = NULL;
        wco->cascaded = false;

        if (list_length(permissive_quals) == 1)
            wco->qual = (Node *) linitial(permissive_quals);
        else
            wco->qual = (Node *) makeBoolExpr(OR_EXPR, permissive_quals, -1);

        ChangeVarNodes(wco->qual, 1, rt_index, 0);

        *withCheckOptions = list_append_unique(*withCheckOptions, wco);

        /*
         * Now add WithCheckOptions for each of the restrictive policy clauses
         * (which will be combined together using AND).  We use a separate
         * WithCheckOption for each restrictive policy to allow the policy
         * name to be included in error reports if the policy is violated.
         */
        foreach(item, restrictive_policies)
        {
            RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);
            Expr	   *qual = QUAL_FOR_WCO(policy);

            if (qual != NULL)
            {
                qual = copyObject(qual);
                ChangeVarNodes((Node *) qual, 1, rt_index, 0);

                wco = makeNode(WithCheckOption);
                wco->kind = kind;
                wco->relname = pstrdup(RelationGetRelationName(rel));
                wco->polname = pstrdup(policy->policy_name);
                wco->qual = (Node *) qual;
                wco->cascaded = false;

                *withCheckOptions = list_append_unique(*withCheckOptions, wco);
                *hasSubLinks |= policy->hassublinks;
            }
        }
    }
    else
    {
        /*
         * If there were no policy clauses to check new data, add a single
         * always-false WCO (a default-deny policy).
         */
        WithCheckOption *wco;

        wco = makeNode(WithCheckOption);
        wco->kind = kind;
        wco->relname = pstrdup(RelationGetRelationName(rel));
        wco->polname = NULL;
        wco->qual = (Node *) makeConst(BOOLOID, -1, InvalidOid,
                                        sizeof(bool), BoolGetDatum(false),
                                        false, true);
        wco->cascaded = false;

        *withCheckOptions = lappend(*withCheckOptions, wco);
    }
}

/* 
 * Copied from src/backend/executor/row_security.c
 *
 * get_policies_for_relation
 *
 * Returns lists of permissive and restrictive policies to be applied to the
 * specified relation, based on the command type and role.
 *
 * This includes any policies added by extensions.
 */
void
get_policies_for_relation(Relation relation, CmdType cmd, Oid user_id,
                          List **permissive_policies,
                          List **restrictive_policies)
{
    ListCell   *item;

    *permissive_policies = NIL;
    *restrictive_policies = NIL;

    /* First find all internal policies for the relation. */
    foreach(item, relation->rd_rsdesc->policies)
    {
        bool		cmd_matches = false;
        RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

        /* Always add ALL policies, if they exist. */
        if (policy->polcmd == '*')
            cmd_matches = true;
        else
        {
            /* Check whether the policy applies to the specified command type */
            switch (cmd)
            {
                case CMD_SELECT:
                    if (policy->polcmd == ACL_SELECT_CHR)
                        cmd_matches = true;
                    break;
                case CMD_INSERT:
                    if (policy->polcmd == ACL_INSERT_CHR)
                        cmd_matches = true;
                    break;
                case CMD_UPDATE:
                    if (policy->polcmd == ACL_UPDATE_CHR)
                        cmd_matches = true;
                    break;
                case CMD_DELETE:
                    if (policy->polcmd == ACL_DELETE_CHR)
                        cmd_matches = true;
                    break;
                case CMD_MERGE:

                    /*
                     * We do not support a separate policy for MERGE command.
                     * Instead it derives from the policies defined for other
                     * commands.
                     */
                    break;
                default:
                    elog(ERROR, "unrecognized policy command type %d",
                            (int) cmd);
                    break;
            }
        }

        /*
         * Add this policy to the relevant list of policies if it applies to
         * the specified role.
         */
        if (cmd_matches && check_role_for_policy(policy->roles, user_id))
        {
            if (policy->permissive)
                *permissive_policies = lappend(*permissive_policies, policy);
            else
                *restrictive_policies = lappend(*restrictive_policies, policy);
        }
    }

    /*
     * We sort restrictive policies by name so that any WCOs they generate are
     * checked in a well-defined order.
     */
    sort_policies_by_name(*restrictive_policies);

    /*
     * Then add any permissive or restrictive policies defined by extensions.
     * These are simply appended to the lists of internal policies, if they
     * apply to the specified role.
     */
    if (row_security_policy_hook_restrictive)
    {
        List	   *hook_policies =
            (*row_security_policy_hook_restrictive) (cmd, relation);

        /*
         * As with built-in restrictive policies, we sort any hook-provided
         * restrictive policies by name also.  Note that we also intentionally
         * always check all built-in restrictive policies, in name order,
         * before checking restrictive policies added by hooks, in name order.
         */
        sort_policies_by_name(hook_policies);

        foreach(item, hook_policies)
        {
            RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

            if (check_role_for_policy(policy->roles, user_id))
                *restrictive_policies = lappend(*restrictive_policies, policy);
        }
    }

    if (row_security_policy_hook_permissive)
    {
        List	   *hook_policies =
            (*row_security_policy_hook_permissive) (cmd, relation);

        foreach(item, hook_policies)
        {
            RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

            if (check_role_for_policy(policy->roles, user_id))
                *permissive_policies = lappend(*permissive_policies, policy);
        }
    }
}

/*
 * Copied from src/backend/executor/row_security.c
 *
 * sort_policies_by_name
 *
 * This is only used for restrictive policies, ensuring that any
 * WithCheckOptions they generate are applied in a well-defined order.
 * This is not necessary for permissive policies, since they are all combined
 * together using OR into a single WithCheckOption check.
 */
static void
sort_policies_by_name(List *policies)
{
    list_sort(policies, row_security_policy_cmp);
}

/*
 * Copied from src/backend/executor/row_security.c
 *
 * list_sort comparator to sort RowSecurityPolicy entries by name
 */
static int
row_security_policy_cmp(const ListCell *a, const ListCell *b)
{
    const RowSecurityPolicy *pa = (const RowSecurityPolicy *) lfirst(a);
    const RowSecurityPolicy *pb = (const RowSecurityPolicy *) lfirst(b);

    /* Guard against NULL policy names from extensions */
    if (pa->policy_name == NULL)
        return pb->policy_name == NULL ? 0 : 1;
    if (pb->policy_name == NULL)
        return -1;

    return strcmp(pa->policy_name, pb->policy_name);
}

/*
 * Copied from src/backend/executor/row_security.c
 *
 * check_role_for_policy -
 *	 determines if the policy should be applied for the current role
 */
static bool
check_role_for_policy(ArrayType *policy_roles, Oid user_id)
{
    int			i;
    Oid		   *roles = (Oid *) ARR_DATA_PTR(policy_roles);

    /* Quick fall-thru for policies applied to all roles */
    if (roles[0] == ACL_ID_PUBLIC)
        return true;

    for (i = 0; i < ARR_DIMS(policy_roles)[0]; i++)
    {
        if (has_privs_of_role(user_id, roles[i]))
            return true;
    }

    return false;
}
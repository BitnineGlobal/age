
/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

LOAD 'age';
SET search_path TO ag_catalog;

SET age.enable_auto_column_conversion = true;
SELECT create_graph('auto_column_conversion');

SELECT * FROM cypher('auto_column_conversion', $$RETURN true, 'AGE', 2022$$) AS (ignore bool);
SELECT * FROM cypher('auto_column_conversion', $$
    CREATE (b:begin)-[:edge {name: 'main edge', number: 1, dangerous: {type: "all", level: "all"}}]->(u1:middle)-[:edge {name: 'main edge', number: 2, dangerous: {type: "all", level: "all"}, packages: [2,4,6]}]->(u2:middle)-[:edge {name: 'main edge', number: 3, dangerous: {type: "all", level: "all"}}]->(u3:middle)-[:edge {name: 'main edge', number: 4, dangerous: {type: "all", level: "all"}}]->(e:end), (u1)-[:self_loop {name: 'self loop', number: 1, dangerous: {type: "all", level: "all"}}]->(u1), (e)-[:self_loop {name: 'self loop', number: 2, dangerous: {type: "all", level: "all"}}]->(e), (b)-[:alternate_edge {name: 'alternate edge', number: 1, packages: [2,4,6], dangerous: {type: "poisons", level: "all"}}]->(u1), (u2)-[:alternate_edge {name: 'alternate edge', number: 2, packages: [2,4,6], dangerous: {type: "poisons", level: "all"}}]->(u3), (u3)-[:alternate_edge {name: 'alternate edge', number: 3, packages: [2,4,6], dangerous: {type: "poisons", level: "all"}}]->(e), (u2)-[:bypass_edge {name: 'bypass edge', number: 1, packages: [1,3,5,7]}]->(e), (e)-[:alternate_edge {name: 'backup edge', number: 1, packages: [1,3,5,7]}]->(u3), (u3)-[:alternate_edge {name: 'backup edge', number: 2, packages: [1,3,5,7]}]->(u2), (u2)-[:bypass_edge {name: 'bypass edge', number: 2, packages: [1,3,5,7], dangerous: {type: "poisons", level: "all"}}]->(b) RETURN 2022, b, e
$$) AS (ignore agtype);

SELECT * FROM cypher('auto_column_conversion', $$
    WITH true AS b
    RETURN 'AGE', b, 'AGE2'
$$) AS (ignore int);

SELECT * FROM cypher('auto_column_conversion', $$
    MATCH (m), (n)
    WITH n, m, 1 + 1 as l
    RETURN 'AGE', l, label(n) as n, label(m), 'AGE2'
    LIMIT 5
$$) AS (ignore bool);

SELECT * FROM round(10.4), cypher('auto_column_conversion', $$
    MATCH (m), (n)
    WITH n, m, 1 + 1 as l
    RETURN 'AGE', l, label(n) as n, label(m), 'AGE2'
    LIMIT 5
$$) AS (ignore bool);

SELECT * FROM (
    SELECT *
    FROM cypher('auto_column_conversion', $$
        WITH true AS b
        RETURN 'AGE', b, 'AGE2'
    $$) AS (ignore int)
) AS cypher_subquery;

SELECT drop_graph('auto_column_conversion', true);
SET age.enable_auto_column_conversion = false;
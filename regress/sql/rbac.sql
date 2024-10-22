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

CREATE ROLE role1;

SELECT create_graph('movies');

SELECT create_vlabel('movies', 'Actor');
SELECT create_vlabel('movies', 'Movie');

SELECT create_elabel('movies', 'ACTED_IN');

-- Create relationships
SELECT * FROM cypher('movies', $$CREATE (a:Actor {name: "Tom Hanks"})-[:ACTED_IN]->(m:Movie {title: "You've Got Mail"})$$) AS (a agtype);
SELECT * FROM cypher('movies', $$CREATE (a:Actor {name: "Meg Ryan"})-[:ACTED_IN]->(m:Movie {title: "Transformers"})$$) AS (a agtype);

--
-- Test RBAC
--

-- To allow role to use age, USAGE on ag_catalog is required
GRANT USAGE ON SCHEMA ag_catalog TO role1;

-- To allow role to access the movies graph, USAGE on movies is required
GRANT USAGE ON SCHEMA movies TO role1;

--
-- MATCH
--

-- Allow role1 to use MATCH on Actor label
GRANT SELECT ON movies."Actor" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (a:Actor) RETURN a$$) AS (a agtype);
-- Should fail as role1 does not have SELECT on movies."Movie"
SELECT * FROM cypher('movies', $$MATCH (m:Movie) RETURN m$$) AS (m agtype);

RESET ROLE;

-- Allow role1 to use MATCH on Movie label
GRANT SELECT ON movies."Movie" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (m:Movie) RETURN m$$) AS (m agtype);
-- Should fail as role1 does not have SELECT on movies."ACTED_IN"
SELECT * FROM cypher('movies', $$MATCH (m:Movie)-[:ACTED_IN]->(a:Actor) RETURN m, a$$) AS (m agtype, a agtype);

RESET ROLE;

-- Allow role1 to use MATCH on ACTED_IN label
GRANT SELECT ON movies."ACTED_IN" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH p=(a:Actor)-[:ACTED_IN]->(m:Movie) RETURN p$$) AS (m agtype);

RESET ROLE;

--
-- UPDATE
--

-- Allow role1 to use UPDATE(SET and REMOVE) on Actor label
GRANT UPDATE ON movies."Actor" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Hanks"}) SET a.name = "Tom Cruise", a.age=50 RETURN a$$) AS (a agtype);
SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"}) REMOVE a.age RETURN a$$) AS (a agtype);
-- Should fail as role1 does not have UPDATE on movies."Movie"
SELECT * FROM cypher('movies', $$MATCH (m:Movie {title: "You've Got Mail"}) SET m.title = "You've Got Mail 2" RETURN m$$) AS (m agtype);

RESET ROLE;

-- Allow role1 to use UPDATE(SET and REMOVE) on Movie label
GRANT UPDATE ON movies."Movie" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (m:Movie {title: "You've Got Mail"}) SET m.title = "You've Got Mail 2", m.rating=8 RETURN m$$) AS (m agtype);
SELECT * FROM cypher('movies', $$MATCH (m:Movie {title: "You've Got Mail 2"}) REMOVE m.rating RETURN m$$) AS (m agtype);

-- Should fail as role1 does not have UPDATE on movies."ACTED_IN"
SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"})-[r:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"}) SET r.role = "Lead Actor" RETURN r$$) AS (r agtype);

RESET ROLE;

-- Allow role1 to use UPDATE(SET and REMOVE) on ACTED_IN label
GRANT UPDATE ON movies."ACTED_IN" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"})-[r:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"}) SET r.role = "Lead Actor" RETURN r$$) AS (r agtype);
SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"})-[r:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"}) REMOVE r.role RETURN r$$) AS (r agtype);

RESET ROLE;

--
-- DELETE
--

-- Allow role1 to use DELETE on ACTED_IN label
GRANT DELETE ON movies."ACTED_IN" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"})-[r:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"}) DELETE r RETURN r$$) AS (r agtype);
-- Should fail as role1 does not have DELETE on movies."Movie"
SELECT * FROM cypher('movies', $$MATCH (m:Movie {title: "You've Got Mail 2"}) DELETE m RETURN m$$) AS (m agtype);

RESET ROLE;

-- Allow role1 to use DELETE on Movie label
GRANT DELETE ON movies."Movie" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (m:Movie {title: "You've Got Mail 2"}) DELETE m RETURN m$$) AS (m agtype);

RESET ROLE;

--
-- CREATE
--
SELECT * FROM cypher('movies', $$MATCH (a:Actor) return a$$) AS (a agtype);
-- Allow role1 to use CREATE on movies."Movie"
GRANT INSERT ON movies."Movie" TO role1;
GRANT USAGE ON movies."Movie_id_seq" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$CREATE (m:Movie {title: "You've Got Mail 2"})$$) AS (m agtype);
-- Should fail as role1 does not have CREATE on movies."Actor"
SELECT * FROM cypher('movies', $$CREATE (a:Actor {name: "New Actor"})$$) AS (a agtype);
SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"}) CREATE (a)-[:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"})$$) AS (m agtype);

RESET ROLE;

-- Allow role1 to use CREATE on movies."ACTED_IN" and movies."Actor"
GRANT INSERT ON movies."ACTED_IN" TO role1;
GRANT USAGE ON movies."ACTED_IN_id_seq" TO role1;
GRANT INSERT ON movies."Actor" TO role1;
GRANT USAGE ON movies."Actor_id_seq" TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT * FROM cypher('movies', $$MATCH (a:Actor {name: "Tom Cruise"}) CREATE (a)-[:ACTED_IN]->(m:Movie {title: "You've Got Mail 2"})$$) AS (m agtype);

RESET ROLE;

--
-- create_vlabel and create_elabel
--

-- Since all labels are child tables of movies."_ag_label_vertex" and movies."_ag_label_edge"
-- Role needs to be owner of _ag_label_vertex and _ag_label_edge to create new labels
GRANT CREATE ON SCHEMA movies TO role1;
GRANT USAGE ON movies."_label_id_seq" TO role1;
ALTER TABLE movies."_ag_label_vertex" OWNER TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT create_vlabel('movies', 'Director');
-- Should fail as role1 is not owner of movies."_ag_label_edge"
SELECT create_elabel('movies', 'DIRECTED');

RESET ROLE;

ALTER TABLE movies."_ag_label_edge" OWNER TO role1;

SET role role1;
SET search_path TO ag_catalog;

SELECT create_elabel('movies', 'DIRECTED');

RESET ROLE;

--
-- cleanup
--
SELECT drop_graph('movies', true);
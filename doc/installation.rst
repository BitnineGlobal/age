.. Licensed to the Apache Software Foundation (ASF) under one
   or more contributor license agreements.  See the NOTICE file
   distributed with this work for additional information
   regarding copyright ownership.  The ASF licenses this file
   to you under the Apache License, Version 2.0 (the
   "License"); you may not use this file except in compliance
   with the License.  You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing,
   software distributed under the License is distributed on an
   "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
   KIND, either express or implied.  See the License for the
   specific language governing permissions and limitations
   under the License.

Installation
============

Installation from Source Code
-----------------------------

Requirements
~~~~~~~~~~~~

Since |project| is an extension of PostgreSQL, its build system is based on `Extension Building Infrastructure`_ that PostgreSQL provides. Therefore, ``pg_config`` (typically the first one in your ``PATH`` environment variable) for the PostgreSQL installation is used to build it.

  |project| |release| supports PostgreSQL 11.

.. _Extension Building Infrastructure: https://www.postgresql.org/docs/11/extend-pgxs.html

Getting The Source
~~~~~~~~~~~~~~~~~~

The |project| |release| sources can be obtained from its GitHub repository: `bitnine-oss/AgensGraph-Extension/releases`_.

.. _bitnine-oss/AgensGraph-Extension/releases: https://github.com/bitnine-oss/AgensGraph-Extension/releases

Installation Procedure
~~~~~~~~~~~~~~~~~~~~~~

To build and install |project|, run the following command in the source code directory of |project|.

.. code-block:: sh

  $ make install

..

  Since |project| will be installed in the directory of the PostgreSQL installation, proper permissions on the directory are required.

Run the following statements in ``psql`` to create and load |project| in PostgreSQL.

.. code-block:: psql

  =# CREATE EXTENSION age; -- run this statement only once
  CREATE EXTENSION
  =# LOAD 'age';
  LOAD
  =# SET search_path = ag_catalog, "$user", public;
  SET

..

  When |project| is being loaded, it installs ``post_parse_analyze_hook``, ``set_rel_pathlist_hook``, and ``object_access_hook`` to analyze and execute Cypher queries.

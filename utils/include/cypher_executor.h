//
// Created by Shoaib on 10/3/2021.
//

#ifndef CYPHER_EXECUTOR_H
#define CYPHER_EXECUTOR_H

#endif //CYPHER_EXECUTOR_H

#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include "postgresql/libpq-fe.h"

void init_cypher(PGconn *conn);
void start_transaction(PGconn *conn);
void commit_transaction(PGconn *conn);
void rollback_transaction(PGconn *conn);
void execute_cypher(PGconn *conn, char* cypher_str,
                    char* graph_name, size_t cypher_size);

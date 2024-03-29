/**
 * @file
 * @brief Debugging tools to print out the state of a graph, nodes and edges.
 */

/*************************************************************************
 * Copyright (c) 2011 AT&T Intellectual Property 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors: Details at https://graphviz.org
 *************************************************************************/

#include <common/render.h>

#define SUB_TREE_MAGIC 32123
#define HAS_SUB_TREE(n) (ND_subtree(n) && (ND_subtree(n))->magic == SUB_TREE_MAGIC)

#define LENGTH(e)	(ND_rank(aghead(e)) - ND_rank(agtail(e)))
#define SLACK(e)	(LENGTH(e) - ED_minlen(e))
#define ND_subtree(n)	(subtree_t*)ND_par(n)
#define TREE_EDGE(e)	(ED_tree_index(e) >= 0)

void edge_to_stderr(edge_t *e) {
    node_t *head, *tail;
       
    if (e) {
	head = aghead(e);
	tail = agtail(e);
	char head_ptr[255];  head ? sprintf(head_ptr, "%p", head) : sprintf(head_ptr, "NULL");
	char tail_ptr[255]; tail != NULL ? sprintf(tail_ptr, "%p", tail) : sprintf(tail_ptr, "NULL");
	char *head_name = ND_label(head) ? ND_label(head)->text : head_ptr;
	char *tail_name = ND_label(tail) ? ND_label(tail)->text : tail_ptr;
	int type = ED_edge_type(e);
	char *in_tree = TREE_EDGE(e) ? "" : "NOT IN TREE";

	fprintf(stderr, "%s -> %s: (%p) cut_value: %i slack: %i weight: %i min_len: %i %s\n", tail_name, head_name, e, ED_cutvalue(e), SLACK(e), ED_weight(e), ED_minlen(e), in_tree);
    } else {
	fprintf(stderr, "NULL EDGE!!!\n");
    }
}

void node_to_stderr(node_t *n) {
    char *name = ND_label(n) ? ND_label(n)->text : "-";
    int in = ND_in(n).size;
    int out = ND_out(n).size;
    edge_t* par_n = ND_par(n);

    char par_str[255];
    if (par_n == NULL) {
	sprintf(par_str, "NULL");
    } else {
	sprintf(par_str, "SUBTREE");
    }
/*
    } else if (!HAS_SUB_TREE(n)) {
	node_t *head, *tail;
	head = aghead(par_n);
	tail = agtail(par_n);

	if (head == n) {
	    char tail_ptr[255]; tail != NULL ? sprintf(tail_ptr, "%p", tail) : sprintf(tail_ptr, "NULL");
	    sprintf(par_str, "%s", ND_label(tail) ? ND_label(tail)->text : tail_ptr);
	} else if (tail == n) {
	    char head_ptr[255]; head != NULL ? sprintf(head_ptr, "%p", head) : sprintf(head_ptr, "NULL");
	    sprintf(par_str, "%s", ND_label(head) ? ND_label(head)->text : head_ptr);
	} else {
	    sprintf(par_str, "UNKNOWN(%p)", par_n);
	}
*/

    // AGID(n) does not seem useful as an identifier it changes each run
    fprintf(stderr, "%s (%p): type=%i rank=%i in=%i out=%i coords:(%f, %f) TreeParent:%s min:%i max:%i ",
	name, n, ND_node_type(n), ND_rank(n), in, out, ND_coord(n).x, ND_coord(n).y, par_str, ND_low(n), ND_lim(n));
    fprintf(stderr, "%s (%p): type=%i rank=%i in=%i out=%i coords:(%f, %f) TreeParent:%s min:%i max:%i ",
	name, *n, ND_node_type(n), ND_rank(n), in, out, ND_coord(n).x, ND_coord(n).y, par_str, ND_low(n), ND_lim(n));

/*    if (HAS_SUB_TREE(n)) {
	subtree_t *st = ND_subtree(n);
	char *cur_name = st->rep && ND_label(st->rep) ? ND_label(st->rep)->text : "-";
	void *par_name = st->par && st->par->rep && ND_label(st->par->rep) ? ND_label(st->par->rep)->text : "-";

	fprintf(stderr, "sub_tree: node:%s size:%i parent:%s heap:%i\n", cur_name, st->size, par_name, st->heap_index);
    } else { */
	fprintf(stderr, "NO SUB_TREE\n");
    // }
}

void nodes_to_stderr(char *title, graph_t *g) {
    int i = 0;
    node_t *n;
    fprintf(stderr, "-%s-NODES----------------\n", title);
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	fprintf(stderr, "%i: ", i);
	node_to_stderr(n);
	if (true) {
	    edge_t *e;
	    for (int j = 0; (e = ND_in(n).list[j]); j++) {
		fprintf(stderr, "     in: ");
		edge_to_stderr(e);
    	    }
	    for (int j = 0; (e = ND_out(n).list[j]); j++) {
		fprintf(stderr, "    out: ");
		edge_to_stderr(e);
	    }
	}
	i++;
    }
    fprintf(stderr, "----------------------\n");
}

void print_stack_trace(void) {
    #include <execinfo.h>
    #include <stdio.h>

    fprintf(stderr, "-----------------\n");
    void* callstack[128];
    int i, frames = backtrace(callstack, 128);
    char** strs = backtrace_symbols(callstack, frames);
    for (i = 0; i < frames; ++i) {
	fprintf(stderr, "%s\n", strs[i]);
    }
    free(strs);
    fprintf(stderr, "-----------------\n");
}

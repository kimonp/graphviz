/*************************************************************************
 * Copyright (c) 2011 AT&T Intellectual Property 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors: Details at http://www.graphviz.org/
 *************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include <getopt.h>
#include <cgraph/alloc.h>
#include <cgraph/cgraph.h>
#include <cgraph/exit.h>
#include <ingraphs/ingraphs.h>
#include "generic_list.h"

/* structure to hold an attribute specified on the commandline */
typedef struct {
    char *n;
    char *v;
} strattr_t;

static int remove_child(Agraph_t * graph, Agnode_t * node);
static void help_message(const char *progname);

static void addattr(generic_list_t * l, char *a);
static void addnode(generic_list_t * l, char *n);

int verbose = 0;		/* Flag to indicate verbose message output */

/* wrapper to match libcgraph conventions with libingraph */
static Agraph_t *gread(FILE *fp);

#define NDNAME "mk"

typedef struct {
    Agrec_t h;
    int mark;
} ndata;

 /* The following macros for marking nodes rely on the ndata record
  * being locked at the front of a node's list of records.
  */
#define NDATA(n)    ((ndata*)(AGDATA(n)))
#define MARKED(n)  (((NDATA(n))->mark)&1)
#define MARK(n)  (((NDATA(n))->mark) = 1)
#define UNMARK(n)  (((NDATA(n))->mark) = 0)

int main(int argc, char **argv)
{
    int c;
    char *progname;

    ingraph_state ig;

    Agraph_t *graph;
    Agnode_t *node;
    Agedge_t *edge;
    Agedge_t *nexte;
    Agsym_t *attr;

    char **files;

    unsigned long i, j;

    opterr = 0;

    progname = strrchr(argv[0], '/');
    if (progname == NULL) {
	progname = argv[0];
    } else {
	progname++;		/* character after last '/' */
    }

    generic_list_t attr_list = new_generic_list(16);
    generic_list_t node_list = new_generic_list(16);

    while ((c = getopt(argc, argv, "hvn:N:")) != -1) {
	switch (c) {
	case 'N':
		addattr(&attr_list, optarg);
		break;
	case 'n':
		addnode(&node_list, optarg);
		break;
	case 'h':
		help_message(progname);
		graphviz_exit(EXIT_SUCCESS);
		break;
	case 'v':
		verbose = 1;
		break;
	case '?':
	    if (optopt == '?') {
		help_message(progname);
		graphviz_exit(EXIT_SUCCESS);
	    } else if (isprint(optopt)) {
		fprintf(stderr, "Unknown option `-%c'.\n", optopt);
	    } else {
		fprintf(stderr, "Unknown option character `\\x%X'.\n",
			optopt);
	    }
	    graphviz_exit(EXIT_FAILURE);
	    break;

	default:
	    help_message(progname);
	    graphviz_exit(EXIT_FAILURE);
	    break;
	}
    }

    /* Any arguments left? */
    if (optind < argc) {
	files = &argv[optind];
    } else {
	files = NULL;
    }

    newIngraph(&ig, files, gread);
    while ((graph = nextGraph(&ig)) != NULL) {
	if (agisdirected(graph) == 0) {
	    fprintf(stderr,
		    "*** Error: Graph is undirected! Pruning works only with directed graphs!\n");
	    graphviz_exit(EXIT_FAILURE);
	}

	/* attach node data for marking to all nodes */
	aginit(graph, AGNODE, NDNAME, sizeof(ndata), 1);

	/* prune all nodes specified on the commandline */
	for (i = 0; i < node_list.used; i++) {
	    if (verbose == 1)
		fprintf(stderr, "Pruning node %s\n", (char*)node_list.data[i]);

	    /* check whether a node of that name exists at all */
	    node = agnode(graph, (char*)node_list.data[i], 0);
	    if (node == NULL) {
		fprintf(stderr,
			"*** Warning: No such node: %s -- gracefully skipping this one\n",
			(char*)node_list.data[i]);
	    } else {
		MARK(node);	/* Avoid cycles */
		/* Iterate over all outgoing edges */
		for (edge = agfstout(graph, node); edge; edge = nexte) {
		    nexte = agnxtout(graph, edge);
		    if (aghead(edge) != node) {	/* non-loop edges */
			if (verbose == 1)
			    fprintf(stderr, "Processing descendant: %s\n",
				    agnameof(aghead(edge)));
			if (!remove_child(graph, aghead(edge)))
			    agdelete(graph, edge);
		    }
		}
		UNMARK(node);	/* Unmark so that it can be removed in later passes */

		/* Change attribute (e.g. border style) to show that node has been pruneed */
		for (j = 0; j < attr_list.used; j++) {
		    /* create attribute if it doesn't exist and set it */
		    attr =
			agattr(graph, AGNODE, ((strattr_t*)attr_list.data[j])->n, "");
		    if (attr == NULL) {
			fprintf(stderr, "Couldn't create attribute: %s\n",
				((strattr_t*)attr_list.data[j])->n);
			graphviz_exit(EXIT_FAILURE);
		    }
		    agxset(node, attr, ((strattr_t*)attr_list.data[j])->v);
		}
	    }
	}
	agwrite(graph, stdout);
	agclose(graph);
    }
    free_generic_list(&attr_list);
    free_generic_list(&node_list);
    graphviz_exit(EXIT_SUCCESS);
}

static int remove_child(Agraph_t *graph, Agnode_t *node) {
    Agedge_t *edge;
    Agedge_t *nexte;

    /* Avoid cycles */
    if MARKED
	(node) return 0;
    MARK(node);

    /* Skip nodes with more than one parent */
    edge = agfstin(graph, node);
    if (edge && (agnxtin(graph, edge) != NULL)) {
	UNMARK(node);
	return 0;
    }

    /* recursively remove children */
    for (edge = agfstout(graph, node); edge; edge = nexte) {
	nexte = agnxtout(graph, edge);
	if (aghead(edge) != node) {
	    if (verbose)
		fprintf(stderr, "Processing descendant: %s\n",
			agnameof(aghead(edge)));
	    if (!remove_child(graph, aghead(edge)))
		agdeledge(graph, edge);
	}
    }

    agdelnode(graph, node);
    return 1;
}

static void help_message(const char *progname) {
    fprintf(stderr, "\
Usage: %s [options] [<files>]\n\
\n\
Options:\n\
  -h :           Print this message\n\
  -? :           Print this message\n\
  -v :           Verbose\n\
  -n<node> :     Name node to prune.\n\
  -N<attrspec> : Attribute specification to apply to pruned nodes\n\
\n\
Both options `-n' and `-N' can be used multiple times on the command line.\n", progname);
}

/* wrapper to match libcgraph conventions with libingraph */
static Agraph_t *gread(FILE *fp) {
    return agread(fp, NULL);
}

/* add element to attribute list */
static void addattr(generic_list_t * l, char *a) {
    char *p;

    strattr_t *sp = gv_alloc(sizeof(strattr_t));

    /* Split argument spec. at first '=' */
    p = strchr(a, '=');
    if (p == NULL) {
	fprintf(stderr, "Invalid argument specification: %s\n", a);
	graphviz_exit(EXIT_FAILURE);
    }
    *(p++) = '\0';

    /* pointer to argument name */
    sp->n = gv_strdup(a);

    /* pointer to argument value */
    sp->v = gv_strdup(p);

    add_to_generic_list(l, (gl_data) sp);
}

/* add element to node list */
static void addnode(generic_list_t *l, char *n) {
    char *sp = gv_strdup(n);

    add_to_generic_list(l, (gl_data) sp);
}

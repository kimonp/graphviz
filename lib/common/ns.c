/**
 * @file
 * @brief Network Simplex algorithm for ranking nodes of a DAG, @ref rank, @ref rank2
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

#include <assert.h>
#include <cgraph/alloc.h>
#include <cgraph/exit.h>
#include <cgraph/overflow.h>
#include <cgraph/prisize_t.h>
#include <cgraph/queue.h>
#include <cgraph/streq.h>
#include <common/render.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>

static void dfs_cutval(node_t * v, edge_t * par);
static int dfs_range_init(node_t * v, edge_t * par, int low);
static int dfs_range(node_t * v, edge_t * par, int low);
static int x_val(edge_t * e, node_t * v, int dir);
#ifdef DEBUG
static void check_cycles(graph_t * g);
#endif

#define LENGTH(e)		(ND_rank(aghead(e)) - ND_rank(agtail(e)))
#define SLACK(e)		(LENGTH(e) - ED_minlen(e))
#define SEQ(a,b,c)		((a) <= (b) && (b) <= (c))
#define TREE_EDGE(e)	(ED_tree_index(e) >= 0)

static graph_t *G;
static size_t N_nodes, N_edges;
static size_t S_i;			/* search index for enter_edge */
static int Search_size;
#define SEARCHSIZE 30
static nlist_t Tree_node;
static elist Tree_edge;

// Add and edge to a tight subtree of the graph.
// 
// However, the edge does not retain which subtree it is a member of.
// That can be looked up by either the head or tail node, which must be
// part of the same subtree.
//
// Note that not all edges in the graph will necessarily be edges a subtree:
// they must be "tight" edges (rank increases by 1)
//
// KAP: Set the following variables for both the head and tail nodes of edge (if they have not yet been added)
// * ND_mark(n) (just so you don't add nodes more than once)
// * Add head and tail to: Trkee_node.list
// * For the head node:
//   * add e to ND_tree_out(n)
// * For the tail node:
//   * add e to ND_tree_in(n)
//   
// Note that tree_in and tree_out are only for edges in the tree, not edges that are not in the tree.
static int add_tree_edge(edge_t * e)
{
    node_t *n;
    //fprintf(stderr,"add tree edge %p %s ", (void*)e, agnameof(agtail(e))) ; fprintf(stderr,"%s\n", agnameof(aghead(e))) ;
    if (TREE_EDGE(e)) {
	agerr(AGERR, "add_tree_edge: missing tree edge\n");
	return -1;
    }
    assert(Tree_edge.size <= INT_MAX);
    ED_tree_index(e) = (int)Tree_edge.size;
    Tree_edge.list[Tree_edge.size++] = e;
    if (!ND_mark(agtail(e)))
	Tree_node.list[Tree_node.size++] = agtail(e);
    if (!ND_mark(aghead(e)))
	Tree_node.list[Tree_node.size++] = aghead(e);
    n = agtail(e);
    ND_mark(n) = true;
    ND_tree_out(n).list[ND_tree_out(n).size++] = e;
    ND_tree_out(n).list[ND_tree_out(n).size] = NULL;
    if (ND_out(n).list[ND_tree_out(n).size - 1] == 0) {
	agerr(AGERR, "add_tree_edge: empty outedge list\n");
	return -1;
    }
    n = aghead(e);
    ND_mark(n) = true;
    ND_tree_in(n).list[ND_tree_in(n).size++] = e;
    ND_tree_in(n).list[ND_tree_in(n).size] = NULL;
    if (ND_in(n).list[ND_tree_in(n).size - 1] == 0) {
	agerr(AGERR, "add_tree_edge: empty inedge list\n");
	return -1;
    }
    return 0;
}

/**
 * Invalidate DFS attributes by walking up the tree from to_node till lca
 * (inclusively). Called when updating tree to improve pruning in dfs_range().
 * Assigns ND_low(n) = -1 for the affected nodes.
 */
static void invalidate_path(node_t *lca, node_t *to_node) {
    while (true) {
        if (ND_low(to_node) == -1)
          break;

        ND_low(to_node) = -1;

        edge_t *e = ND_par(to_node);
        if (e == NULL)
          break;

        if (ND_lim(to_node) >= ND_lim(lca)) {
          if (to_node != lca)
            agerr(AGERR, "invalidate_path: skipped over LCA\n");
          break;
        }

        if (ND_lim(agtail(e)) > ND_lim(aghead(e)))
          to_node = agtail(e);
        else
          to_node = aghead(e);
    }
}

// Replace edge e with edge f in the tree and remove edge f from the tree.
// 
// * The Tree_edge list is a list of all edges currently in the tree.
// * Each edge in the tree has a field to store their index into Tree_edge.
//   * Tree_edge[e] is replaced with f
// * Each node keeps a list of which edges it holds which are in the tree.
//   * For the head and tail of e, remove e from that node's list of tree edges
//   * For the head and tail of f, add e to that node's list of tree edges
static void exchange_tree_edges(edge_t * e, edge_t * f)
{
    node_t *n;

    ED_tree_index(f) = ED_tree_index(e);
    Tree_edge.list[ED_tree_index(e)] = f;
    ED_tree_index(e) = -1;

    n = agtail(e);
    size_t i = --ND_tree_out(n).size;
    size_t j;
    for (j = 0; j <= i; j++)
	if (ND_tree_out(n).list[j] == e)
	    break;
    ND_tree_out(n).list[j] = ND_tree_out(n).list[i];
    ND_tree_out(n).list[i] = NULL;
    n = aghead(e);
    i = --ND_tree_in(n).size;
    for (j = 0; j <= i; j++)
	if (ND_tree_in(n).list[j] == e)
	    break;
    ND_tree_in(n).list[j] = ND_tree_in(n).list[i];
    ND_tree_in(n).list[i] = NULL;

    n = agtail(f);
    ND_tree_out(n).list[ND_tree_out(n).size++] = f;
    ND_tree_out(n).list[ND_tree_out(n).size] = NULL;
    n = aghead(f);
    ND_tree_in(n).list[ND_tree_in(n).size++] = f;
    ND_tree_in(n).list[ND_tree_in(n).size] = NULL;
}

// init_rank() does an inital ranking to start things off.
//
// QUESTION: Where and what are rank values set to before init_rank()?
//           This is important because it uses the current values of ranks
//           to initialize the ranks.  It seems like it expects them to be set to
//           zero or some baseline to begin with, but I have not found where
//           that is done.
//
// This ranking will be subsequently modified by the network simplex ranking mechanism
// * All nodes with no incoming edges are placed in a queue.
// * While we can pull the top node off the queue:
//   * Pull the top node of the queue and make it the current node.
//   * Rank the current node with the maximum rank of the node connected to each incoming edge+1.
//     That is:
//     * for each incoming edge of the current node
//       * rank(n) = max(rank(v), rank(tail(e)) + min_len(e)
//       * Since the first nodes in the queue have no incloming edges, the first nodes
//         in queue are ranked zero.
//   * for each outgoing edge of the current node
//
// KAP: only called by rank2() if there are any edge has slack less than the minimum.
// * Thus, if ranks have not been assigned, init_rank() is called.
static
void init_rank(void)
{
    int i;
    node_t *v;
    edge_t *e;

    queue_t Q = queue_new(N_nodes);
    size_t ctr = 0;

    for (v = GD_nlist(G); v; v = ND_next(v)) {
	if (ND_priority(v) == 0)
	    queue_push(&Q, v);
    }

    while ((v = queue_pop(&Q))) {
	ND_rank(v) = 0;
	ctr++;
	for (i = 0; (e = ND_in(v).list[i]); i++)
	    ND_rank(v) = MAX(ND_rank(v), ND_rank(agtail(e)) + ED_minlen(e));
	for (i = 0; (e = ND_out(v).list[i]); i++) {
	    if (--ND_priority(aghead(e)) <= 0)
		queue_push(&Q, aghead(e));
	}
    }
    if (ctr != N_nodes) {
	agerr(AGERR, "trouble in init_rank\n");
	for (v = GD_nlist(G); v; v = ND_next(v))
	    if (ND_priority(v))
		agerr(AGPREV, "\t%s %d\n", agnameof(v), ND_priority(v));
    }
    queue_free(&Q);
}

// Return an edge in the feasible tree with a negative cut value, otherwise NULL.
// 
// S_i is the index to start the search.  If not found to the end, loop around to
// zero and search up to S_i.  This is to support a finding in the paper that
// network simplex is much more effecient if you choose the next edge cyclically,
// instead of always starting the search from the beginning.
static edge_t *leave_edge(void)
{
    edge_t *f, *rv = NULL;
    int cnt = 0;

    size_t j = S_i;
    while (S_i < Tree_edge.size) {
	if (ED_cutvalue(f = Tree_edge.list[S_i]) < 0) {
	    if (rv) {
		if (ED_cutvalue(rv) > ED_cutvalue(f))
		    rv = f;
	    } else
		rv = Tree_edge.list[S_i];
	    if (++cnt >= Search_size)
		return rv;
	}
	S_i++;
    }
    if (j > 0) {
	S_i = 0;
	while (S_i < j) {
	    if (ED_cutvalue(f = Tree_edge.list[S_i]) < 0) {
		if (rv) {
		    if (ED_cutvalue(rv) > ED_cutvalue(f))
			rv = f;
		} else
		    rv = Tree_edge.list[S_i];
		if (++cnt >= Search_size)
		    return rv;
	    }
	    S_i++;
	}
    }
    return rv;
}

static edge_t *Enter;
static int Low, Lim, Slack;

static void dfs_enter_outedge(node_t * v)
{
    int i, slack;
    edge_t *e;

    for (i = 0; (e = ND_out(v).list[i]); i++) {
	if (!TREE_EDGE(e)) {
	    if (!SEQ(Low, ND_lim(aghead(e)), Lim)) {
		slack = SLACK(e);
		if (slack < Slack || Enter == NULL) {
		    Enter = e;
		    Slack = slack;
		}
	    }
	} else if (ND_lim(aghead(e)) < ND_lim(v))
	    dfs_enter_outedge(aghead(e));
    }
    for (i = 0; (e = ND_tree_in(v).list[i]) && (Slack > 0); i++)
	if (ND_lim(agtail(e)) < ND_lim(v))
	    dfs_enter_outedge(agtail(e));
}

static void dfs_enter_inedge(node_t * v)
{
    int i, slack;
    edge_t *e;

    for (i = 0; (e = ND_in(v).list[i]); i++) {
	if (!TREE_EDGE(e)) {
	    if (!SEQ(Low, ND_lim(agtail(e)), Lim)) {
		slack = SLACK(e);
		if (slack < Slack || Enter == NULL) {
		    Enter = e;
		    Slack = slack;
		}
	    }
	} else if (ND_lim(agtail(e)) < ND_lim(v))
	    dfs_enter_inedge(agtail(e));
    }
    for (i = 0; (e = ND_tree_out(v).list[i]) && Slack > 0; i++)
	if (ND_lim(aghead(e)) < ND_lim(v))
	    dfs_enter_inedge(aghead(e));
}

// Given a tree edge, return the non-tree edge with the lowest remaining cut-value
//
// Documentation from paper:
// * enter_edge ﬁnds a non-tree edge to replace e.
//   * This is done by breaking the edge e, which divides the tree into a head and tail component.
//   * All edges going from the head component to the tail are considered, with an edge of minimum slack being chosen.
//   * This is necessary to maintain feasibility
static edge_t *enter_edge(edge_t * e)
{
    node_t *v;
    bool outsearch;

    /* v is the down node */
    if (ND_lim(agtail(e)) < ND_lim(aghead(e))) {
	v = agtail(e);
	outsearch = false;
    } else {
	v = aghead(e);
	outsearch = true;
    }
    Enter = NULL;
    Slack = INT_MAX;
    Low = ND_low(v);
    Lim = ND_lim(v);
    if (outsearch)
	dfs_enter_outedge(v);
    else
	dfs_enter_inedge(v);
    return Enter;
}

static void init_cutvalues(void)
{
    dfs_range_init(GD_nlist(G), NULL, 1);
    dfs_cutval(GD_nlist(G), NULL);
}

/* functions for initial tight tree construction */
// borrow field from network simplex - overwritten in init_cutvalues() forgive me
#define ND_subtree(n) (subtree_t*)ND_par(n)
#define ND_subtree_set(n,value) (ND_par(n) = (edge_t*)value)

#define SUB_TREE_MAGIC 32123

// An "elt" seems to be the pointer to the subtree_s in held in each heap element.
// * heap_index is used for two purposes:
//   * To tell if a subtree is in the heap or not (-1)
//   * When a tree is merged, to know what its index into the heap is
//     so that the heap can be effeciently re-heapified, since the merged tree
//     probably increased in size.
typedef struct subtree_s {
        int magic;       // always true KAP
        node_t *rep;            /* some node in the tree */
        int    size;            /* total tight tree size */
        int    heap_index;      /* required to find non-min elts when merged */
        struct subtree_s *par;  /* union find */
} subtree_t;

// Finds a tight subtree from node v.
//
// So given a node, finds all nodes connected to that node that increase in rank by one,
// and then does this recursively on all the new nodes.
//
// Starting with a root node, a "tight subtree" is a list of nodes whereby each included
// edge on that node points to a node that has rank = cur_rank+1 (thus some edges will
// not be included if they point to a node of lesser rank or rank > rank + 1).  All nodes
// in the subtree follow this rule recursively.
// 
// It only makes sense to do this search after all nodes have a rank, because a "tight" edge
// is (typically) an edge that goes from a node of rank to a node of rank+1.
// 
// Note that only edges with a slack of zero are considered, meaning that they are "tight"
// edges, which is why this called "tight_subtree_search".  A slack of zero between to 
// edges e1 and e2 implies that:
// * The rank of e1 > e2
// * rank(e1) - rank(e2) = min_rank_diff, where min_rank_diff is typilcally one.
//   * so the rank of rank(e1) == rank(e2) - min_rank_diff
//
// * for each incoming edge of v:
//   * if already a TREE_EDGE in this or another subtree (edge.tree_index < 0), skip it
//   * if the edge has slack zero (length == min_length)
//     * Add the edge, and recursively try the tail node of e
// * for each outgoing edge of v:
//   * same as for the incoming edge, but recursively look at the head node instead of
//     the tail.
// KAP: ND_subtree(n) == uses the ND_par(n) field which is overwritten in init_cutvalues().
//      which will be called shortly after this.
//      Populate: 
//        * Tree_node.list
//        * For each node: ND_out() and ND_in()
//        * Note that these are only set for edges that are in the newly discovered tree,
//          not all edges in the graph
/* find initial tight subtrees */
static int tight_subtree_search(Agnode_t *v, subtree_t *st)
{
    Agedge_t *e;
    int     i;
    int     rv;

    rv = 1;
    
    // Store the subtree of this node in the node itself, so you
    // can later look up the subtree of a node from the node.
    ND_subtree_set(v,st);

    for (i = 0; (e = ND_in(v).list[i]); i++) {
        if (TREE_EDGE(e)) continue;
        // If the subtree for the tail of the edge has not been set
        // and slack(0) == 0, add the edge to the tree.
        // And do a search on the tail node of that edge
        if (ND_subtree(agtail(e)) == 0 && SLACK(e) == 0) {
               if (add_tree_edge(e) != 0) {
                   return -1;
               }
               // Note that we are going to save the SAME subtree
               // pointer in all these nodes as well!  All node members
               // of a subtree point back to the same subtree struct.
               rv += tight_subtree_search(agtail(e),st);
        }
    }
    for (i = 0; (e = ND_out(v).list[i]); i++) {
        if (TREE_EDGE(e)) continue;
        if (ND_subtree(aghead(e)) == 0 && SLACK(e) == 0) {
               if (add_tree_edge(e) != 0) {
                   return -1;
               }
               rv += tight_subtree_search(aghead(e),st);
        }
    }
    // Return the size of the subtree, so that the calling
    // function can add this to the size of its
    return rv;
}

// Allocate memory for a new subtree struct, and then
// find the subtree within the graph for node v and return it.
// 
// Parent is set to itself for now, which means the subtree has
// no parent.
static subtree_t *find_tight_subtree(Agnode_t *v)
{
    subtree_t       *rv;
    rv = gv_alloc(sizeof(subtree_t));
    rv->magic = SUB_TREE_MAGIC;
    rv->rep = v;
    rv->size = tight_subtree_search(v,rv);
    if (rv->size < 0) {
        free(rv);
        return NULL;
    }
    // If your parent points to you, you have no parent...
    rv->par = rv;
    return rv;
}

typedef struct STheap_s {
        subtree_t       **elt;
        int             size;
} STheap_t;

// Given a node, return the root of that node's subtree.
// 
// Has the side effect of compresing the path to the root
// by skipping non-root parents of nodes searched.
static subtree_t *STsetFind(Agnode_t *n0)
{
  subtree_t *s0 = ND_subtree(n0);
  while  (s0->par && s0->par != s0) {
    if (s0->par->par) {s0->par = s0->par->par;}  /* path compression for the code weary */
    s0 = s0->par;
  }
  return s0;
}
 
// Return a subtree that is the "union" of the roots of s0 and s1.
// * In fact, the only thing that is used in the return value is the heap index of
//   the newly merged sub_tree.
// * However, the pointer to the new sub_tree is the same as the root that it replaces,
//   so the pointer to the merged sub_tree is in fact in the heap.
//
// * Find the root of each subtree-- one of these will become the merged tree
//   * At least one of the root trees must still be in the heap
//   * If one is not in the heap, choose the other one
//   * Otherwise, choose the larger one of the two roots.
// * Now that we have selected the root tree, we base the new
//   medrged tree off of that one:
//   * preserve the start_none, parent_node and heap_index
//   * merged size = s0.size + s1.size
//   * set the parents of the old roots to the new one.
static subtree_t *STsetUnion(subtree_t *s0, subtree_t *s1)
{
  subtree_t *r0, *r1, *r;

  // Find the root of each subtree
  for (r0 = s0; r0->par && r0->par != r0; r0 = r0->par);
  for (r1 = s1; r1->par && r1->par != r1; r1 = r1->par);

  // If they are equal, no need to merge
  if (r0 == r1) return r0;  /* safety code but shouldn't happen */

  // At least one of the two trees must have a valid heap_index.
  // This means that at least one subtree still exists in the sub_tree heap
  // that was created as part of feasible_tree() -> merge_trees() -> STsetUnion()
  assert(r0->heap_index > -1 || r1->heap_index > -1);
  
  // We will base the new subtree after:
  // * Whichever is still in the heap (because at least one must be)
  // * Whichever has the greater size
  // * Otherwise, just pick the second one (because both are in the heap and are of equal size)
  if (r1->heap_index == -1) r = r0;
  else if (r0->heap_index == -1) r = r1;
  else if (r1->size < r0->size) r = r0;
  else r = r1;

  // The parent of the old trees new becomes the new subtree
  //
  // Be carefull here, because by definition a sub_tree that points
  // to itself has no parent.  So this effects the unmerged remaining
  // tree (pointing to the merged tree) and sets the merged tree to
  // have no parent.
  r0->par = r1->par = r;
  
  // The size of the new subtree is the combined size of the old ones
  r->size = r0->size + r1->size;

  // The heap index of the new tree is valid (indeed it is the same
  // heap index as one of the valid sub_trees)
  assert(r->heap_index >= 0);
  return r;
}

/* find tightest edge to another tree incident on the given tree */
static Agedge_t *inter_tree_edge_search(Agnode_t *v, Agnode_t *from, Agedge_t *best)
{
    int i;
    Agedge_t *e;
    // Set ts = the root subtree of this node (ts maybe stands for "tree_sub")
    subtree_t *ts = STsetFind(v);
    if (best && SLACK(best) == 0) return best;
    for (i = 0; (e = ND_out(v).list[i]); i++) {
            
      // Tree edges are not candidate edges, but may lead to candidates
      if (TREE_EDGE(e)) {
          if (aghead(e) == from) continue;  // do not search back in tree
          best = inter_tree_edge_search(aghead(e),v,best); // search forward in tree
      }
      else {
        // If the non-tree edge is not part of this subtree...thus it connects
        // thus subtree to another
        if (STsetFind(aghead(e)) != ts) {   // encountered candidate edge
          // If it has the lowest slack we have seen so far, select this edge
          if (best == 0 || SLACK(e) < SLACK(best)) best = e;
        }
        /* else ignore non-tree edge between nodes in the same tree */
      }
    }
    /* the following code must mirror the above, but for in-edges */
    for (i = 0; (e = ND_in(v).list[i]); i++) {
      if (TREE_EDGE(e)) {
          if (agtail(e) == from) continue;
          best = inter_tree_edge_search(agtail(e),v,best);
      }
      else {
        if (STsetFind(agtail(e)) != ts) {
          if (best == 0 || SLACK(e) < SLACK(best)) best = e;
        }
      }
    }
    return best;
}

// Return the tightest non-tree edge that connects to another sub-tree incident to the given tree.
// 
// * The first non-tree edge encountered with a slack of zero is returned.
// * Oherwise, a non-tree edge with the lowest slack of all non-tree edges to the tree
//   is returned.
// * If no non-tree edge is found that connects to other sub_trees, zero is returned.
// 
// * An "edge incident on a tree" refers to an edge that connects a vertex of the tree to a vertex outside the tree.
// * The tighetest possible edge has a slack of zero (generally a rank increase of 1), so any node that increases rank
//   by one will do.  If the slack is not zero, then it is not tight.
static Agedge_t *inter_tree_edge(subtree_t *tree)
{
    Agedge_t *rv;
    rv = inter_tree_edge_search(tree->rep, NULL, NULL);
    return rv;
}

static
int STheapsize(STheap_t *heap) { return heap->size; }

// Re-sorts entry i deaper into the heap after the size of i has increased.
//
// * This heap is a min-heap: gives values from smallest to largest.
// * Takes only log2(n-i) steps to complete.
// * Stops when i has moved into the position where it is now the smallest.
//   * So starts with the item at position i.
//   * Keeps pushing item lower until it is 
static 
void STheapify(STheap_t *heap, int i)
{
    int left, right, smallest;
    subtree_t **elt = heap->elt;
    do {
        left = 2*(i+1)-1;
        right = 2*(i+1);
        if (left < heap->size && elt[left]->size < elt[i]->size) smallest = left;
        else smallest = i;
        if (right < heap->size && elt[right]->size < elt[smallest]->size) smallest = right;
        // Keep going until i is smaller than the left and the right.  If that's true,
        // its in the right place.
        if (smallest != i) {
            subtree_t *temp;
            // Swap i with the smalest entry, and then continue from there
            temp = elt[i];
            elt[i] = elt[smallest];
            elt[smallest] = temp;
            elt[i]->heap_index = i;
            elt[smallest]->heap_index = smallest;
            i = smallest;
        }
        else break;
    } while (i < heap->size);
}

// Allocate memory for a new heap, and then fill it.
static
STheap_t *STbuildheap(subtree_t **elt, int size)
{
    int     i;
    STheap_t *heap = gv_alloc(sizeof(STheap_t));
    heap->elt = elt;
    heap->size = size;

    // Set the index of each subtree to its place in the heap
    for (i = 0; i < heap->size; i++) heap->elt[i]->heap_index = i;
    for (i = heap->size/2; i >= 0; i--)
        STheapify(heap,i);
    return heap;
}

// Extract the smalest sized sub_tre of the heap, and
// * set that sub_tree's heap_index to be -1, so that
//   when it is merged, we know that it is not still in the heap
static
subtree_t *STextractmin(STheap_t *heap)
{
    subtree_t *rv;
    rv = heap->elt[0];
    rv->heap_index = -1;
    heap->elt[0] = heap->elt[heap->size - 1];
    heap->elt[0]->heap_index = 0;
    heap->elt[heap->size -1] = rv;    /* needed to free storage later */
    heap->size--;
    STheapify(heap,0);
    return rv;
}

static
void tree_adjust(Agnode_t *v, Agnode_t *from, int delta)
{
    int i;
    Agedge_t *e;
    Agnode_t *w;
    ND_rank(v) = ND_rank(v) + delta;
    for (i = 0; (e = ND_tree_in(v).list[i]); i++) {
      w = agtail(e);
      if (w != from)
        tree_adjust(w, v, delta);
    }
    for (i = 0; (e = ND_tree_out(v).list[i]); i++) {
      w = aghead(e);
      if (w != from)
        tree_adjust(w, v, delta);
    }
}

// Merge two sub trees on each side of edge e, and add e to the building tree.
//
// * e is not a tree edge
// * the head and the tail are in different subtrees
// * The tree pointed to by e (root of aghead(e)) will
//   need to have the rank of all its nodes adjusted since
//   its now under the other subtree
//   * If for some reason t0 is not in the priority queue (why would that be?)
//     we adjust the rank of t0 instead
static
subtree_t *merge_trees(Agedge_t *e)   /* entering tree edge */
{
  int       delta;
  subtree_t *t0, *t1, *rv;

  assert(!TREE_EDGE(e));

  t0 = STsetFind(agtail(e));
  t1 = STsetFind(aghead(e));

  //fprintf(stderr,"merge trees of %d %d of %d, delta %d\n",t0->size,t1->size,N_nodes,delta);

  if (t0->heap_index == -1) {   // move t0
    delta = SLACK(e);
    if (delta != 0)
      tree_adjust(t0->rep,NULL,delta);
  }
  else {  // move t1
    delta = -SLACK(e);
    if (delta != 0)
      tree_adjust(t1->rep,NULL,delta);
  }
  if (add_tree_edge(e) != 0) {
    return NULL;
  }
  rv = STsetUnion(t0,t1);
  
  return rv;
}

// feasible_tree calculates a initial tight tree for rank2().
// * for all nodes: node.subtree = 0
// * for each node
//   * if node.subtree == 0: find_tight_subtree(node)
// * all subtrees created above are then merged with: merge_tree()
// * sets cut_values for all edges in the feasible tree.
//
/* Construct initial tight tree. Graph must be connected, feasible.
 * Adjust ND_rank(v) as needed.  add_tree_edge() on tight tree edges.
 * trees are basically lists of nodes stored in nodequeues.
 * Return 1 if input graph is not connected; 0 on success.
 */
static
int feasible_tree(void)
{
  Agnode_t *n;
  Agedge_t *ee;
  subtree_t *tree0, *tree1;
  int i, subtree_count = 0;
  STheap_t *heap = NULL;
  int error = 0;

  /* initialization */
  // Set the subtree of each node to be unset (0)
  for (n = GD_nlist(G); n; n = ND_next(n)) {
      ND_subtree_set(n,0);
  }

  // "tree" is a block of memory that contains enough memory to hold a
  // subtree for every node. However, there will likely be fewer subtrees
  // than nodes, since multiple nodes may be in a subtree.
  subtree_t **tree = gv_calloc(N_nodes, sizeof(subtree_t *));
  /* given init_rank, find all tight subtrees */

  nodes_to_stderr("before find_tight_subtree() in feasible_tree()", G);
  // Populate "tree" with all the subtrees we can find in the graph.
  for (n = GD_nlist(G); n; n = ND_next(n)) {
        if (ND_subtree(n) == 0) {
                tree[subtree_count] = find_tight_subtree(n);
                if (tree[subtree_count] == NULL) {
                    error = 2;
                    goto end;
                }
                subtree_count++;
        }
  }

  /* incrementally merge subtrees */
  heap = STbuildheap(tree,subtree_count);
  while (STheapsize(heap) > 1) {
    // Choose the smallest remaining subtree to merge.
    tree0 = STextractmin(heap);

    // Find the tightest edge to another tree
    if (!(ee = inter_tree_edge(tree0))) {
      error = 1;
      break;
    }
    // Merge the subtrees
    tree1 = merge_trees(ee);
    if (tree1 == NULL) {
      error = 2;
      break;
    }
    // Now that that tree has increased in size, fix the heap
    //
    // But Tree1 is thrown away!  The only thing from the merged
    // tree itself is the heap index!
    STheapify(heap,tree1->heap_index);
  }

end:
  free(heap);
  for (i = 0; i < subtree_count; i++) free(tree[i]);
  free(tree);
  if (error) return error;
  assert(Tree_edge.size == N_nodes - 1);
  init_cutvalues();
  return 0;
}

// Set new cutvalues from v to the least commmon ancestor of nodes v and w,
// and return the least common ancestor of v and w.
//
// SEQ(low(v), lim(w), lim(v))
// Where:
//   * ND_low(n) == min_tree_index(n) for nodes in subtree of n
//   * ND_lim(n) == max_tree_index(n) for nodes in subtree of n
//   * SEQ returns true if a <= b <= c, so if a,b,c do not decrease.
// So:
//   * min_tree_index(v) <= max_tree_index(w) <= max_tree_index(v)
//   * So the max tree index of w is inbetween the min and max index of v
//   * This will be no longer be true after you have passed the least 
//     common ancestor of v and w.
/* walk up from v to LCA(v,w), setting new cutvalues. */
static Agnode_t *treeupdate(Agnode_t * v, Agnode_t * w, int cutvalue, int dir)
{
    edge_t *e;
    int d;

    // While v is still a common ancestor of w, continue
    while (!SEQ(ND_low(v), ND_lim(w), ND_lim(v))) {
        // Consider edge e that points to v's parent
	e = ND_par(v);
	if (v == agtail(e))
	    d = dir;
	else
	    d = !dir;
        // If if the parent of e is through the tail,
        // the cutvalue of e is increased.  Otherwise it decreases.
	if (d)
	    ED_cutvalue(e) += cutvalue;
	else
	    ED_cutvalue(e) -= cutvalue;

        // The next v is chosen from the head or tail node of e
        // that has the greater max_tree_index.
	if (ND_lim(agtail(e)) > ND_lim(aghead(e)))
	    v = agtail(e);
	else
	    v = aghead(e);
    }
    return v;
}

// Reduces the rank of the subtree starting at v by delta.
//
// First reduces the rank of node v by delta.
// Further recursively reduces the rank of any edge of v that
// does not point to its parent by delta as well.  Thus the entire
// subtree of v is reduces by delta.
static void rerank(Agnode_t * v, int delta)
{
    int i;
    edge_t *e;

    ND_rank(v) -= delta;
    for (i = 0; (e = ND_tree_out(v).list[i]); i++)
	if (e != ND_par(v))
	    rerank(aghead(e), delta);
    for (i = 0; (e = ND_tree_in(v).list[i]); i++)
	if (e != ND_par(v))
	    rerank(agtail(e), delta);
}

// Add e to the tree while removing f, and update all cut values.
// Note that in doing so, entire subtrees will be reranked.
//
/* e is the tree edge that is leaving and f is the nontree edge that
 * is entering.  compute new cut values, ranks, and exchange e and f.
 */
static int
update(edge_t * e, edge_t * f)
{
    int cutvalue, delta;
    Agnode_t *lca;

    delta = SLACK(f);
    /* "for (v = in nodes in tail side of e) do ND_rank(v) -= delta;" */
    if (delta > 0) {
	size_t s = ND_tree_in(agtail(e)).size + ND_tree_out(agtail(e)).size;
	if (s == 1)
	    rerank(agtail(e), delta);
	else {
	    s = ND_tree_in(aghead(e)).size + ND_tree_out(aghead(e)).size;
	    if (s == 1)
		rerank(aghead(e), -delta);
	    else {
		if (ND_lim(agtail(e)) < ND_lim(aghead(e)))
		    rerank(agtail(e), delta);
		else
		    rerank(aghead(e), -delta);
	    }
	}
    }

    cutvalue = ED_cutvalue(e);
    lca = treeupdate(agtail(f), aghead(f), cutvalue, 1);
    if (treeupdate(aghead(f), agtail(f), cutvalue, 0) != lca) {
	agerr(AGERR, "update: mismatched lca in treeupdates\n");
	return 2;
    }

    // invalidate paths from LCA till affected nodes:
    int lca_low = ND_low(lca);
    invalidate_path(lca, aghead(f));
    invalidate_path(lca, agtail(f));

    ED_cutvalue(f) = -cutvalue;
    ED_cutvalue(e) = 0;
    exchange_tree_edges(e, f);
    dfs_range(lca, ND_par(lca), lca_low);
    return 0;
}

static int scan_and_normalize(void) {
    node_t *n;

    int Minrank = INT_MAX;
    int Maxrank = INT_MIN;
    for (n = GD_nlist(G); n; n = ND_next(n)) {
	if (ND_node_type(n) == NORMAL) {
	    Minrank = MIN(Minrank, ND_rank(n));
	    Maxrank = MAX(Maxrank, ND_rank(n));
	}
    }
    for (n = GD_nlist(G); n; n = ND_next(n))
	ND_rank(n) -= Minrank;
    Maxrank -= Minrank;
    return Maxrank;
}

static void reset_lists(void) {

  free(Tree_node.list);
  Tree_node = (nlist_t){0};

  free(Tree_edge.list);
  Tree_edge = (elist){0};
}

static void
freeTreeList (graph_t* g)
{
    node_t *n;
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	free_list(ND_tree_in(n));
	free_list(ND_tree_out(n));
	ND_mark(n) = false;
    }
    reset_lists();
}

// KAP: LR_balance is the balance method of rank for network simplex
//      when it is used for left-right as opposed up up-down rankings.
//      
// enter_edge(): given an edge, returns a non-tree edge to replace it.
// ND_lim(n): max DFS index for nodes in sub-tree
static void LR_balance(void)
{
    int delta;
    edge_t *e, *f;

    // For each edge in the feasible tree...
    for (size_t i = 0; i < Tree_edge.size; i++) {
	e = Tree_edge.list[i];

        // Interesting here that they are using cut values of zero.
        // During ranking, they are looking for negative cut values. 
        //
        // Of course, during ranking, all negative cut values have been
        // removed, so cut_values of zero are now the lowest hanging fruit.
        // 
        // A cut value of zero means that you have the just as many graph edges
        // crossing from the "head nodes" to the "tail nodes".

	if (ED_cutvalue(e) == 0) {
	    f = enter_edge(e);
	    if (f == NULL)
		continue;
	    delta = SLACK(f);
	    if (delta <= 1)
		continue;
	    if (ND_lim(agtail(e)) < ND_lim(aghead(e)))
		rerank(agtail(e), delta / 2);
	    else
		rerank(aghead(e), -delta / 2);
	}
    }
    freeTreeList (G);
}

static int decreasingrankcmpf(const void *x, const void *y) {
// Suppress Clang/GCC -Wcast-qual warning. Casting away const here is acceptable
// as the later usage is const. We need the cast because the macros use
// non-const pointers for genericity.
#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"
#endif
  node_t **n0 = (node_t**)x;
  node_t **n1 = (node_t**)y;
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
  if (ND_rank(*n1) < ND_rank(*n0)) {
    return -1;
  }
  if (ND_rank(*n1) > ND_rank(*n0)) {
    return 1;
  }
  return 0;
}

static int increasingrankcmpf(const void *x, const void *y) {
// Suppress Clang/GCC -Wcast-qual warning. Casting away const here is acceptable
// as the later usage is const. We need the cast because the macros use
// non-const pointers for genericity.
#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"
#endif
  node_t **n0 = (node_t **)x;
  node_t **n1 = (node_t **)y;
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
  if (ND_rank(*n0) < ND_rank(*n1)) {
    return -1;
  }
  if (ND_rank(*n0) > ND_rank(*n1)) {
    return 1;
  }
  return 0;
}

// Try to improve the top-bottom balance of the number of nodes in ranks.
// * Only look at non-virtual nodes
// * Get a count of how many nodes are in each rank.
// * Sort nodes so that we can step through them by most conjested rank to least conjested.
// * For each node, ranked by rank population (higest to lowest)
//   * consider all the ranks between the highest rank and lowest
//     rank the node is connected to another node.
//   * If any of those ranks has fewer nodes then where it is currently,
//     move it there.
static void TB_balance(void)
{
    node_t *n;
    edge_t *e;
    int low, high, choice;
    int inweight, outweight;
    int adj = 0;
    char *s;

    const int Maxrank = scan_and_normalize();

    /* find nodes that are not tight and move to less populated ranks */
    assert(Maxrank >= 0);
    // Initialize nrank to be an array of integers set to zero from 0-Maxrank
    int *nrank = gv_calloc((size_t)Maxrank + 1, sizeof(int));
    // If TBBalance attribute is set to either min or max,
    // set all normal node ranks to min or max respectively
    // if they have no in our out edges respectively.
    // 
    // Looks like only under special circumstances is adj
    // anything other than zero?
    if ( (s = agget(G,"TBbalance")) ) {
         if (streq(s,"min")) adj = 1;
         else if (streq(s,"max")) adj = 2;
         if (adj) for (n = GD_nlist(G); n; n = ND_next(n))
              if (ND_node_type(n) == NORMAL) {
                if (ND_in(n).size == 0 && adj == 1) {
                   ND_rank(n) = 0;
                }
                if (ND_out(n).size == 0 && adj == 2) {
                   ND_rank(n) = Maxrank;
                }
              }
    }
    
    // Place all nodes in the Tree_node list, and sort them by decreasing
    // or increasing rank, depending on adj
    size_t ii;
    for (ii = 0, n = GD_nlist(G); n; ii++, n = ND_next(n)) {
      Tree_node.list[ii] = n;
    }
    Tree_node.size = ii;
    qsort(Tree_node.list, Tree_node.size, sizeof(Tree_node.list[0]),
          adj > 1 ? decreasingrankcmpf: increasingrankcmpf);
    // Set nrank so it counts the number of (normal, not virtual) nodes at each rank
    for (size_t i = 0; i < Tree_node.size; i++) {
        n = Tree_node.list[i];
        if (ND_node_type(n) == NORMAL)
          nrank[ND_rank(n)]++;
    }
    for (ii = 0; ii < Tree_node.size; ii++) {
      n = Tree_node.list[ii];
      if (ND_node_type(n) != NORMAL)
        continue;
      inweight = outweight = 0;
      low = 0;
      high = Maxrank;
      // Low is set to the max rank of incoming edge's tail node + 1
      for (size_t i = 0; (e = ND_in(n).list[i]); i++) {
        inweight += ED_weight(e);
        low = MAX(low, ND_rank(agtail(e)) + ED_minlen(e));
      }
      // High is set to the min rank of outgoing edge's head node - 1
      for (size_t i = 0; (e = ND_out(n).list[i]); i++) {
        outweight += ED_weight(e);
        high = MIN(high, ND_rank(aghead(e)) - ED_minlen(e));
      }
      if (low < 0)
        low = 0;		/* vnodes can have ranks < 0 */
      
      // If the weight of all incoming edges == outgoing edges
      // Adjust the rank of this node:
      //   Check all the ranks between high and low
      //      If there are fewer nodes on that rank than
      //        whatever rank it currently is in, switch to the rank with fewer
      //
      if (adj) {
        if (inweight == outweight)
            ND_rank(n) = (adj == 1? low : high);
      }
      else {
                if (inweight == outweight) {
                    choice = low;
                    for (int i = low + 1; i <= high; i++)
                        if (nrank[i] < nrank[choice])
                            choice = i;
                    nrank[ND_rank(n)]--;
                    nrank[choice]++;
                    ND_rank(n) = choice;
                }
      }
      free_list(ND_tree_in(n));
      free_list(ND_tree_out(n));
      ND_mark(n) = false;
    }
    free(nrank);
}

// KAP: init_graph() is done just before the network simplex ago (rank2()) is run.
//  * It returns true if there can be a feasible_tree in this graph.
//    * This is only false if any edge of the tree has negative "slack".
//    * negative "slack" means that rank_head(e) - rank_tail(e) < min_edge_length()
//    * Basically the head and tail of an edge are on the same rank, or the
//      tail is on a greater rank than the head.
//      * If ranks have not been set, this will be true because all will be
//        on the same rank.
//    * Set G (global pointer the graph being processed) to the graph passed in (G = g)
//    * N_nodes and N_edges (number of nodes and number of edges)
//    * Tree_node
//
//  * init_graph() initializes key global variables that will be used for network simplex
//    * G is a global pointer to a graph used in the network symplex file (nc.c)
//    * S_i is the "search" index to the last edge "entered" with enter_edge()
//    * N_nodes and N_edges are the count of edges and nodes in the graph.
//    * Tree_node is the list of nodes in the "feasible" tree this is all
//      connected nodes in the graph).  Memory is allocated here, but calculated later in
//      feasible_tree().
//    * Tree_edge is the list of edges in the "feasible" tree (this is only
//      those nodes traveled to find get to all the nodes in the tree).  Memory is
//      allocated here, but calculated later in feasible_tree().
//
//  * init_graph() initializes data within the nodes and edges of g that are used only
//    for network simplex.
//    * ND_priority(n) is set to the number of incoming tree edges to a node.
//      * This us used later in init_rank() by rank2() before entering it's main loop
//        if rank has not yet been set.
//    * ND_tree_in(n) is allocated to hold all tree edges but, not set.
//      * will be set in feasible tree, along with ND_tree_out(n)
//    * ED_cutvalue(n) is central to network simplex and explained in the paper.
//      * All cutvalues initialized to zero here.
//    * ED_tree_index(e) is how far away from the tree root this edge is.
//      * all indexes initialied to -1 here.
static bool init_graph(graph_t *g) {
    node_t *n;
    edge_t *e;

    G = g;
    N_nodes = N_edges = S_i = 0;
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	ND_mark(n) = false;
	N_nodes++;
	for (size_t i = 0; (e = ND_out(n).list[i]); i++)
	    N_edges++;
    }

    Tree_node.list = gv_calloc(N_nodes, sizeof(node_t *));
    Tree_edge.list = gv_calloc(N_nodes, sizeof(edge_t *));

    bool feasible = true;
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	ND_priority(n) = 0;
	size_t i;
	for (i = 0; (e = ND_in(n).list[i]); i++) {
	    ND_priority(n)++;
	    ED_cutvalue(e) = 0;
	    ED_tree_index(e) = -1;
            // Because:
            //   LENGTH(e) = (ND_rank(aghead(e)) - ND_rank(agtail(e)))
            //   SLACK(e)  = (LENGTH(e) - ED_minlen(e))
            // So this could be more clearly written:
            //   if (SLACK(e) < 0) tree is not feasible
	    if (ND_rank(aghead(e)) - ND_rank(agtail(e)) < ED_minlen(e))
		feasible = false;
	}
	ND_tree_in(n).list = gv_calloc(i + 1, sizeof(edge_t *));
	ND_tree_in(n).size = 0;
	for (i = 0; (e = ND_out(n).list[i]); i++);
	ND_tree_out(n).list = gv_calloc(i + 1, sizeof(edge_t *));
	ND_tree_out(n).size = 0;
    }
    return feasible;
}

/* graphSize:
 * Compute no. of nodes and edges in the graph
 */
static void
graphSize (graph_t * g, int* nn, int* ne)
{
    int i, nnodes, nedges;
    node_t *n;
    edge_t *e;
   
    nnodes = nedges = 0;
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	nnodes++;
	for (i = 0; (e = ND_out(n).list[i]); i++) {
	    nedges++;
	}
    }
    *nn = nnodes;
    *ne = nedges;
}

// rank2() ranks nodes using the network simplex algorithm.
//
// rank2() is the bottom level ranking function for dot and coresponds
// pretty closely with the paper "A Technique for Drawing Directed Graphs".
//
// All other ranking functions in dot eventually call this one to
// do the low level work, including:
// * dot_rank()
//  * dot1_rank() -> rank3() -> rank1() -> rank() -> rank2()
//  * dot2_rank() -> rank2()
// * dot_position() -> rank() -> rank2()
//
//
/* rank:
 * Apply network simplex to rank the nodes in a graph.
 * Uses ED_minlen as the internode constraint: if a->b with minlen=ml,
 * rank b - rank a >= ml.
 * Assumes the graph has the following additional structure:
 *   A list of all nodes, starting at GD_nlist, and linked using ND_next.
 *   Out and in edges lists stored in ND_out and ND_in, even if the node
 *  doesn't have any out or in edges.
 * The node rank values are stored in ND_rank.
 * Returns 0 if successful; returns 1 if the graph was not connected;
 * returns 2 if something seriously wrong;
 */
int rank2(graph_t * g, int balance, int maxiter, int search_size)
{
    int iter = 0;
    char *ns = "network simplex: ";
    edge_t *e, *f;

#ifdef DEBUG
    check_cycles(g);
#endif
    if (Verbose) {
	int nn, ne;
	graphSize (g, &nn, &ne);
	fprintf(stderr, "%s %d nodes %d edges maxiter=%d balance=%d\n", ns,
	    nn, ne, maxiter, balance);
	start_timer();
    }
    // init_graph() initializes key global variables that will be used for network simplex
    //              and returns true if the graph
    //  * G is a global pointer to a graph used in the network symplex file (nc.c)
    //  * S_i is the "search" index to the last edge "entered" with enter_edge()
    //  * N_nodes and N_edges are the count of edges and nodes in the graph.
    // init_graph() initializes data within the nodes and edges of g for network simplex:
    //  * ND_priority(n) is set to the number of incoming tree edges to a node.
    //  * ND_tree_in(n) is allocated to hold all tree edges but, not set.
    //    * will be set in feasible tree, along with ND_tree_out(n)
    //  * ED_cutvalue(n) is central to network simplex and explained in the paper.
    //    * All cutvalues initialized to zero here.
    //  * ED_tree_index(e) is how far away from the tree root this edge is.
    //    * all indexes initialied to -1 here.
    bool feasible = init_graph(g);
    // Prevents re-ranking if the graph is already ranked
    if (!feasible)
        // Rank nodes starting with those with no incoming edges as rank = 0.
        // Other edges are 
	init_rank();

    if (search_size >= 0)
	Search_size = search_size;
    else
	Search_size = SEARCHSIZE;

    {
	int err = feasible_tree();
	if (err != 0) {
	    freeTreeList (g);
	    return err;
	}
    }
    if (maxiter <= 0) {
	freeTreeList (g);
	return 0;
    }

    while ((e = leave_edge())) {
	int err;
	f = enter_edge(e);
	err = update(e, f);
	if (err != 0) {
	    freeTreeList (g);
	    return err;
	}
	iter++;
	if (Verbose && iter % 100 == 0) {
	    if (iter % 1000 == 100)
		fputs(ns, stderr);
	    fprintf(stderr, "%d ", iter);
	    if (iter % 1000 == 0)
		fputc('\n', stderr);
	}
	if (iter >= maxiter)
	    break;
    }
    switch (balance) {
    case 1:
	TB_balance();
	reset_lists();
	break;
    case 2:
	LR_balance();
	break;
    default:
	(void)scan_and_normalize();
	freeTreeList (G);
	break;
    }
    if (Verbose) {
	if (iter >= 100)
	    fputc('\n', stderr);
	fprintf(stderr, "%s%" PRISIZE_T " nodes %" PRISIZE_T " edges %d iter %.2f sec\n",
		ns, N_nodes, N_edges, iter, elapsed_sec());
    }
    return 0;
}

int rank(graph_t * g, int balance, int maxiter)
{
    char *s;
    int search_size;

    if ((s = agget(g, "searchsize")))
	search_size = atoi(s);
    else
	search_size = SEARCHSIZE;

    return rank2 (g, balance, maxiter, search_size);
}

/* set cut value of f, assuming values of edges on one side were already set */
static void x_cutval(edge_t * f)
{
    node_t *v;
    edge_t *e;
    int i, sum, dir;

    /* set v to the node on the side of the edge already searched */
    if (ND_par(agtail(f)) == f) {
	v = agtail(f);
	dir = 1;
    } else {
	v = aghead(f);
	dir = -1;
    }

    sum = 0;
    for (i = 0; (e = ND_out(v).list[i]); i++)
	if (sadd_overflow(sum, x_val(e, v, dir), &sum)) {
	    agerr(AGERR, "overflow when computing edge weight sum\n");
	    graphviz_exit(EXIT_FAILURE);
	}
    for (i = 0; (e = ND_in(v).list[i]); i++)
	if (sadd_overflow(sum, x_val(e, v, dir), &sum)) {
	    agerr(AGERR, "overflow when computing edge weight sum\n");
	    graphviz_exit(EXIT_FAILURE);
	}
    ED_cutvalue(f) = sum;
}

// KAP: typically returns: cut_value(e)-weight(e)
//
// * returns the weight(e) if:
//     low_index(node_v) > lim_index(other) > lim_index(node_v)
//   So, same as:
//     min_index(node_v) > max_index(other) > max_index(node_v)
//   where:
//      * low_index(node) == ND_low(n) - min DFS index for nodes in sub-tree (>= 1)
//      * lim_index(node) == ND_lim(n) max DFS index for nodes in sub-tree
//        Seems like they could have called lim(node) instead: max(node)
// * ELSE returns the cut_value(e)-weight(e) if tree_edge(e)
// * ELSE eturns the -weight(e)
//
// And based on a few factors, may negate the number it returns
//
// SEQ(a,b,c) = ((a) <= (b) && (b) <= (c))
// SEQ returns true if a <= b <= c, so if a,b,c do not decrease.
static int x_val(edge_t * e, node_t * v, int dir)
{
    node_t *other;
    int d, rv, f;

    if (agtail(e) == v)
	other = aghead(e);
    else
	other = agtail(e);
    if (!(SEQ(ND_low(v), ND_lim(other), ND_lim(v)))) {
	f = 1;
	rv = ED_weight(e);
    } else {
	f = 0;
	if (TREE_EDGE(e))
	    rv = ED_cutvalue(e);
	else
	    rv = 0;
	rv -= ED_weight(e);
    }
    if (dir > 0) {
	if (aghead(e) == v)
	    d = 1;
	else
	    d = -1;
    } else {
	if (agtail(e) == v)
	    d = 1;
	else
	    d = -1;
    }
    if (f)
	d = -d;
    if (d < 0)
	rv = -rv;
    return rv;
}

// KAP: Do a recursive depth-first search to set the cur_value paramenter
//      in each edge in the feasible tree.
static void dfs_cutval(node_t * v, edge_t * par)
{
    int i;
    edge_t *e;

    for (i = 0; (e = ND_tree_out(v).list[i]); i++)
	if (e != par)
	    dfs_cutval(aghead(e), e);
    for (i = 0; (e = ND_tree_in(v).list[i]); i++)
	if (e != par)
	    dfs_cutval(agtail(e), e);
    if (par)
	x_cutval(par);
}

/*
* Initializes DFS range attributes (par, low, lim) over tree nodes such that:
* ND_par(n) - parent tree edge
* ND_low(n) - min DFS index for nodes in sub-tree (>= 1)
* ND_lim(n) - max DFS index for nodes in sub-tree
*/
// KAP:
// Initially called from init_cutvalues() with the first node in the graph, and  par=NULL and low=1
// So the first node this is called on is sort of random, unless the node that is returned by GD_nlist
// is specially chosen.  Perhaps it is always the first node mentioned in the graph?
// If G is fully connected, then the depth first search will find all nodes,
// and the first node becomes the root of the tree, with min_tree_index(G) == 1, and
// the index increasing the farther you get from the root.
// index(root) == 1 == min_tree_index().  It would also seem that the root would be the LCA of all
// nodes in the tree.
//
// * ND_low(n) == min_tree_index(n)
// * ND_lim(n) == max_tree_index(n)
// where tree_index is the distance of this node from the head of the tree+1 (since the root
// node is 1)
// So: A(1)
//    / \
//  B(2) C(2)
// /
// D(3)
static int dfs_range_init(node_t *v, edge_t *par, int low) {
    int i, lim;

    lim = low;
    ND_par(v) = par;
    ND_low(v) = low;

    for (i = 0; ND_tree_out(v).list[i]; i++) {
        edge_t *e = ND_tree_out(v).list[i];
        if (e != par) {
            lim = dfs_range_init(aghead(e), e, lim);
        }
    }

    for (i = 0; ND_tree_in(v).list[i]; i++) {
        edge_t *e = ND_tree_in(v).list[i];
        if (e != par) {
            lim = dfs_range_init(agtail(e), e, lim);
        }
    }

    ND_lim(v) = lim;

    return lim + 1;
}

/*
 * Incrementally updates DFS range attributes
 */
static int dfs_range(node_t * v, edge_t * par, int low)
{
    edge_t *e;
    int i, lim;

    if (ND_par(v) == par && ND_low(v) == low) {
	return ND_lim(v) + 1;
    }

    lim = low;
    ND_par(v) = par;
    ND_low(v) = low;
    for (i = 0; (e = ND_tree_out(v).list[i]); i++)
	if (e != par)
	    lim = dfs_range(aghead(e), e, lim);
    for (i = 0; (e = ND_tree_in(v).list[i]); i++)
	if (e != par)
	    lim = dfs_range(agtail(e), e, lim);
    ND_lim(v) = lim;
    return lim + 1;
}

#ifdef DEBUG
void tchk(void)
{
    int i, n_cnt, e_cnt;
    node_t *n;
    edge_t *e;

    n_cnt = 0;
    e_cnt = 0;
    for (n = agfstnode(G); n; n = agnxtnode(G, n)) {
	n_cnt++;
	for (i = 0; (e = ND_tree_out(n).list[i]); i++) {
	    e_cnt++;
	    if (SLACK(e) > 0)
		fprintf(stderr, "not a tight tree %p", e);
	}
    }
    if (n_cnt != Tree_node.size || e_cnt != Tree_edge.size)
	fprintf(stderr, "something missing\n");
}

void check_fast_node(node_t * n)
{
    node_t *nptr;
    nptr = GD_nlist(agraphof(n));
    while (nptr && nptr != n)
	nptr = ND_next(nptr);
    assert(nptr != NULL);
}

static char* dump_node (node_t* n)
{
    static char buf[50];

    if (ND_node_type(n)) {
	snprintf(buf, sizeof(buf), "%p", n);
	return buf;
    }
    else
	return agnameof(n);
}

static void dump_graph (graph_t* g)
{
    int i;
    edge_t *e;
    node_t *n,*w;
    FILE* fp = fopen ("ns.gv", "w");
    fprintf (fp, "digraph \"%s\" {\n", agnameof(g));
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	fprintf (fp, "  \"%s\"\n", dump_node(n));
    }
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	for (i = 0; (e = ND_out(n).list[i]); i++) {
	    fprintf (fp, "  \"%s\"", dump_node(n));
	    w = aghead(e);
	    fprintf (fp, " -> \"%s\"\n", dump_node(w));
	}
    }

    fprintf (fp, "}\n");
    fclose (fp);
}

static node_t *checkdfs(graph_t* g, node_t * n)
{
    edge_t *e;
    node_t *w,*x;
    int i;

    if (ND_mark(n))
	return 0;
    ND_mark(n) = true;
    ND_onstack(n) = true;
    for (i = 0; (e = ND_out(n).list[i]); i++) {
	w = aghead(e);
	if (ND_onstack(w)) {
	    dump_graph (g);
	    fprintf(stderr, "cycle: last edge %lx %s(%lx) %s(%lx)\n",
		(uint64_t)e,
	       	agnameof(n), (uint64_t)n,
		agnameof(w), (uint64_t)w);
	    return w;
	}
	else {
	    if (!ND_mark(w)) {
		x = checkdfs(g, w);
		if (x) {
		    fprintf(stderr,"unwind %lx %s(%lx)\n",
			(uint64_t)e,
			agnameof(n), (uint64_t)n);
		    if (x != n) return x;
		    fprintf(stderr,"unwound to root\n");
		    fflush(stderr);
		    abort();
		    return 0;
		}
	    }
	}
    }
    ND_onstack(n) = false;
    return 0;
}

void check_cycles(graph_t * g)
{
    node_t *n;
    for (n = GD_nlist(g); n; n = ND_next(n)) {
	ND_mark(n) = false;
	ND_onstack(n) = false;
    }
    for (n = GD_nlist(g); n; n = ND_next(n))
	checkdfs(g, n);
}
#endif				/* DEBUG */

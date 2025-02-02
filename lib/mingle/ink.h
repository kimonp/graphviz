/*************************************************************************
 * Copyright (c) 2011 AT&T Intellectual Property
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors: Details at https://graphviz.org
 *************************************************************************/

#pragma once

#include <mingle/edge_bundling.h>
#include <vector>

typedef struct {
  double x, y;
} point_t;

/* given a list of edges, find the best ink bundling by making them meet at 2 points
   \                       /
   -meet1 ---------- meet2 - 
   /                       \
   edges: list of edges
   numEdges: number of edges
   pick: if not NULL, consider edges pick[0], pick[1], ..., pick[numedges-1],
   .     othetwise consider edges 0, 1, ..., numEdge-1
   ink0: ink needed if no bundling
   meet1, meet2: meeting point
   return: best ink needed if bundled.
*/
double ink(const std::vector<pedge> &edges, int numEdges, int *pick,
           double *ink0, point_t *meet1, point_t *meet2, double angle_param,
           double angle);
double ink1(const pedge &e);

extern double ink_count;

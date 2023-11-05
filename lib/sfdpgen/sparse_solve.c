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
#include <string.h>
#include <sfdpgen/sparse_solve.h>
#include <sfdpgen/sfdpinternal.h>
#include <common/memory.h>
#include <math.h>
#include <common/arith.h>
#include <common/types.h>
#include <common/globals.h>

/* #define DEBUG_PRINT */

static double *diag_precon(const double *diag, double *x, double *y) {
  int i, m;
  m = (int) diag[0];
  diag++;
  for (i = 0; i < m; i++) y[i] = x[i]*diag[i];
  return y;
}

static double *diag_precon_new(SparseMatrix A) {
  int i, j, m = A->m, *ia = A->ia, *ja = A->ja;
  double *a = A->a;

  assert(A->type == MATRIX_TYPE_REAL);

  assert(a);

  double *data = N_GNEW(A->m + 1, double);
  double *diag = data;

  diag[0] = m;
  diag++;
  for (i = 0; i < m; i++){
    diag[i] = 1.;
    for (j = ia[i]; j < ia[i+1]; j++){
      if (i == ja[j] && fabs(a[j]) > 0) diag[i] = 1./a[j];
    }
  }

  return data;
}

static double conjugate_gradient(SparseMatrix A, const double *precon, int n,
                                 double *x, double *rhs, double tol,
                                 int maxit) {
  double *z, *r, *p, *q, res, alpha;
  double rho, rho_old = 1, res0, beta;
  int iter = 0;

  z = N_GNEW(n,double);
  r = N_GNEW(n,double);
  p = N_GNEW(n,double);
  q = N_GNEW(n,double);

  SparseMatrix_multiply_vector(A, x, &r);
  r = vector_subtract_to(n, rhs, r);

  res0 = res = sqrt(vector_product(n, r, r))/n;
#ifdef DEBUG_PRINT
    if (Verbose){
      fprintf(stderr, "on entry, cg iter = %d of %d, residual = %g, tol = %g\n", iter, maxit, res, tol);
    }
#endif

  while ((iter++) < maxit && res > tol*res0){
    z = diag_precon(precon, r, z);
    rho = vector_product(n, r, z);

    if (iter > 1){
      beta = rho/rho_old;
      p = vector_saxpy(n, z, p, beta);
    } else {
      memcpy(p, z, sizeof(double)*n);
    }

    SparseMatrix_multiply_vector(A, p, &q);

    alpha = rho/vector_product(n, p, q);

    x = vector_saxpy2(n, x, p, alpha);
    r = vector_saxpy2(n, r, q, -alpha);
    
    res = sqrt(vector_product(n, r, r))/n;

#ifdef DEBUG_PRINT
    if (Verbose && 0){
      fprintf(stderr, "   cg iter = %d, residual = %g, relative res = %g\n", iter, res, res/res0);
    }
#endif



    rho_old = rho;
  }
  free(z); free(r); free(p); free(q);
#ifdef DEBUG
    _statistics[0] += iter - 1;
#endif

#ifdef DEBUG_PRINT
  if (Verbose){
    fprintf(stderr, "   cg iter = %d, residual = %g, relative res = %g\n", iter, res, res/res0);
  }
#endif
  return res;
}

static double cg(SparseMatrix A, const double *precond, int n, int dim,
                 double *x0, double *rhs, double tol, int maxit) {
  double *x, *b, res = 0;
  int k, i;
  x = N_GNEW(n, double);
  b = N_GNEW(n, double);
  for (k = 0; k < dim; k++){
    for (i = 0; i < n; i++) {
      x[i] = x0[i*dim+k];
      b[i] = rhs[i*dim+k];
    }
    
    res += conjugate_gradient(A, precond, n, x, b, tol, maxit);
    for (i = 0; i < n; i++) {
      rhs[i*dim+k] = x[i];
    }
  }
  free(x);
  free(b);
  return res;
}

double SparseMatrix_solve(SparseMatrix A, int dim, double *x0, double *rhs, double tol, int maxit){
  int n = A->m;

  double *precond = diag_precon_new(A);
  double res = cg(A, precond, n, dim, x0, rhs, tol, maxit);
  free(precond);
  return res;
}


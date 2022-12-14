#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"

void vector_add(double *x, double *y, double *r, unsigned N) {
  unsigned i;
  for (i=0; i<N; i++) r[i] = x[i]+y[i];
}

/* jacobi_aux(y,b,x,N) 
   adds vectors y+b and stores result into x;
   returns square of Euclidean distance from old x to new x. */
double jacobi_aux (double *y, double *b, double *x, unsigned N) {
  unsigned i; double s=0.0;
  for (i=0; i<N; i++) {
    double yi = y[i];
    double r = yi+b[i];
    double d = x[i]-yi;
    s = fma(d,d,s);
    x[i]=d;
  }
  return s;
}

/* vector A1 represents the diagonal of NxN matrix A.
   matrix A2 is A-A1.
   b and x are vectors of length N.
 */
void jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc) {
  unsigned i, N=A2->rows;
  double *y = (double *)surely_malloc(N*sizeof(double));
  double *z = (double *)surely_malloc(N*sizeof(double));
  double s;
  for (i=0; i<N; i++) A1[i] = 1.0/A1[i];
  for (i=0; i<N; i++) b[i] *= A1[i];
  diag_mult(A1,A2);
  do {
    crs_matrix_vector_multiply(A2,x,y);
    s=jacobi_aux(y,b,x,N);
  } while (s>acc);
  free(y); free(z);
}


    

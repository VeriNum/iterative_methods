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
   subtracts vectors b-y and stores result into x;
   returns square of Euclidean distance from old x to new x. */
double jacobi_aux (double *y, double *b, double *x, unsigned N) {
  unsigned i; double s=0.0;
  for (i=0; i<N; i++) {
    double yi = y[i];
    double r = b[i]-yi;
    double d = x[i]-r;
    s = fma(d,d,s);
    x[i]=r;
  }
  return s;
}

/* vector A1 represents the diagonal of NxN matrix A.
   matrix A2 is A-A1.
   b and x are vectors of length N.
   At start, x is initialized to some arbitraryish vector.
   At finish, x is some vector that's within acc^2 Euclidean distance 
   of (A x - b).
 */
void jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc) {
  unsigned i, N=A2->rows;
  double *y = (double *)surely_malloc(N*sizeof(double));
  double s;
  for (i=0; i<N; i++) A1[i] = 1.0/A1[i];
  for (i=0; i<N; i++) b[i] *= A1[i];
  diag_mult(A1,A2);
  do {
    crs_matrix_vector_multiply(A2,x,y);
    s=jacobi_aux(y,b,x,N);
  } while (s>acc);
  free(y);
}

struct jtask {
  struct crs_matrix A2;
  double *b;
  double *x;
  double *y;
  double s;
  unsigned delta;
  unsigned phase;
};

void phase0 (struct jtask *p) {
  double *b = p->b, *x = p->x, *y = p->y, s=0;
  unsigned i, delta=p->delta, N=p->A2.rows;
  crs_matrix_vector_multiply(&p->A2,x,y);    
  for (i=0; i<N; i++) {
    double yi = y[i];
    double r = b[i]-yi;
    double d = x[i+delta]-r;
    y[i]=r;
    s = fma(d,d,s);
  }
  p->s=s;
  p->phase=1;
}

void phase1 (struct jtask *p) {
  double *x = p->x, *y = p->y;
  unsigned i, N=p->A2.rows, delta=p->delta;
  for (i=0; i<N; i++)
    x[i+delta]=y[i];
  p->phase=0;
}

void jacobi_worker(void *closure) {
  struct jtask *p = (struct jtask *)closure;
  if (p->phase)
    phase1(p);
  else phase0(p);
}


  
typedef unsigned long long ubig;

unsigned threads = 1;

void par_jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc) {
  unsigned i, N=A2->rows, t, T=threads, delta, delta_next;
  double *y = (double *)surely_malloc(N*sizeof(double));
  struct jtask *jt = (struct jtask *)surely_malloc(T*sizeof(struct jtask));
  struct task *tasks = make_tasks(T);
  double s;
  for (i=0; i<N; i++) A1[i] = 1.0/A1[i];
  for (i=0; i<N; i++) b[i] *= A1[i];
  delta=0;
  for (t=0; t<T; t++) {
    struct jtask *p = jt+t; /* need this workaround for VST issue #613 */
    delta_next = ((ubig)(t+1))*((ubig)N)/((ubig)T);
    p->A2.val=A2->val;
    p->A2.col_ind=A2->col_ind;
    p->A2.row_ptr=A2->row_ptr+delta;
    p->A2.rows=delta_next-delta;
    p->A2.cols=A2->cols;
    p->b=b;
    p->x=x;
    p->y=y+delta;
    p->delta=delta;
    delta=delta_next;
    initialize_task(tasks, t, jacobi_worker, p);
  }

  do {
    double s=0.0;
    do_tasks(tasks, T);  /* phase 0 */
    for (t=0; t<T; t++) s += jt[t].s;
    do_tasks(tasks, T);  /* phase 1 */
  } while (s>acc);
}

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
double jacobi_aux (double *A1, double *y, double *b, double *x, unsigned N) {
  unsigned i; double s=0.0;
  for (i=0; i<N; i++) {
    double r = A1[i]*(b[i]-y[i]);
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
void jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc, unsigned maxiter) {
  unsigned i, N=A2->rows;
  double *y = (double *)surely_malloc(N*sizeof(double));
  double s;
  for (i=0; i<N; i++) A1[i] = 1.0/A1[i];
  do {
    if (maxiter-- == 0) break;
    crs_matrix_vector_multiply(A2,x,y);
    s=jacobi_aux(A1,y,b,x,N);
  } while (s>acc);
  free(y);
}

double jacobi2_oneiter(double *A1inv, struct crs_matrix *A2, double *b, double *x, double *y) {
  unsigned i, N=crs_matrix_rows(A2);
  double s = 0.0;
  for (i=0; i<N; i++) {
      double r = A1inv[i]*(b[i] - crs_row_vector_multiply(A2,x,i));
      double d = x[i]-r;
      s = fma(d,d,s);
      y[i] = r;
    }
  return s;
}

double jacobi2(double *A1, struct crs_matrix *A2, double *b, double *x, double acc, unsigned maxiter) {
  unsigned i, N=crs_matrix_rows(A2);
  double s=0.0,  /* need to initialize s just to keep the proof happy */
     *t, *z=x, 
    *y = (double *)surely_malloc(N*sizeof(double)),
    *A1inv = (double *)surely_malloc(N*sizeof(double));
  for (i=0; i<N; i++) A1inv[i] = 1.0/A1[i];
  do {
    s = jacobi2_oneiter(A1inv,A2,b,z,y);
    t=z; z=y; y=t;
    maxiter--;
  } while (s*0==0.0 && s>acc && maxiter);
  if (z!=x) {
    for (i=0; i<N; i++) x[i]=z[i];
    y=z;
  }
  free(y);
  free (A1inv);
  return s;
}

struct jtask {
  struct crs_matrix A2;
  double *A1;
  double *b;
  double *x;
  double *y;
  double s;
  unsigned delta;
  unsigned phase;
};

void phase0 (struct jtask *p) {
  double *A1=p->A1, *b = p->b, *x = p->x, *y = p->y, s=0;
  unsigned i, delta=p->delta, N=p->A2.rows;
  crs_matrix_vector_multiply(&p->A2,x,y);    
  for (i=0; i<N; i++) {
    double r = A1[i]*(b[i]-y[i]);
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
  delta=0;
  for (t=0; t<T; t++) {
    struct jtask *p = jt+t; /* need this workaround for VST issue #613 */
    delta_next = ((ubig)(t+1))*((ubig)N)/((ubig)T);
    p->A2.val=A2->val;
    p->A2.col_ind=A2->col_ind;
    p->A2.row_ptr=A2->row_ptr+delta;
    p->A2.rows=delta_next-delta;
    p->A2.cols=A2->cols;
    p->A1=A1;
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

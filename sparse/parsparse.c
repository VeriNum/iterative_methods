#include <stdlib.h>
#include <math.h>
#include "sparse.h"
#include "parsplit.h"
#include "parsparse.h"

typedef unsigned long long ubig;

struct mtask {
  struct csr_matrix mat;
  double *vec;
  double *result;
};

struct mtask *split_csr_matrix (
      struct csr_matrix *m, double *vec, double *result, unsigned int T) {
  struct mtask *arr = (struct mtask *)surely_malloc(T * sizeof(*arr));
  unsigned delta=0, delta_next;
  unsigned t, n=m->rows;
  for (t=0;t<T;t++) {
    struct mtask *p = arr+t; /* need this workaround for VST issue #613 */
    delta_next = ((ubig)(t+1))*((ubig)n)/((ubig)T);
    p->mat.val=m->val;
    p->mat.col_ind=m->col_ind;
    p->mat.row_ptr=m->row_ptr+delta;
    p->mat.rows=delta_next-delta;
    p->mat.cols=m->cols;
    p->vec=vec;
    p->result=result+delta;
    delta=delta_next;
  }
  return arr;
}

void worker(void *closure) {
  struct mtask *p = (struct mtask *)closure;
  csr_matrix_vector_multiply(&p->mat,p->vec,p->result);
}

struct task *make_multiply_tasks (struct csr_matrix *m, double *v, double *p, unsigned T) {
  unsigned t;
  struct task *tasks = make_tasks(T);
  struct mtask *arr = split_csr_matrix(m,v,p,T);
  for (t=0; t<T; t++)
    initialize_task(tasks, t, worker, arr+t);
  return tasks;
}  

void par_matrix_vector_multiply (struct task *jobs, unsigned T) {
  do_tasks(jobs,T);
}

/*
void alt_matrix_vector_multiply (struct csr_matrix *m, double *v, double *p, unsigned T) {
  struct mtask *arr = split_csr_matrix(m,v,p,T);
  unsigned t;
  for (t=0; t<T; t++) worker(arr+t);
}
*/
  



#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <pthread.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include "jacobi.h"

unsigned num_threads = 8;

typedef struct {
  double a1;
  double *v1; 
  double a2; 
  double *v2;
  double *res;
  unsigned start_idx;
  unsigned end_idx;
} vector_linear_comb_data;

void* vector_linear_comb_thread(void *arg) 
{
  vector_linear_comb_data *data = (vector_linear_comb_data*) arg;
  for (unsigned i = data->start_idx; i < data->end_idx; ++i) {
    data->res[i] = data->a1 * data->v1[i] + data->a2 * data->v2[i];
  }
  return NULL;
}
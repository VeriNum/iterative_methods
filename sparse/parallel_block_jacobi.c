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
    data->res[i] = fma(data->a1, data->v1[i], 0.0);
    data->res[i] = fma(data->a2, data->v2[i], data->res[i]);
  }
  return NULL;
}

void vector_linear_comb_parallel(double a1, double *v1, double a2, double *v2, double *res, unsigned N)
{
  pthread_t threads[num_threads];
  vector_linear_comb_data thread_data[num_threads];
  unsigned chunk_size = N / num_threads;

  int i;

  for (i = 0; i < num_threads; i++) {
    thread_data[i].a1 = a1;
    thread_data[i].v1 = v1;
    thread_data[i].a2 = a2;
    thread_data[i].v2 = v2;
    thread_data[i].res = res;
    thread_data[i].start_idx = i * chunk_size;
    thread_data[i].end_idx = (i == num_threads - 1) ? N : (i + 1) * chunk_size;
    pthread_create(&threads[i], NULL, vector_linear_comb_thread, &thread_data[i]);
  }

  for (i = 0; i < num_threads; i++) {
    pthread_join(threads[i], NULL);
  }

}
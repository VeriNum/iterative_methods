#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <pthread.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include "jacobi.h"

#include <time.h>

unsigned num_threads = 16;

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

void vector_linear_comb(double a1, double *v1, double a2, double *v2, double *res, unsigned N)
{
  int i;
  for (i = 0; i < N; i++) {
    res[i] = fma(a1, v1[i], 0);
    res[i] = fma(a2, v2[i], res[i]);
  }
}

void block_inverse(double *A, double *B, unsigned left, unsigned right, unsigned N)
{
  int i, j, k;
  double t;

  for (i = left; i < right; i++) {
    for (j = left; j < right; j++) {
      if (i == j) {
        B[i*N + j] = 1.0;
      } else {
        B[i*N + j] = 0.0;
      }
    }
  }

  for (i = left; i < right; i++) {
    t = A[i*N + i];
    for (j = left; j < right; j++) {
      A[i*N + j] /= t;
      B[i*N + j] /= t;
    }

    for (j = left; j < right; j++) {
      if (i == j) continue;
      t = A[j*N + i];
      for (k = left; k < right; k++) {
        A[j*N + k] -= t * A[i*N + k];
        B[j*N + k] -= t * B[i*N + k];
      }
    }
  }
}

typedef struct {
  double *A;
  double *B;
  unsigned *block_idx;
  unsigned N;
  unsigned block_num;
  unsigned start_idx;
  unsigned end_idx;
} block_matrix_inverse_data;

void* block_matrix_inverse_thread(void *arg)
{
  block_matrix_inverse_data *data = (block_matrix_inverse_data*) arg;
  for (unsigned i = data->start_idx; i < data->end_idx; ++i) {
    if (i == data->block_num - 1) {
      block_inverse(data->A, data->B, data->block_idx[i], data->N, data->N);
    } else {
      block_inverse(data->A, data->B, data->block_idx[i], data->block_idx[i+1], data->N);
    }
  }
  return NULL;
}

void block_matrix_inverse_parallel(double *A, double *B, unsigned *block_idx, unsigned N, unsigned block_num)
{
  int i, j;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
        B[i*N + j] = 0.0;
    }
  }

  pthread_t threads[num_threads];
  block_matrix_inverse_data thread_data[num_threads];
  unsigned chunk_size = block_num / num_threads;

  for (i = 0; i < num_threads; i++) {
    thread_data[i].A = A;
    thread_data[i].B = B;
    thread_data[i].block_idx = block_idx;
    thread_data[i].N = N;
    thread_data[i].block_num = block_num;
    thread_data[i].start_idx = i * chunk_size;
    thread_data[i].end_idx = (i == num_threads - 1) ? block_num : (i + 1) * chunk_size;

    pthread_create(&threads[i], NULL, block_matrix_inverse_thread, &thread_data[i]);
  }

  for (unsigned i = 0; i < num_threads; i++) {
    pthread_join(threads[i], NULL);
  }
}

void block_diagonal_partition (double *A, double *A1, double *A2, unsigned *block_idx, unsigned N, unsigned block_num)
{
  int i, j, k;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      A1[i*N + j] = 0.0;
      A2[i*N + j] = A[i*N + j];
    }
  }

  for (i = 0; i < block_num; i++) {
    if (i == block_num - 1) {
      for (j = block_idx[i]; j < N; j++) {
        for (k = block_idx[i]; k < N; k++) {
          A1[j*N + k] = A[j*N + k];
          A2[j*N + k] = 0.0;
        }
      }
    } else {
      for (j = block_idx[i]; j < block_idx[i+1]; j++) {
        for (k = block_idx[i]; k < block_idx[i+1]; k++) {
          A1[j*N + k] = A[j*N + k];
          A2[j*N + k] = 0.0;
        }
      }
    }
  }
}

typedef struct {
  double *A;
  double *v;
  double *res;
  // unsigned *block_idx;
  unsigned N;
  // unsigned block_num;
  unsigned start_idx;
  unsigned end_idx;
} matrix_vector_multiply_data;

void *matrix_vector_multiply_thread(void *arg) 
{
  matrix_vector_multiply_data *data = (matrix_vector_multiply_data *)arg;
  for (unsigned i = data->start_idx; i < data->end_idx; i++) {
    data->res[i] = 0;
    for (unsigned j = 0; j < data->N; j++) {
      data->res[i] = fma(data->A[i * data->N + j], data->v[j], data->res[i]);
    }
  }
  return NULL;
}

void matrix_vector_multiplication_parallel(double *A, double *v, double *res, unsigned N)
{
  pthread_t threads[num_threads];
  matrix_vector_multiply_data thread_data[num_threads];
  unsigned rows_per_thread = N / num_threads;

  for (unsigned i = 0; i < num_threads; i++) {
    thread_data[i].A = A;
    thread_data[i].v = v;
    thread_data[i].res = res;
    // thread_data[i].block_idx = block_idx;
    thread_data[i].N = N;
    // thread_data[i].block_num = block_num;
    thread_data[i].start_idx = i * rows_per_thread;
    thread_data[i].end_idx = (i == num_threads - 1) ? N : (i + 1) * rows_per_thread;

    pthread_create(&threads[i], NULL, matrix_vector_multiply_thread, &thread_data[i]);
  }

  for (unsigned i = 0; i < num_threads; i++) {
    pthread_join(threads[i], NULL);
  }
}

void matrix_vector_multiplication(double *A, double *v, double *res, unsigned N) 
{
  int i, j;
  double t;
  for (i = 0; i < N; i++) {
    t = 0.0;
    for (j = 0; j < N; j++) {
      t = fma(A[i*N + j], v[j], t);
    }
    res[i] = t;
  }
}

double l2norm(double *x, unsigned N)
{
  double s = 0.0;
  for (int i = 0; i < N; i++) {
    s = fma(x[i], x[i], s);
  }
  return sqrt(s);
}

double residual(double *A, double *b, double *x, unsigned N)
{
  double s = 0.0;
  double t1[N];
  matrix_vector_multiplication(A, x, t1, N);

  double t2[N];
  vector_linear_comb(1.0, b, -1.0, t1, t2, N);

  s = l2norm(t2, N);
  return s;
}

void block_jacobi_oneiter(double *A1inv, double *A2, double *b, double *x, unsigned N)
{
  double t1[N];
  double t2[N];

  matrix_vector_multiplication_parallel(A2, x, t1, N);
  vector_linear_comb_parallel(1.0, b, -1.0, t1, t2, N);
  matrix_vector_multiplication_parallel(A1inv, t2, x, N);

}

void block_jacobi(double *A, double *b, double *x0, unsigned *block_idx, unsigned N, unsigned block_num, double acc, unsigned max_iter) 
{

  clock_t t0 = clock();
  double A1[N * N];
  double A2[N * N];
  block_diagonal_partition(A, A1, A2, block_idx, N, block_num);

  double A1inv[N * N];
  block_matrix_inverse_parallel(A1, A1inv, block_idx, N, block_num);
  clock_t t1 = clock();

  double x[N];
  for (int i = 0; i < N; i++) {
    x[i] = x0[i];
  }

  double res = 2 * acc;
  unsigned iter = 0;

  while (res > acc && iter < max_iter) {
    block_jacobi_oneiter(A1inv, A2, b, x, N);

    printf("Iteration %d:\n", iter);
    res = residual(A, b, x, N);
    iter++;
    printf("x = [");
    for (int i = 0; i < N; i++) {
      printf("%.4f ", x[i]);
    }
    printf("]\n");
    printf("residual = %.6f\n", res);

  }

  clock_t t2 = clock();

  double time_spent1 = (double)(t1 - t0) / CLOCKS_PER_SEC;
  double time_spent2 = (double)(t2 - t1) / CLOCKS_PER_SEC;
  printf("Time spent on inverse: %f\n", time_spent1);
  printf("Time spent on iteration: %f\n", time_spent2);
}


int main()
{
  unsigned N = 200;
  double A[N * N];

  unsigned block_idx[10] = {0, 20, 40, 60, 80, 100, 120, 140, 160, 180};
  for (int i = 0; i < N; i++){
    for (int j = 0; j < N; j++) {
      if (i == j) {
        A[i * N + j] = 2.0 * N + 1;
      } else {
        A[i * N + j] = 1.0;
      }
    }
  }

  double tempx[N];
  for (int i = 0; i < N; i++) tempx[i] = 1.0;

  double b[N];
  matrix_vector_multiplication(A, tempx, b, N);

  double x[N];
  for (int i = 0; i < N; i++) x[i] = 0.0;

  clock_t start = clock();

  block_jacobi(A, b, x, block_idx, N, 5, 1e-6, 100);

  clock_t end = clock();
  double time_spent = (double)(end - start) / CLOCKS_PER_SEC;
  printf("Number of threads: %d\n", num_threads);
  printf("Time spent: %f\n", time_spent);




  // unsigned block_idx[3] = {0, 3, 10};
  // for (int i = 0; i < N; i++) {
  //   for (int j = 0; j < N; j++) {
  //     if (i == j) {
  //       A[i*N + j] = 2.0 * N + 1;
  //     } else {
  //       A[i*N + j] = 0.0;
  //     }
  //   }
  // }

  // A[0 * N + 1] = 5.0;
  // A[1 * N + 0] = 5.0;

  // for (int i = 0; i < N; i++) {
  //   for (int j = 0; j < N; j++) {
  //     printf("%f ", A[i*N + j]);
  //   }
  //   printf("\n");
  // }

  // block_matrix_inverse_parallel(A, B, block_idx, N, 3);

  // printf("\n");

  // for (int i = 0; i < N; i++) {
  //   for (int j = 0; j < N; j++) {
  //     printf("%f ", B[i*N + j]);
  //   }
  //   printf("\n");
  // }

  return 0;

}
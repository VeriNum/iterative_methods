#include <stdlib.h>
#include "parsparse.h"

int main(void) {
  struct task *jobs =  make_multiply_tasks(NULL, NULL, NULL, 4);
  par_matrix_vector_multiply(jobs, 4);
  return 0;
}


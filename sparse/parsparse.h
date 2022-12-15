struct crs_matrix;

struct task *make_multiply_tasks (struct crs_matrix *m, double *v, double *p, unsigned T);

void par_matrix_vector_multiply (struct task *jobs, unsigned T);

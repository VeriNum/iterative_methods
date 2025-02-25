#ifndef SPARSE_DOT_H
#define SPARSE_DOT_H

#include <stddef.h>
#include <sys/time.h>

/* Compressed Row Storage (CRS) representation of matrix,
   see section 4.3.1 of 
   "Templates for the Solution of Linear Systems: Building Blocks 
    for Iterative Methods" by Richard Barrett et al., 
    https://netlib.org/templates/templates.pdf
*/
struct crs_matrix {
  double *val;
  unsigned *col_ind;
  unsigned *row_ptr;
  unsigned rows, cols;
};

void *surely_malloc(size_t n);

unsigned crs_matrix_rows(struct crs_matrix *m);

void crs_matrix_vector_multiply (struct crs_matrix *m, double *v, double *p);
double crs_row_vector_multiply(struct crs_matrix *m, double *v, unsigned i);
void crs_matrix_vector_multiply_byrows (struct crs_matrix *m, double *v, double *p);

/* Let D be a diagonal matrix, whose diagonal is represented
   as the vector diag.  Let A be a matrix with number of rows equal
   to dimension of D.  let m represent A.
   Then diag_mult(diag,m) sets m to represent D*A */
void diag_mult(double *diag, struct crs_matrix *m);


struct crs_matrix *make_example(unsigned N, unsigned D, double diag);
void dump_crs_matrix  (struct crs_matrix *m);
void print_crs_matrix (struct crs_matrix *m);
double timediff(struct timeval *start, struct timeval *finish);

struct coo_matrix {
  unsigned *row_ind, *col_ind;
  double *val;
  unsigned n, maxn;
  unsigned rows, cols;
};

struct coo_matrix *create_coo_matrix (unsigned maxn, unsigned rows, unsigned cols);
void add_to_coo_matrix(struct coo_matrix *p, unsigned i, unsigned j, double x);
struct crs_matrix *coo_to_crs_matrix(struct coo_matrix *p);




#endif

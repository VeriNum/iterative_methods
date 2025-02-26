#include "../sparse/sparse.h"

struct coo_matrix *p;
struct vertex_data;  /* abstract (opaque) */

struct elements {
  unsigned n_elements;             /* number of triangles */
  unsigned n_vertices;             /* number of vertices */
  unsigned n_interior;             /* number of interior vertices */
  unsigned (*corner)[3];  /* variable-length array, corner[n_elements][3] */
  struct vertex_data **vdata;  /* variable-length array, vdata[n_vertices] */
  unsigned (*count_coo_entries)(struct elements *p, unsigned elem[3]);
  void (*add_to_coo)(struct coo_matrix *m, double *vec, struct elements *p, unsigned elem);
};

struct coo_matrix *finite_elem_to_coo (struct elements *p) {
  struct coo_matrix *m;
  unsigned n = p->n_elements;
  unsigned interior = p->n_interior;
  unsigned i,e;
  unsigned count=0;
  unsigned (*corner)[3] = p->corner;
  double *vec = (double *)(interior*sizeof(double));
  for (i=0; i<interior; i++) vec[i]=0.0;
  for (e=0; e<n; e++)
    count += p->count_coo_entries(p, corner[e]);
  m = create_coo_matrix(count, interior, interior);
  for (e=0; e<n; e++)
    p->add_to_coo(m, vec, p, e);
  return m;
}


  
/* --------------------------- */
/* ------ Usage example ------ */

struct my_vertex_data {
  double x, y;
};

unsigned my_count_coo_entries(struct elements *p, unsigned elem[3]) {
  unsigned interior = p->n_interior;
  unsigned k = (elem[0]<interior)+(elem[1]<interior)+(elem[2]<interior);
  return k*k;
}

extern double sqr(double);
extern double sqrt(double);

double distance2(struct my_vertex_data *a, struct my_vertex_data *b) {
  return sqr(a->x-b->x)+sqr(a->y-b->y);
}

void add_vertex(struct coo_matrix *m, double *vec,
		       struct my_vertex_data **vdata, unsigned interior, unsigned a) {
  if (a<interior)
    add_to_coo_matrix(m,a,a,4.0);
}


void add_edge(struct coo_matrix *m, double *vec,
		      struct my_vertex_data **vdata, unsigned interior, unsigned a, unsigned b) {
    double h = distance2(vdata[a],vdata[b]);
    double x = 1.0/h;
    if (a<interior && b<interior) {
      add_to_coo_matrix(p, a, b, x);
      add_to_coo_matrix(p, b, a, x);
    }
    else if (a<interior)
      vec[b] += x;
    else if (b<interior)
      vec[a] += x;
}

void my_add_to_coo(struct coo_matrix *m, double *vec, struct elements *p, unsigned elem) {
  unsigned *triangle = p->corner[elem];
  unsigned a = triangle[0];
  unsigned b = triangle[1];
  unsigned c = triangle[2];
  unsigned interior = p->n_interior;
  struct my_vertex_data **vdata = (struct my_vertex_data**) p->vdata;
  add_vertex(m,vec,vdata,interior,a);
  add_vertex(m,vec,vdata,interior,b);
  add_vertex(m,vec,vdata,interior,c);
  add_edge(m,vec,vdata,interior,a,b);
  add_edge(m,vec,vdata,interior,b,c);
  add_edge(m,vec,vdata,interior,c,a);
}

struct coo_matrix *planar_triangulation_to_matrix(struct elements *p, struct my_vertex_data *vdata) {
  p->vdata = (struct vertex_data **) vdata;
  p->count_coo_entries = &my_count_coo_entries;
  p->add_to_coo = &my_add_to_coo;
  return finite_elem_to_coo(p);
}

  

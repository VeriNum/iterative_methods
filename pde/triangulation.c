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
  void (*add_to_coo)(struct coo_matrix *m, double *vec, struct elements *p, unsigned e);
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

void my_add_to_coo(struct coo_matrix *m, double *vec, struct elements *p, unsigned e) {
  unsigned *triangle = p->corner[e];
  unsigned a = triangle[0];
  unsigned b = triangle[1];
  unsigned c = triangle[2];
  unsigned interior = p->n_interior;
  struct my_vertex_data **vdata = (struct my_vertex_data**) p->vdata;
  double ax=vdata[a]->x, ay=vdata[a]->y;
  double bx=vdata[b]->x, by=vdata[b]->y;
  double cx=vdata[b]->x, cy=vdata[c]->y;

  /* Fill in quadrature here.  At this point, the vertex numbers are a,b,c,
     and their coordinates are (ax,ay), (bx,by), (cx,cy).
     A vertex a is interior if (a<interior), otherwise exterior.
     To add an element (i,j,x) to the matrix, for i<interior, j<interior,
          add_to_coo_matrix(m,i,j,x).
     To add an element (i,x) to the vector,
          vec[i]+=x.
  */	  
}

struct coo_matrix *planar_triangulation_to_matrix(struct elements *p, struct my_vertex_data *vdata) {
  p->vdata = (struct vertex_data **) vdata;
  p->count_coo_entries = &my_count_coo_entries;
  p->add_to_coo = &my_add_to_coo;
  return finite_elem_to_coo(p);
}

  

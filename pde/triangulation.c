struct coo_matrix *p;
struct vertex_data;  /* abstract (opaque) */

struct elements {
  unsigned n_elements;             /* number of triangles */
  unsigned n_vertices;             /* number of vertices */
  unsigned n_interior;             /* number of interior vertices */
  unsigned (*corner)[3];  /* variable-length array, corner[n_elements][3] */
  struct vertex_data **vdata;  /* variable-length array, vdata[n_vertices] */
  unsigned (*count_coo_entries)(struct elements *p, unsigned elem);
  void (*add_to_coo)(struct coo_matrix *m, struct elements *p, unsigned elem);
};

struct coo_matrix *finite_elem_to_coo (struct elements *p) {
  struct coo_matrix *m;
  unsigned n = p->n_elements;
  unsigned e;
  unsigned count=0;
  unsigned (*corner)[3] = p->corner;
  for (e=0; e<n; e++)
    count += p->count_coo_entries(p, corner[e]);
  m = create_coo_matrix(count, n_interior, n_interior);
  for (e=0; e<n; e++)
    add_to_coo(m, p, corner[e]);
  return m;
}


  
/* --------------------------- */
/* ------ Usage example ------ */

struct my_vertex_data {
  double x, y;
};

unsigned my_count_coo_entries(struct elements *p, unsigned elem) {
  unsigned k = (p->corner[elem][0]<interior)+(p->corner[elem][1]<interior)+(p->corner[elem][2]<interior);
  return k*k;
}

void add_edges_to_coo(struct coo_matrix *m, struct vertex_data **vdata, unsigned a, unsigned b) {
  if (a<interior && b < interior) {
    double h = distance(vdata[a],vdata[b]);
    double x = 1.0/(h*h);
    add_to_coo_matrix(p, a, b, x);
    add_to_coo_matrix(p, b, a, x);
  }
}

void my_add_to_coo(struct coo_matrix *m, struct elements *p, unsigned elem) {
  unsigned a = p->corner[elem][0];
  unsigned b = p->corner[elem][1];
  unsigned c = p->corner[elem][2];
  unsigned interior = p->n_interior;
  struct vertex_data **vdata = p->vdata;
  if (a<interior) add_to_coo_matrix(p, a, a, 4.0);
  if (b<interior) add_to_coo_matrix(p, b, b, 4.0);
  if (c<interior) add_to_coo_matrix(p, c, c, 4.0);
  add_edges_to_coo(m,vdata,a,b);
  add_edges_to_coo(m,vdata,b,c);
  add_edges_to_coo(m,vdata,c,a);
}

struct coo_matrix *planar_triangulation_to_matrix(struct elements *p, struct my_vertex_data *vdata) {
  p->vdata = vdata;
  p->count_coo_entries = &my_count_coo_entries;
  p->add_to_coo = &my_count_coo_entries;
  return finite_elem_to_coo(p);
}

  

Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import VSTlib.spec_malloc.
#[export] Declare Instance M: MallocAPD.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Require Import Iterative.sparse.spec_sparse.

Definition jacobi2_oneiter_spec :=
 DECLARE _jacobi2_oneiter
 WITH shA1: share, shA2: share, shb: share, shx: share, shy: share,
      A1p: val, A1: vector Tdouble, A2p: val, A2: matrix Tdouble, 
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      yp: val
 PRE [ tptr tdouble, tptr t_crs, tptr tdouble, tptr tdouble, tptr tdouble ]
    PROP(readable_share shA1; readable_share shA2; readable_share shb;
             readable_share shx; writable_share shy;
             matrix_cols A2 (matrix_rows A2);
             matrix_rows A2 < Int.max_unsigned;
             Forall finite A1;  Forall (Forall finite) A2; 
             Forall finite b; Forall finite x)
    PARAMS(A1p; A2p; bp; xp; yp)
    SEP (data_at shA1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           crs_rep shA2 A2 A2p;
           data_at shb (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at shx (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at_ shy (tarray tdouble (matrix_rows A2)) yp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX s: ftype Tdouble,
    PROP( floatlist_eqv y  (jacobi_iter A1 A2 b x); 
              float_eqv s (norm2 (vector_sub x y)))
    RETURN(Vfloat s)
    SEP (data_at shA1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           crs_rep shA2 A2 A2p;
           data_at shb (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at shx (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at shy (tarray tdouble (matrix_rows A2)) (map Vfloat y) yp).

Definition jacobi2_spec :=
 DECLARE _jacobi2
 WITH shA1: share, shA2: share, shb: share,
      A: matrix Tdouble, A1p: val, A1: vector Tdouble, A2p: val, A2: matrix Tdouble, 
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      acc: ftype Tdouble, maxiter: Z, gv: globals
 PRE [ tptr tdouble, tptr t_crs, tptr tdouble, tptr tdouble, tdouble, tuint ]
    PROP(readable_share shA1; readable_share shA2; readable_share shb;
             matrix_cols A (matrix_rows A);
             0 < matrix_rows A < Int.max_unsigned;
             Forall (Forall finite) A; 
             Forall finite (invert_diagmatrix (diag_of_matrix A));
             Forall finite b; Forall finite x; finite acc; 
             0 < maxiter <= Int.max_unsigned)
    PARAMS(A1p; A2p; bp; xp; Vfloat acc; Vint (Int.repr maxiter)) GLOBALS(gv)
    SEP (mem_mgr gv;
           data_at shA1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           crs_rep shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat x) xp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX n:nat, EX s: ftype Tdouble,
    PROP(floatlist_eqv y  (jacobi_n A b x (S n)); 
             Z.of_nat n < maxiter; 
             float_eqv s (norm2 (vector_sub (jacobi_n A b x n) y)))
    RETURN(Vfloat s)
    SEP (mem_mgr gv;
           data_at shA1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           crs_rep shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat y) xp).

Definition JacobiASI : funspecs := [ jacobi2_oneiter_spec; jacobi2_spec ].

Lemma Zlength_jacobi_iter: 
  forall {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_iter A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_iter, diagmatrix_vector_mult,
        vector_sub, map2.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      unfold matrix_vector_mult.
      rewrite Zlength_map. unfold matrix_rows in *. lia.
Qed.

Lemma Znth_jacobi_iter {t}:
  forall i A1 A2 (b x: vector t) (y: ftype t),
  Zlength A1 = matrix_rows A2 -> 
  Zlength b = matrix_rows A2 -> 
  Zlength x = matrix_rows A2 -> 
  0 <= i < matrix_rows A2 ->
  float_eqv y (dotprod (Znth i A2) x) ->
  float_eqv (Znth i (jacobi_iter A1 A2 b x))
     (BMULT t (Znth i A1)
         (BMINUS t (Znth i b) y)).
Proof.
intros. unfold matrix_rows in *.
 unfold jacobi_iter, diagmatrix_vector_mult, vector_sub, map2,
   matrix_vector_mult.
  rewrite Znth_map.
2:rewrite Zlength_combine, Zlength_map,
     Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite Zlength_map, Zlength_combine, Zlength_map; lia.
rewrite Znth_map.
2:rewrite Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite Zlength_map; lia.
rewrite Znth_map by lia.
unfold uncurry.
apply BMULT_congr; auto.
apply BMINUS_congr; auto.
symmetry.
auto.
Qed.



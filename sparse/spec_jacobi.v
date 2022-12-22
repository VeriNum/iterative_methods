Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Require Import Iterative.sparse.spec_sparse.

Definition jacobi2_oneiter_spec :=
 DECLARE _jacobi2_oneiter
 WITH sh1: share, sh2: share,
      A1p: val, A1: vector Tdouble, A2p: val, A2: matrix Tdouble, 
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      yp: val
 PRE [ tptr tdouble, tptr t_crs, tptr tdouble, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; writable_share sh2;
             matrix_cols A2 (matrix_rows A2);
             matrix_rows A2 < Int.max_unsigned;
             Forall finite A1;  Forall (Forall finite) A2; 
             Forall finite b; Forall finite x)
    PARAMS(A1p; A2p; bp; xp; yp)
    SEP (data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           crs_rep sh1 A2 A2p;
           data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at_ sh2 (tarray tdouble (matrix_rows A2)) yp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX s: ftype Tdouble,
    PROP( floatlist_eqv y  (jacobi_iter A1 A2 b x); 
              float_eqv s (norm2 (vector_sub x y)))
    RETURN(Vfloat s)
    SEP (data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           crs_rep sh1 A2 A2p;
           data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at sh1 (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at sh2 (tarray tdouble (matrix_rows A2)) (map Vfloat y) yp).

Definition jacobi2_spec :=
 DECLARE _jacobi2
 WITH sh1: share, sh2: share,
      A: matrix Tdouble, A1p: val, A1: vector Tdouble, A2p: val, A2: matrix Tdouble, 
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      acc: ftype Tdouble, maxiter: Z
 PRE [ tptr tdouble, tptr t_crs, tptr tdouble, tptr tdouble, tdouble, tuint ]
    PROP(readable_share sh1; writable_share sh2;
             matrix_cols A (matrix_rows A);
             matrix_rows A < Int.max_unsigned;
             Forall (Forall finite) A; 
             Forall finite b; Forall finite x; finite acc; 
             0 <= maxiter <= Int.max_unsigned)
    PARAMS(A1p; A2p; bp; xp; Vfloat acc; Vint (Int.repr maxiter))
    SEP (data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           crs_rep sh1 (remove_diag A) A2p;
           data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat x) xp)
 POST [ tvoid ]
   EX y: vector Tdouble,
    PROP(floatlist_eqv y  (jacobi A b x acc (Z.to_nat maxiter)))
    RETURN()
    SEP (data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           crs_rep sh1 (remove_diag A) A2p;
           data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at sh1 (tarray tdouble (matrix_rows A)) (map Vfloat y) xp).

Definition JacobiASI : funspecs := [ jacobi2_oneiter_spec; jacobi2_spec ].

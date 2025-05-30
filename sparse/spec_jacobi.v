Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import Iterative.jacobi_iteration_bound.
Import RelationPairs.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Require Import VSTlib.spec_malloc.
Require Import vcfloat.FPStdLib.
#[export] Declare Instance M: MallocAPD.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Require Import Iterative.sparse.spec_sparse.

Definition jacobi2_oneiter_spec :=
 DECLARE _jacobi2_oneiter
 WITH shA1: share, shA2: share, shb: share, shx: share, shy: share,
      A1p: val, A1: vector Tdouble, A2p: val, A2: matrix Tdouble, csr: csr_matrix Tdouble,
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      yp: val
 PRE [ tptr tdouble, tptr t_csr, tptr tdouble, tptr tdouble, tptr tdouble ]
    PROP(readable_share shA1; readable_share shA2; readable_share shb;
         csr_to_matrix csr A2;
             readable_share shx; writable_share shy;
             matrix_cols A2 (matrix_rows A2);
             matrix_rows A2 < Int.max_unsigned;
             Forall (Forall finite) A2; 
             Forall finite b; Forall finite x)
    PARAMS(A1p; A2p; bp; xp; yp)
    SEP (data_at shA1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           csr_rep shA2 csr A2p;
           data_at shb (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at shx (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at_ shy (tarray tdouble (matrix_rows A2)) yp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX s: ftype Tdouble,
    PROP( Forall2 feq y  (jacobi_iter A1 A2 b x); 
              feq s (norm2 (jacobi_residual A1 A2 b x)))
    RETURN(Vfloat s)
    SEP (data_at shA1 (tarray tdouble (matrix_rows A2)) (map Vfloat A1) A1p;
           csr_rep shA2 csr A2p;
           data_at shb (tarray tdouble (matrix_rows A2)) (map Vfloat b) bp;
           data_at shx (tarray tdouble (matrix_rows A2)) (map Vfloat x) xp;
           data_at shy (tarray tdouble (matrix_rows A2)) (map Vfloat y) yp).

Definition jacobi2_spec :=
 DECLARE _jacobi2
 WITH shA1: share, shA2: share, shb: share,
      A: matrix Tdouble, A1p: val, A2p: val,
      bp: val, b: vector Tdouble, xp: val, x: vector Tdouble, 
      acc: ftype Tdouble, maxiter: Z, gv: globals
 PRE [ tptr tdouble, tptr t_csr, tptr tdouble, tptr tdouble, tdouble, tuint ]
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
           csr_rep_abstract shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat x) xp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX s: ftype Tdouble,
    PROP(RelProd feq (Forall2 feq) (s,y) (jacobi A b x acc (Z.to_nat maxiter)))
    RETURN(Vfloat s)
    SEP (mem_mgr gv;
           data_at shA1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           csr_rep_abstract shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat y) xp).

Definition jacobi2_highspec :=
 DECLARE _jacobi2
 WITH shA1: share, shA2: share, shb: share,
      A: matrix Tdouble, A1p: val, A2p: val,
      bp: val, b: vector Tdouble, xp: val,
      acc: ftype Tdouble, maxiter: Z, gv: globals
 PRE [ tptr tdouble, tptr t_csr, tptr tdouble, tptr tdouble, tdouble, tuint ]
    PROP(readable_share shA1; readable_share shA2; readable_share shb;
             jacobi_preconditions A b acc (Z.to_nat (maxiter-1));
             0 < matrix_rows A < Int.max_unsigned;
             0 < maxiter <= Int.max_unsigned)
    PARAMS(A1p; A2p; bp; xp; Vfloat (BMULT acc acc); Vint (Int.repr maxiter)) GLOBALS(gv)
    SEP (mem_mgr gv;
           data_at shA1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           csr_rep_abstract shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat (Zrepeat (Zconst Tdouble 0) (matrix_rows A))) xp)
 POST [ tdouble ]
   EX y: vector Tdouble, EX s: ftype Tdouble,
    PROP(feq s (norm2 (jacobi_residual (diag_of_matrix A) (remove_diag A) b y));
             BCMP Lt true s (BMULT acc acc) = true)
    RETURN(Vfloat s)
    SEP (mem_mgr gv;
           data_at shA1 (tarray tdouble (matrix_rows A)) (map Vfloat (diag_of_matrix A)) A1p;
           csr_rep_abstract shA2 (remove_diag A) A2p;
           data_at shb (tarray tdouble (matrix_rows A)) (map Vfloat b) bp;
           data_at Ews (tarray tdouble (matrix_rows A)) (map Vfloat y) xp).

Definition JacobiASI : funspecs := [ jacobi2_oneiter_spec; jacobi2_spec ].


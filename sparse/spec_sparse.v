Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse sparse_model.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition t_csr := Tstruct _csr_matrix noattr.

Definition csr_rep (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
    EX v: val, EX ci: val, EX rp: val,
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.


Definition csr_rep_abstract (sh: share) (mval: matrix Tdouble) (p: val) : mpred :=
  EX csr, !!csr_to_matrix csr mval && csr_rep sh csr p.

Definition csr_matrix_rows_spec :=
 DECLARE _csr_matrix_rows
 WITH sh: share, m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble
 PRE [ tptr t_csr ]
    PROP (readable_share sh; matrix_rows mval < Int.max_unsigned; csr_to_matrix csr mval)
    PARAMS (m)
    SEP (csr_rep sh csr m)
 POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (matrix_rows mval)))
    SEP (csr_rep sh csr m).

Definition csr_row_vector_multiply_spec :=
 DECLARE _csr_row_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, i: Z
 PRE [ tptr t_csr, tptr tdouble, tuint ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             0 <= i < matrix_rows mval;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; Vint (Int.repr i))
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v)
 POST [ tdouble ]
   EX s: ftype Tdouble,
    PROP(feq s (dotprod (Znth i mval) vval)) 
    RETURN(Vfloat s)
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v).

Definition csr_matrix_vector_multiply_byrows_spec :=
 DECLARE _csr_matrix_vector_multiply_byrows
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition csr_matrix_vector_multiply_spec :=
 DECLARE _csr_matrix_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).


Definition t_coo := Tstruct _coo_matrix noattr.

Definition coo_rep (sh: share) (coo: coo_matrix Tdouble) (p: val) : mpred :=
 EX (r c n maxn: Z) (rp cp vp : val), 
 !! (0 <= n <= maxn /\ maxn <= Int.max_signed /\ 0 <= r <= Int.max_signed /\
       0 <= c <= Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr n), (Vint (Int.repr maxn), 
                     (Vint (Int.repr r), (Vint (Int.repr c)))))))) p *
  data_at sh (tarray tint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) rp *
  data_at sh (tarray tint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) cp *
  data_at sh (tarray tint maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-n)) vp.

Definition SparseASI : funspecs := [ 
   csr_matrix_rows_spec;
   csr_row_vector_multiply_spec;
   csr_matrix_vector_multiply_byrows_spec;
   csr_matrix_vector_multiply_spec ].

Lemma BFMA_eq:
   forall H H0 x y z,
  Binary.Bfma (fprec Tdouble) (femax Tdouble) H H0
    (@FPCompCert.FMA_NAN.fma_nan_pl 
          (FPCore.fprec FPCore.Tdouble) 
          (FPCore.femax FPCore.Tdouble) (FPCore.fprec_gt_one _)) 
     BinarySingleNaN.mode_NE x y z = 
  BFMA x y z.
Proof.
intros.
 unfold BFMA.
 f_equal; try apply proof_irr.
 simpl. f_equal. apply proof_irr.
Qed.


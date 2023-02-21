From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
From mathcomp Require Import all_ssreflect.
Require Import floatlib.
Require Import common float_acc_lems.
Local Open Scope R.
Section WITHNANS.
Context {NANS: Nans}. 

Lemma Bminus_bplus_opp_equiv {ty} (x y : ftype ty):
  finite (BPLUS x (BOPP y)) ->
  BMINUS x y = BPLUS x (BOPP y).
Proof.
intros.
rewrite finite_is_finite in H.
destruct x, y; (unfold BMINUS, BPLUS, BOPP, BINOP, Bminus, Bplus in *; simpl in *; auto;
  try destruct (Bool.eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto);
  (destruct (BinarySingleNaN.binary_normalize 
    (fprec ty) (femax ty) (fprec_gt_0 ty)
    (fprec_lt_femax ty) BinarySingleNaN.mode_NE
    (BinarySingleNaN.Fplus_naive s m e 
       (~~ s0) m0 e1 (Z.min e e1)) 
    (Z.min e e1) false); simpl;auto;
  by destruct s,s0;simpl in *; auto).
Qed.

Lemma BPLUS_le_rel
  {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (FIN: finite (BPLUS x y)),
  Rabs (FT2R (BPLUS x y )) <= (Rabs (FT2R x) + Rabs (FT2R y)) * (1+ default_rel t).
Proof.
intros.
pose proof (BPLUS_accurate' t x y FIN).
destruct H as [delta H].
destruct H as [Hd Heq].
rewrite Heq.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; try apply Rabs_triang.
apply Rle_trans with (Rabs 1 + Rabs delta).
+ apply Rabs_triang.
+ rewrite Rabs_R1. apply Rplus_le_compat_l.
  apply Hd.
Qed.

Lemma BPLUS_error_le_rel
  {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (FIN: finite (BPLUS x y)),
  Rabs (FT2R (BPLUS x y ) - (FT2R x + FT2R y)) <= (Rabs (FT2R x) + Rabs (FT2R y)) * (default_rel t).
Proof.
intros.
pose proof (BPLUS_accurate' t x y FIN).
destruct H as [delta H].
destruct H as [Hd Heq].
rewrite Heq.
assert (((FT2R x + FT2R y) * (1 + delta) - (FT2R x + FT2R y)) =
        ((FT2R x + FT2R y) * delta)).
{ nra. } rewrite H.
rewrite Rabs_mult.
apply Rmult_le_compat; try by apply Rabs_pos.
+ apply Rabs_triang.
+ apply Hd.
Qed.

Lemma BPLUS_error_le_rel'
  {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (FIN: finite (BPLUS x y)),
  Rabs (FT2R (BPLUS x y ) - (FT2R x + FT2R y)) <= (Rabs (FT2R x + FT2R y)) * (default_rel t).
Proof.
intros.
pose proof (BPLUS_accurate' t x y FIN).
destruct H as [delta H].
destruct H as [Hd Heq].
rewrite Heq.
assert (((FT2R x + FT2R y) * (1 + delta) - (FT2R x + FT2R y)) =
        ((FT2R x + FT2R y) * delta)).
{ nra. } rewrite H.
rewrite Rabs_mult.
apply Rmult_le_compat; try by apply Rabs_pos.
+ nra.
+ apply Hd.
Qed.

Lemma Bplus_no_ov_finite : 
   forall (t: type) 
             (x: ftype t) (FINx: finite x) 
             y (FINy: finite y) 
          (FIN: Bplus_no_overflow t (FT2R x) (FT2R y)), 
          finite (BPLUS x y).
Proof.
intros.
rewrite finite_is_finite in FINx. 
rewrite finite_is_finite in FINy. 
rewrite finite_is_finite.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) 
                      BinarySingleNaN.mode_NE x y FINx FINy ).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x + FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
{ destruct H as ( _ & Hyp & _).
fold (@BPLUS _ t) in Hyp; auto. }
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma BMULT_finite_e {t : type}: 
  forall (x y : ftype t), 
  finite (BMULT x y) -> finite x /\finite y.
Proof.
intros.
rewrite finite_is_finite in H.
rewrite !finite_is_finite. 
destruct x, y; (unfold BMULT, BINOP, Bmult in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto).
Qed.

Lemma Bminus_bplus_opp_implies {ty} (x y : ftype ty):
  finite (BMINUS x y) -> 
  finite (BPLUS x (BOPP y)).
Proof.
intros.
rewrite finite_is_finite in H.
rewrite !finite_is_finite. 
destruct x, y; (unfold BMINUS, BPLUS, BOPP, BINOP, Bplus, Bminus, Bopp in *; simpl in *; auto;
try destruct (Bool.eqb s (~~ s0)); simpl in * ;auto; try by []; 
try unfold is_finite in H1; simpl in *; auto);
(destruct (BinarySingleNaN.binary_normalize 
    (fprec ty) (femax ty) (fprec_gt_0 ty)
    (fprec_lt_femax ty) BinarySingleNaN.mode_NE
    (BinarySingleNaN.Fplus_naive s m e 
       (~~ s0) m0 e1 (Z.min e e1)) 
    (Z.min e e1) false); simpl;auto;
  by destruct s,s0;simpl in *; auto).
Qed.

Lemma Bplus_bminus_opp_implies {ty} (x y : ftype ty): 
  finite (BPLUS x (BOPP y)) ->
  finite (BMINUS x y).
Proof.
intros.
rewrite finite_is_finite in H.
rewrite finite_is_finite. 
destruct x, y; (unfold BMINUS, BPLUS, BOPP, BINOP, Bplus, Bminus, Bopp in *; simpl in *; auto;
try destruct (Bool.eqb s (~~ s0)); simpl in * ;auto; try by []; 
try unfold is_finite in H1; simpl in *; auto);
(destruct (BinarySingleNaN.binary_normalize 
    (fprec ty) (femax ty) (fprec_gt_0 ty)
    (fprec_lt_femax ty) BinarySingleNaN.mode_NE
    (BinarySingleNaN.Fplus_naive s m e 
       (~~ s0) m0 e1 (Z.min e e1)) 
    (Z.min e e1) false); simpl;auto;
  by destruct s,s0;simpl in *; auto).
Qed.

Lemma BPLUS_finite_e {t : type}: 
  forall (x y : ftype t), 
  finite (BPLUS x y) -> finite x /\finite y.
Proof.
intros.
rewrite finite_is_finite in H.
rewrite !finite_is_finite. 
destruct x, y; (unfold BPLUS, BINOP, Bplus, is_finite in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto);
  by destruct s,s0;simpl in *; auto.
Qed.

Lemma BMULT_no_overflow_is_finite {NAN: Nans} (t : type): 
  forall (x y : ftype t) 
  (Hx : finite x)
  (Hy : finite y)
  (Hnov: Bmult_no_overflow t (FT2R x) (FT2R y)),
   finite (BMULT x y).
Proof.
intros.
rewrite finite_is_finite in Hx.
rewrite finite_is_finite in Hy.
rewrite finite_is_finite. 
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
unfold Bmult_no_overflow in Hnov.
unfold rounded in Hnov.
apply Rlt_bool_true in Hnov.
rewrite Hnov in H0.
destruct H0 as [H01 [H02 H03]].
rewrite H02. by apply /andP.
Qed.

Lemma BPLUS_no_overflow_is_finite {NAN: Nans} (t : type): 
  forall (x y : ftype t) 
  (Hx : finite x)
  (Hy : finite y)
  (Hnov: Bplus_no_overflow t (FT2R x) (FT2R y)),
   finite (BPLUS x y).
  
Proof.
intros.
rewrite finite_is_finite in Hx.
rewrite finite_is_finite in Hy.
rewrite finite_is_finite. 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
unfold Bplus_no_overflow in Hnov.
unfold rounded in Hnov.
apply Rlt_bool_true in Hnov.
rewrite Hnov in H0. specialize (H0 Hx Hy).
destruct H0 as [H01 [H02 H03]].
by rewrite H02.
Qed.

Definition Bdiv_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs (rounded t  (x / y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma finite_Binv_no_overflow {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (HFINb : finite (BDIV (Zconst t 1) y)),
  finite y ->
  Bdiv_no_overflow t (FT2R (Zconst t 1)) (FT2R y).
Proof.
intros.
assert (FT2R y <> 0).
{ by apply BDIV_FT2R_sep_zero. }
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R (Zconst t 1) / FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H1; red.
unfold rounded, FT2R  in H1.
pose proof (Binary.Bdiv_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (div_nan t) BinarySingleNaN.mode_NE (Zconst t 1) y) as
  H2.
specialize (H2 H0).
simpl in H2; simpl in H1;
rewrite H1 in H2.  unfold BDIV, BINOP in HFINb.
destruct ((Binary.Bdiv (fprec t) (femax t) (fprec_gt_0 t) 
             (fprec_lt_femax t) (div_nan t) BinarySingleNaN.mode_NE (Zconst t 1) y));
simpl;  try discriminate; contradiction. 
Qed.

Lemma Binv_accurate' {NAN: Nans}: 
   forall (t: type) y 
  (FIN: Bdiv_no_overflow t (FT2R (Zconst t 1)) (FT2R y)), 
  FT2R y <> 0 ->
  exists delta, exists epsilon,
   (delta * epsilon = 0) /\
   (Rabs delta <= default_rel t) /\
   (Rabs epsilon <= default_abs t) /\ 
   (FT2R (BDIV (Zconst t 1) y) = (FT2R (Zconst t 1) / FT2R y) * (1+delta) + epsilon).
Proof.
intros.
pose proof (Binary.Bdiv_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (div_nan t) BinarySingleNaN.mode_NE (Zconst t 1) y).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H0.
specialize (H0 H).
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R (Zconst t 1) / FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H1.
destruct H0 as [? _].
rewrite H0.
apply generic_round_property.
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma Binv_accurate {NAN: Nans}: 
   forall (t: type) y 
  (FIN: finite (BDIV (Zconst t 1) y))
  (FINy : finite y) , 
  exists delta, exists epsilon,
   (delta * epsilon = 0) /\
   (Rabs delta <= default_rel t) /\
   (Rabs epsilon <= default_abs t) /\ 
   (FT2R (BDIV (Zconst t 1) y) = (FT2R (Zconst t 1) / FT2R y) * (1+delta) + epsilon).
Proof.
intros.
pose proof (@BDIV_FT2R_sep_zero _ t y FIN FINy).
by apply Binv_accurate'; try apply finite_Binv_no_overflow .
Qed.

End WITHNANS.
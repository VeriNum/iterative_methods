From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
From mathcomp Require Import all_ssreflect.
Require Import floatlib.
Require Import common float_acc_lems.

Section WITHNANS.
Context {NANS: Nans}. 


Lemma bmult_overflow_implies {t : type}: 
  forall x y , 
  Binary.is_finite _ _ (BMULT t x y) = true ->
  is_finite _ _ x = true /\
  is_finite _ _ y = true.
Proof.
intros.
destruct x, y; (unfold BMULT, BINOP, Bmult in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto).
Qed.


Lemma Bminus_bplus_opp_implies {ty} (x y : ftype ty):
  is_finite _ _ (BMINUS ty x y) -> 
  is_finite _ _ (BPLUS ty x (BOPP ty y)).
Proof.
intros.
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


Lemma bplus_overflow_implies {t : type}: 
  forall x y , 
  Binary.is_finite _ _ (BPLUS t x y) = true ->
  is_finite _ _ x = true /\
  is_finite _ _ y = true.
Proof.
intros.
destruct x, y; (unfold BPLUS, BINOP, Bplus, is_finite in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto);
  by destruct s,s0;simpl in *; auto.
Qed.


Lemma bfma_overflow_implies {t : type}: 
  forall x y z, 
  Binary.is_finite _ _ (@BFMA _ t x y z) = true ->
  is_finite _ _ x = true /\
  is_finite _ _ y = true /\
  is_finite _ _ z = true.
Proof.
intros.
destruct x, y, z; (unfold BFMA, BINOP, Bfma, is_finite in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto);
  by destruct s,s0,s1;simpl in *; auto.
Qed.

Definition Bdiv_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs (rounded t  (x / y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma is_finite_Binv_no_overflow {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (HFINb : Binary.is_finite (fprec t) (femax t) (BDIV t (Zconst t 1) y) = true),
  is_finite _ _ y = true ->
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
simpl;  try discriminate. 
Qed.




Lemma Binv_accurate' {NAN: Nans}: 
   forall (t: type) y 
  (FIN: Bdiv_no_overflow t (FT2R (Zconst t 1)) (FT2R y)), 
  FT2R y <> 0 ->
  exists delta, exists epsilon,
   (delta * epsilon = 0) /\
   (Rabs delta <= default_rel t) /\
   (Rabs epsilon <= default_abs t) /\ 
   (FT2R (BDIV t (Zconst t 1) y) = (FT2R (Zconst t 1) / FT2R y) * (1+delta) + epsilon).
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
  (FIN: Binary.is_finite (fprec t) (femax t) (BDIV t (Zconst t 1) y) = true )
  (FINy : is_finite _ _ y = true) , 
  exists delta, exists epsilon,
   (delta * epsilon = 0) /\
   (Rabs delta <= default_rel t) /\
   (Rabs epsilon <= default_abs t) /\ 
   (FT2R (BDIV t (Zconst t 1) y) = (FT2R (Zconst t 1) / FT2R y) * (1+delta) + epsilon).
Proof.
intros.
pose proof (@BDIV_FT2R_sep_zero _ t y FIN FINy).
by apply Binv_accurate'; try apply is_finite_Binv_no_overflow .
Qed.

End WITHNANS.
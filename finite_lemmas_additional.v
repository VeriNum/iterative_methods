From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
From mathcomp Require Import all_ssreflect.
Require Import floatlib.


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


End WITHNANS.
(* This file contains lemmas regarding the accuracy of floating point 
  operations such as BPLUS, BFMA, and BMULT. *)

Require Import vcfloat.VCFloat vcfloat.FPStdLib.
From vcfloat Require Import IEEE754_extra.
Require Import common op_defs.
Require Import ZArith.
Local Open Scope R.

Section NAN.

Definition fma_no_overflow (t: type) (x y z: R) : Prop :=
  (Rabs (rounded t  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.


Definition Bmult_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs (rounded t  (x * y)) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma generic_round_property:
  forall (t: type) (x: R),
exists delta epsilon : R,
   delta * epsilon = 0 /\
  (Rabs delta <= default_rel t)%R /\
  (Rabs epsilon <= default_abs t)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
split; [ | split]; auto.
Qed.

Lemma fma_accurate {NAN: Nans} : 
   forall (t: type) 
             (x: ftype t) (FINx: finite x) 
             y (FINy: finite y) 
             z (FINz: finite z)
          (FIN: fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
rewrite finite_is_finite in FINx.
rewrite finite_is_finite in FINy.
rewrite finite_is_finite in FINz.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z FINx FINy FINz).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y + FT2R z)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
fold (@BFMA NAN t) in H.
rewrite H.
apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma is_finite_fma_no_overflow {NAN: Nans} (t : type) :
  forall (x y z : ftype t)
  (HFINb : finite (BFMA x y z)),
  fma_no_overflow t (FT2R x) (FT2R y) (FT2R z).
Proof.
intros.
red. set (ov:= bpow Zaux.radix2 (femax t)).
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
destruct (BFMA_finite_e _ _ _ HFINb) as (A & B & C).
unfold rounded, FT2R, ov in H.
rewrite finite_is_finite in *.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE x y z A B C) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0. clear H. fold (@BFMA NAN t) in H0.
destruct (BFMA x y z); try discriminate.
Qed.

Lemma fma_accurate' {NAN: Nans} : 
   forall (t: type) (x y z : ftype t)
          (FIN: finite (BFMA x y z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
destruct (BFMA_finite_e _ _ _ FIN) as (A & B & C).
apply fma_accurate; auto.
apply is_finite_fma_no_overflow; auto.
Qed.

Lemma BMULT_accurate {NAN: Nans}: 
   forall (t: type) (x y: ftype t) (FIN: Bmult_no_overflow t (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (mult_nan t) BinarySingleNaN.mode_NE x y).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
destruct H as [? _].
unfold BMULT, BINOP.
rewrite H.
apply generic_round_property.
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma finite_BMULT_no_overflow {NAN: Nans} (t : type) :
  forall (x y : ftype t) 
  (HFINb :finite (BMULT x y)),
  Bmult_no_overflow t (FT2R x) (FT2R y).
Proof.
intros.
rewrite finite_is_finite in HFINb.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded, FT2R  in H.
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0.  unfold BMULT, BINOP in HFINb.
destruct ((Binary.Bmult (fprec t) (femax t) (fprec_gt_0 t) 
             (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y));
simpl;  try discriminate.
Qed.

Lemma BMULT_accurate' {NAN: Nans}: 
  forall (t: type) 
  (x y : ftype t) 
  (FIN: finite (BMULT x y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros. 
pose proof BMULT_accurate t x y (finite_BMULT_no_overflow t x y FIN); auto.
Qed.


Definition Bplus_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x + y )) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma BPLUS_neg_zero {NAN: Nans} (t : type) (a : ftype t) :
  finite a ->
  BPLUS a neg_zero = a.
Proof.
destruct a; try contradiction; unfold neg_zero; simpl; auto.
destruct s; auto.
Qed.

Lemma BPLUS_accurate {NAN: Nans} (t : type) :
 forall   (x: ftype t) (FINx: finite x) 
             y (FINy: finite y) 
          (FIN: Bplus_no_overflow t (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
rewrite finite_is_finite in FINx, FINy. 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE x y FINx FINy).
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
-
destruct H as [? _].
unfold BPLUS, BINOP.
rewrite H. 
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ) by (apply Binary.generic_format_B2R).
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R y) ) by (apply Binary.generic_format_B2R).
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (FT2R y) A B.
unfold Relative.u_ro in H1. fold (default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
 
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x + FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x + FT2R y)) by auto.
rewrite <- H1 in Hd'. clear H1. rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (default_rel t * 1); try nra.
-
red in FIN.
Lra.lra.
Qed.

Lemma BPLUS_finite_e {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (FIN: finite (BPLUS x y)), 
  finite x /\ finite y.
Proof.
intros.
destruct x,y; try contradiction; simpl; auto.
destruct s,s0; simpl in FIN; auto.
Qed.

Lemma finite_sum_no_overflow {NAN: Nans} (t : type) :
  forall (x y: ftype t)
  (HFINb : finite (BPLUS x y)),
  Bplus_no_overflow t (FT2R x) (FT2R y).
Proof.
intros.
 destruct (BPLUS_finite_e _ _ _ HFINb) as [A B].
rewrite finite_is_finite in HFINb.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x + FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
unfold rounded, FT2R in H.
rewrite finite_is_finite in *.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE x y A B) as
  H0;
rewrite H in H0;
destruct H0 as ( C & _).
unfold BPLUS, BINOP in HFINb.
destruct ((Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan t) BinarySingleNaN.mode_NE x y));
simpl; try discriminate.
Qed.

Lemma BPLUS_accurate' {NAN: Nans} (t : type) :
  forall (x y : ftype t)
  (FIN: finite (BPLUS x y)), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
destruct (BPLUS_finite_e _ _ _ FIN) as [A B].
apply BPLUS_accurate; auto.
apply finite_sum_no_overflow; auto.
Qed.

Lemma BDIV_sep_zero' {NAN: Nans} (t : type) :
  forall (f1 f2 : ftype t)
  (Hfin: finite (BDIV f1 f2))
  (Hfin1: Binary.is_finite_strict _ _ f1 = true)
  (Hfin2: finite f2),
  Binary.is_finite_strict _ _ f2 = true.
Proof.
intros ? ?;
destruct f2; destruct f1; simpl; try discriminate; auto.
Qed.

Lemma fprec_lb {NAN: Nans} (t : type) :
  (2 <= fprec t)%Z.
Proof. pose proof ( fprec_gt_one t); lia. Qed.

Lemma femax_lb {NAN: Nans} (t : type) :
  (3 <= femax t)%Z.
Proof. 
pose proof fprec_lb t;
pose proof fprec_lt_femax t; lia. 
Qed.

Lemma femax_minus_fprec (t: type): 
  (0 < (femax t - fprec t))%Z.
Proof.
pose proof fprec_lt_femax t; lia. 
Qed.

Lemma in_fprec_bound1 {NAN: Nans} (t : type) :
 (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z.
Proof.
split. eapply Z.le_trans with (-2 ^ 2)%Z; [|lia].
apply Z.opp_le_mono; rewrite !Z.opp_involutive.
apply Z.pow_le_mono_r; [lia |apply fprec_lb ].
eapply Z.le_trans with (2 ^ 2)%Z; [lia|].
apply Z.pow_le_mono_r; [lia |apply fprec_lb ].
Qed.

Lemma in_fprec_bound0 {NAN: Nans} (t : type) :
 (- 2 ^ fprec t <= 0 <= 2 ^ fprec t)%Z.
Proof.
split. eapply Z.le_trans with (-2 ^ 2)%Z; [|lia].
apply Z.opp_le_mono; rewrite !Z.opp_involutive.
apply Z.pow_le_mono_r; [lia |apply fprec_lb ].
eapply Z.le_trans with (2 ^ 2)%Z; [lia|].
apply Z.pow_le_mono_r; [lia |apply fprec_lb ].
Qed.

Lemma Bone_strict_finite {NAN: Nans} (t : type) :
  Binary.is_finite_strict _ _ (Zconst t 1) = true.
Proof.
destruct 
  (BofZ_exact (fprec t) (femax t) (Pos2Z.is_pos (fprecp t)) (fprec_lt_femax t) 1 (in_fprec_bound1 t)) 
  as ( A & H & _); fold (Zconst t 1) in *.
destruct (Zconst t 1);
  simpl; simpl in A; try discriminate; auto.
nra.
Qed.

Lemma BDIV_sep_zero1 {NAN: Nans} (t : type) :
  forall (f1 : ftype t)
  (Hfin: finite (BDIV (Zconst t 1) f1))
  (Hfin1: finite f1),
  f1 <> (Zconst t 0).
Proof.
intros. intros HF.
pose proof BDIV_sep_zero' t (Zconst t 1) f1 Hfin (Bone_strict_finite t) Hfin1.
destruct f1; try discriminate; auto.
Qed.

Lemma BDIV_sep_zero2 {NAN: Nans} (t : type) :
  forall (f1 : ftype t)
  (Hfin: finite (BDIV (Zconst t 1) f1))
  (Hfin1: finite f1),
  f1 <> (neg_zero).
Proof.
intros. intros HF.
pose proof BDIV_sep_zero' t (Zconst t 1) f1 Hfin (Bone_strict_finite t) Hfin1.
destruct f1; try discriminate; auto.
Qed.

Lemma BDIV_FT2R_sep_zero {NAN: Nans} (t : type) :
  forall (f1 : ftype t)
  (Hfin: finite (BDIV (Zconst t 1) f1))
  (Hfin1: finite f1),
  FT2R f1 <> 0.
Proof.
intros. intros HF.
pose proof BDIV_sep_zero1 t f1 Hfin Hfin1 as H0.
pose proof BDIV_sep_zero2 t f1 Hfin Hfin1 as H1.
pose proof BDIV_sep_zero' t (Zconst t 1) f1 Hfin (Bone_strict_finite t) Hfin1 as HFINx.
rewrite finite_is_finite in Hfin.
rewrite finite_is_finite in Hfin1.
pose proof Binary.B2R_Bsign_inj (fprec t) (femax t) f1 neg_zero Hfin1 (eq_refl _) as HA.
pose proof Binary.B2R_Bsign_inj (fprec t) (femax t) f1 (Zconst t 0) Hfin1 (eq_refl _) as HB.
destruct f1; try discriminate; auto.
destruct s; try discriminate; auto.
Qed. 

Lemma is_finite_fma_no_overflow' {NAN: Nans} (t : type) :
  forall (x y z: ftype t)
  (Hfinx: finite x)
  (Hfiny: finite y)
  (Hfinz: finite z)
  (Hov : fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)),
 finite (BFMA x y z).
Proof.
intros.
rewrite finite_is_finite in Hfinx, Hfiny, Hfinz|-*.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z Hfinx Hfiny Hfinz).
unfold fma_no_overflow, FT2R, rounded in Hov;
apply Rlt_bool_true in Hov.
cbv zeta in H.
rewrite Hov in H; simpl in H; destruct H as (_ & B & _); simpl; auto.
Qed.

Lemma finite_BOPP: forall {NAN: Nans} (t: type) (x: ftype t),
   finite (BOPP x) <-> finite x.
Proof.
intros.
unfold BOPP.
rewrite !finite_is_finite, Binary.is_finite_Bopp.
tauto.
Qed.

End NAN.
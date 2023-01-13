Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.
Require Import fma_dot_acc.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

Definition fmax (t: type) := bpow Zaux.radix2 (femax t).

Definition F' (t: type) := 
    fmax t * (1 -  2 * default_rel t).


Lemma fma_no_ov_is_finite : 
   forall (t: type) 
             x (FINx: Binary.is_finite (fprec t) (femax t) x = true) 
             y (FINy: Binary.is_finite (fprec t) (femax t) y = true) 
             z (FINz: Binary.is_finite (fprec t) (femax t) z = true)
          (FIN: fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)), 
          Binary.is_finite (fprec t) (femax t) (BFMA x y z) = true.
Proof.
intros.
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
{ destruct H as ( _ & Hyp & _).
fold (@BFMA NAN t) in Hyp; auto. }
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.


Lemma fma_is_finite: 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> forall fp,
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite (fprec t) (femax t) (fst xy) = true /\ 
      Binary.is_finite _ _ (snd xy) = true /\
      let n:= (length v1) in 
      Rabs (FT2R (fst (xy))) <= sqrt (F' t / (INR n * (1 + default_rel t)^n) - default_abs t) /\
      Rabs (FT2R (snd (xy))) <= sqrt (F' t / (INR n * (1 + default_rel t)^n) - default_abs t)) -> 
  Binary.is_finite (fprec t) (femax t) fp = true. 
Proof.
intros t v1 v2 Hlen.
assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).
rewrite <- H. clear H; revert Hlen.
induction (List.combine v1 v2).
{ intros; simpl.
 inversion H. subst; simpl; auto. }
intros Hlen fp  Hfp   Hin .
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{ subst.
inversion Hfp. inversion H2. subst.
destruct a. simpl. simpl in Hfp.
assert (hyp: In (f, f0) [(f, f0)]) by (simpl;auto).
specialize (Hin (f,f0) hyp); simpl in Hin.
destruct Hin as (A & B & C1 & C2).
apply fma_no_ov_is_finite; auto.
unfold neg_zero; simpl; auto.
unfold fma_no_overflow, rounded.
pose proof (generic_round_property t (FT2R f * FT2R f0)).
rewrite Rplus_0_r.
destruct H as (d & e & Hmul  & Hd & He & H).
rewrite H.
clear IHl H2 Hfp hyp H.
eapply Rle_lt_trans; [apply Rabs_triang|].
rewrite !Rabs_mult.
eapply Rle_lt_trans.
eapply Rplus_le_compat; [| apply He].
eapply Rmult_le_compat; try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
eapply Rmult_le_compat; try apply Rabs_pos;
try apply C1; try apply C2.
eapply Rle_trans; [apply Rabs_triang| apply Rplus_le_compat_l; 
  apply Hd].
rewrite Rabs_R1; 
rewrite !Rmult_1_l;
rewrite !Rmult_1_r.
rewrite sqrt_sqrt.
replace (F' t / (1 + default_rel t)) with 
  (F' t * / (1 + default_rel t)) by nra.
rewrite Rmult_minus_distr_r.
rewrite Rmult_assoc.
rewrite Rmult_comm.
replace (/ (1 + default_rel t) * (1 + default_rel t))
  with ((1 + default_rel t) * / (1 + default_rel t)) by nra.
rewrite Rinv_r_simpl_r.
unfold F'.
rewrite Rmult_minus_distr_l.
rewrite Rmult_1_r.
replace (fmax t - fmax t * (2 * default_rel t) -
default_abs t * (1 + default_rel t) + default_abs t)
with (fmax t + default_abs t - fmax t * (2 * default_rel t) -
default_abs t * (1 + default_rel t) ) by nra.
apply Rcomplements.Rlt_minus_l. 
apply Rcomplements.Rlt_minus_l. 
unfold fmax. rewrite Rplus_assoc.
apply Rplus_le_lt_compat; try nra.
rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
eapply Rle_lt_trans with (default_abs t + 0); try nra.
rewrite Rplus_assoc.
apply Rplus_le_lt_compat; try nra.
apply Rplus_lt_0_compat.
apply Rmult_lt_0_compat; 
  [apply default_abs_gt_0 |apply default_rel_gt_0].
apply Rmult_lt_0_compat; [apply bpow_gt_0 |
  apply Rmult_lt_0_compat; [ try nra |
     apply default_rel_gt_0 ]].
apply tech_Rplus; try nra; apply default_rel_gt_0.
apply Rle_0_minus.  
apply Generic_proof.Rdiv_le_mult_pos.
eapply Rlt_trans with 1; try nra.
admit.
unfold F'. 

Admitted.


End NAN.
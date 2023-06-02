(*This file contains two main theorems: forward and mixed error bounds for 
  the fused muliply add dot product of two floating point lists; 
  the functional model for the fma dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat vcfloat.FPLib.
Require Import List.
Import ListNotations.
Require Import common dotprod_model sum_model float_acc_lems list_lemmas.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.


(* forward error bounds *)
Lemma fma_dotprod_forward_error:
  forall (t: type) `{STD: is_standard t} (v1 v2: list (ftype t))
  (Hlen: length v1 = length v2)
  (fp : ftype t) (rp rp_abs : R)
  (Hfp: fma_dot_prod_rel (List.combine v1 v2) fp)
  (Hrp: R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp)
  (Hra: R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs)
  (Hfin: finite fp),
  Rabs (FT2R fp - rp) <=  g t (length v1) * Rabs rp_abs + g1 t (length v1) (length v1 - 1).
Proof.
intros ? ? ? ? ?.
rewrite (combine_map _ _ FT2R FR2).
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
rewrite <- H. clear H; revert Hlen.
induction (List.combine v1 v2).
{
intros;
inversion Hrp;
inversion Hfp;
inversion Hra;
subst.
unfold Zconst. rewrite FT2R_ftype_of_float. simpl.
unfold g, g1; simpl;
rewrite Rminus_eq_0;
rewrite Rabs_R0.
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof fma_accurate' t (fst a) (snd a) (Zconst t 0) Hfin as Hacc.
destruct Hacc as (e & d & Hz & He & Hd & A). rewrite A; clear A.
inversion Hra; inversion H3; subst.
unfold g1, g; simpl.
unfold Zconst; rewrite FT2R_ftype_of_float; simpl.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + default_rel t - 1) with (default_rel t) by nra.
field_simplify_Rabs. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
rewrite Rmult_plus_distr_l. rewrite Rmult_comm.
apply Rplus_le_compat; try nra.
  apply Rmult_le_compat; try apply Rabs_pos; try apply Rle_refl;
  try apply Rabs_pos; auto.
rewrite <- Rabs_mult; rewrite Rabs_Rabsolu; apply Req_le; nra.
simpl in Hrp; auto.
}
(* non-empty l *)
intros; inversion Hfp;
inversion Hrp; inversion Hra; subst.
(destruct (BFMA_finite_e _ _ _ Hfin) as (A & B & C)).
(* IHl *)
specialize (IHl Hlen s s0 s1 H3 H7 H11 C).
pose proof (fma_accurate' t (fst a) (snd a) s Hfin) as Hplus.
destruct Hplus as (d' & e'& Hz & Hd'& He'& Hplus); rewrite Hplus;
  clear Hplus.
(* algebra *)
destruct a; cbv [ FR2 Rabsp fst snd].
set (D:= default_rel t);
set (E:= default_abs t).
simpl.
set (n:= length l).
field_simplify_Rabs.
replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0) with
   (d' * (FT2R f * FT2R f0) + d' * FT2R s + (FT2R s - s0) + e') by nra.
eapply Rle_trans;
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans;
  [  apply Rplus_le_compat_r | ].
apply Rplus_le_compat_r.
apply Rabs_triang.
eapply Rle_trans;
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l | ].
apply IHl.
eapply Rle_trans;
  [apply Rplus_le_compat; [apply Rplus_le_compat_r| apply He' ] | ].
apply Rplus_le_compat.
rewrite Rabs_mult;
apply Rmult_le_compat_r; try apply Rabs_pos;
apply Hd'.
rewrite Rabs_mult;
apply Rmult_le_compat; try apply Rabs_pos.
apply Hd'.
apply Rabs_le_minus in IHl.
assert (Hs: Rabs (FT2R s) <=
      g t (length l) * Rabs s1 + g1 t (length l) (length l - 1) + Rabs s1).
{ eapply Rle_trans. apply IHl. apply Rplus_le_compat_l.
apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto.
}
apply Hs.
fold E D n.
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0) + s1)) with
(Rabs ( FT2R f *  FT2R f0) +  Rabs s1).
set (F:=Rabs (FT2R f * FT2R f0)).
set (Y:=Rabs s1).
rewrite !Rmult_plus_distr_l.
replace (D * F + (D * (g t n * Y) + D * g1 t n (n - 1) + D * Y) +
(g t n * Y + g1 t n (n - 1)) + E) with
(D * F + ((1 + D) * g t n * Y + D * Y) + g1 t n (n - 1) * (1 + D) + E) by nra.
unfold D.
rewrite one_plus_d_mul_g. rewrite one_plus_d_mul_g1.
rewrite Rplus_assoc.
apply Rplus_le_compat.
apply Rplus_le_compat.
apply Rmult_le_compat_r.
unfold F; apply Rabs_pos.
apply d_le_g_1; lia.
apply Rmult_le_compat_r.
unfold Y; apply Rabs_pos.
apply Req_le; f_equal; auto; lia.
unfold E; rewrite Nat.sub_0_r. apply plus_e_g1_le.
unfold n; apply length_not_empty in H; auto.
rewrite !Rabs_mult.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1) at 2; auto.
symmetry.
rewrite Rabs_pos_eq; auto. 
apply Rplus_le_le_0_compat; try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
unfold FR2; simpl; auto.
Qed.


Lemma fma_dotprod_forward_error_2:
  forall (t: type) `{STD: is_standard t} (v1 v2: list (ftype t))
  (Hlen1: (1 <= length v1)%nat)
  (Hlen2: length v1 = length v2)
  (Hin: (forall xy, In xy (List.combine v1 v2) ->  finite (fst xy) /\  finite (snd xy)))
  (Hfin: finite (fma_dotprod t v1 v2)),
  let prods := map (uncurry Rmult) (List.combine (map FT2R v1) (map FT2R v2)) in
  let abs_prods := map (uncurry Rmult) (List.combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) in  
  Rabs (FT2R (fma_dotprod t v1 v2) - sum_fold prods) <= g t (length v1) * sum_fold abs_prods + g1 t (length v1) (length v1 - 1).
Proof.
intros.
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
rewrite <- rev_length in Hlen1.
pose proof fma_dotprod_forward_error t (rev v1) (rev v2) Hlenr
  (fma_dotprod t v1 v2) (sum_fold prods) (sum_fold abs_prods) as H2.
rewrite rev_length in H2.
rewrite combine_rev in H2; auto.
assert (Hrel:      R_dot_prod_rel
       (combine (map Rabs (map FT2R (rev v1))) (map Rabs (map FT2R (rev v2))))
       (sum_fold abs_prods) ).
{ rewrite !map_rev.
rewrite combine_rev.
subst abs_prods.
rewrite (combine_map _ _ Rabs Rabsp); try simpl; auto.
rewrite (combine_map _ _ FT2R FR2); try simpl; auto.
pose proof R_dot_prod_rel_fold_right_Rabs t v1 v2 as HRrel; simpl in HRrel; auto.
rewrite !map_length; auto. }
replace (Rabs (sum_fold abs_prods)) with (sum_fold abs_prods) in H2.
apply H2; clear H2; auto.
{ apply (fma_dot_prod_rel_fold_right t v1 v2). }
{ rewrite !map_rev.
rewrite combine_rev.
subst prods.
rewrite (combine_map _ _ FT2R FR2); try simpl; auto.
pose proof R_dot_prod_rel_fold_right t v1 v2 as HRrel; simpl in HRrel; auto.
rewrite !map_length; auto. }
symmetry.
apply (R_dot_prod_rel_Rabs_eq (combine (map FT2R (rev v1)) (map FT2R (rev v2))) (sum_fold abs_prods)).
rewrite <- (combine_map R R Rabs Rabsp); auto.
Qed.

Lemma rev_combine :
  forall {A B : Type} (l1 : list A) (l2 : list B),
     length l1 = length l2 ->
     rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
induction l1; destruct l2; intros; inversion H; clear H; subst; auto.
simpl.
rewrite (IHl1 _ H1).
clear - H1.
rewrite <- (rev_length l1), <- (rev_length l2) in H1.
set (r1 := rev l1) in *; set (r2 := rev l2) in *; clearbody r1; clearbody r2.
revert r2 H1; induction r1; intros; destruct r2; simpl; intros; inversion H1; clear H1; subst; auto.
f_equal; auto.
Qed.

Lemma fma_dotprod_forward_error_3:
  forall (t: type) `{STD: is_standard t} (v1 v2: list (ftype t))
  (Hlen2: length v1 = length v2)
  (Hfin: finite (fma_dotprod t v1 v2)),
  let prods := map (uncurry Rmult) (List.combine (map FT2R v1) (map FT2R v2)) in
  let abs_prods := map (uncurry Rmult) (List.combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) in  
  Rabs (FT2R (fma_dotprod t v1 v2) - sum_fold prods) <= g t (length v1) * sum_fold abs_prods + g1 t (length v1) (length v1 - 1).
Proof.
intros.
assert (length v1 = O \/ 1 <= length v1)%nat by lia.
destruct H as [Hlen1|Hlen1].
destruct v1,v2; inversion Hlen1; inversion Hlen2; clear Hlen1 Hlen2; subst.
unfold fma_dotprod; simpl.
unfold Zconst; rewrite FT2R_ftype_of_float.
simpl.
unfold g1,g. simpl. 
rewrite Rmult_0_r, Rmult_0_l.
rewrite Rminus_diag, Rabs_R0.
lra.
apply fma_dotprod_forward_error_2; auto.
(* the rest of this proof is really just finite_dotprod_e from iterative_methods.floatlib *)
clear - Hfin Hlen2.
unfold fma_dotprod in Hfin.
rewrite <- fold_left_rev_right in Hfin.
rewrite <- (rev_involutive v1), <- (rev_involutive v2).
rewrite rev_combine in Hfin by auto.
rewrite <- rev_combine by (rewrite !rev_length; auto).
set (al := combine _ _) in *.
clearbody al. clear - Hfin.
induction al; simpl in *. tauto.
intros.
apply BFMA_finite_e in Hfin.
destruct Hfin as [? [? ?]].
rewrite in_app_iff in H.
destruct H.
apply IHal in H; auto.
destruct H.
subst; auto.
destruct H.
Qed.

(* mixed error bounds *)
Lemma fma_dotprod_mixed_error:
  forall (t: type) `{STD: is_standard t} (v1 v2: list (ftype t))
  (Hlen1: (1 <= length v1)%nat)
  (Hlen2: length v1 = length v2)
  (fp : ftype t) (rp : R)
  (Hfp: fma_dot_prod_rel (List.combine v1 v2) fp)
  (Hrp: R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp)
  (Hin: (forall xy, In xy (List.combine v1 v2) -> finite (fst xy) /\  finite(snd xy)))
  (Hfin: finite fp),
  exists (u : list R) (eta : R),
    length u = length v2 /\
    R_dot_prod_rel (List.combine u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n <= length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 (Zconst t 0)) * (1 + delta) /\ Rabs delta <= g t (length v2))  /\
    Rabs eta <= g1 t (length v2) (length v2 - 1).
Proof.
intros t ? v1 v2 Hlen.
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
revert Hlen. revert v1. induction v2.
{ simpl; intros; rewrite Hlen2 in Hlen; pose proof (Nat.nle_succ_0 0); try contradiction. }
intros.
  destruct v1; intros.
  { pose proof Nat.neq_0_succ (length v2); try contradiction. }
    assert (Hv1: v1 = [] \/ v1 <> []).
    destruct v1; auto. right.
    eapply hd_error_some_nil; simpl; auto.
    assert (Hlen1: length v1 = length v2) by (simpl in Hlen2; auto).
    destruct Hv1.
    assert (v2 = []). { simpl in Hlen2; apply length_zero_iff_nil;  
          apply length_zero_iff_nil in H; rewrite H in Hlen1; auto. }
    subst; clear Hlen1.
{
inversion Hfp; subst. inversion Hrp; subst.
inversion H2; inversion H3; subst; clear H2 H3.
 simpl in Hrp, Hfp, Hfin.
pose proof fma_accurate' t f a (Zconst t 0) Hfin as Hacc.
destruct Hacc as (d & e & Hde & Hd & He& Hacc).
exists [FT2R f * (1  +d)], e; repeat split.
{ simpl. rewrite Hacc.
  unfold Zconst. rewrite FT2R_ftype_of_float. simpl.
   replace ((FT2R f * FT2R a + 0) * (1 + d) + e - e) with
  (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil. }
{ intros; exists d; split; auto. simpl in H. 
  destruct n. { simpl; auto. }
  apply le_S_n in H; apply Nat.le_0_r in H; subst; simpl.
  unfold Zconst. rewrite FT2R_ftype_of_float. simpl. nra.
eapply Rle_trans; [apply Hd| apply d_le_g_1; simpl; auto].
}
eapply Rle_trans; [apply He|]. unfold g1, g; simpl; nra.
}
 (* apply IH *)
pose proof (length_not_empty v1 H) as Hlen3.
assert (HIN : (forall xy : ftype t * ftype t,
  In xy (combine v1 v2) ->finite (fst xy) /\finite (snd xy))).
  { intros. assert (HIN: In xy (combine (f :: v1) (a :: v2))) by (simpl; auto);
  specialize (Hin xy HIN); auto. }  
inversion Hfp; inversion Hrp; subst.
assert (HFIN: finite s).
  { revert Hfin; simpl.
    clear; intros. apply BFMA_finite_e in Hfin; tauto. }
specialize (IHv2 v1 Hlen3 Hlen1 s s0 H3 H7 HIN HFIN).
destruct IHv2 as (u & eta & Hlenu & A & B & C ).
(* construct u0 *)
simpl in Hfin.
pose proof fma_accurate' t f a s Hfin as Hacc;
destruct Hacc as (d & e & Hz & Hd & He & Hacc). 
unfold fst, snd; rewrite Hacc.
exists (FT2R f * (1+d) :: map (Rmult (1+d)) u), (e + eta * (1 + d)).
repeat split.
{ simpl. rewrite map_length; auto. }
{ pose proof dot_prod_combine_map_Rmult (1+d) u (map FT2R v2) (FT2R s - eta).
rewrite map_length in H0. specialize (H0 Hlenu A); simpl.
replace  ((FT2R f * FT2R a + FT2R s) * (1 + d) + e - (e + eta * (1 + d))) with
(FT2R f * (1 + d) * FT2R a + (FT2R s - eta)*(1+d)) by nra.
apply R_dot_prod_rel_cons. rewrite Rmult_comm; auto. }
{ intros. destruct n. simpl.
{ simpl. exists d; split; auto. eapply Rle_trans; [apply Hd| ]. apply d_le_g_1. apply le_n_S; lia. }
assert (n<=length v2)%nat by (simpl in H0; lia); clear H0.
specialize (B n H1); destruct B as (delta & B & HB); simpl.
replace 0 with (Rmult (1 + d) 0) by nra. rewrite map_nth.
rewrite B.
exists ( (1+d) * (1+delta) -1).
split; [nra | ].
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply HB] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd.
apply HB.
apply Hd.
replace (default_rel t * g t (length v2) + default_rel t + g t (length v2)) with
((1 + default_rel t) * g t (length v2) *1 + default_rel t *1) by nra.
rewrite one_plus_d_mul_g.
rewrite Rmult_1_r.
apply Req_le; f_equal; lia.
}
simpl.
eapply Rle_trans; [apply Rabs_triang| ].
eapply Rle_trans; [apply Rplus_le_compat; [apply He| rewrite Rabs_mult] | ].
eapply Rmult_le_compat; try apply Rabs_pos.
apply C.
eapply Rle_trans; [apply Rabs_triang| ].
rewrite Rabs_R1.
eapply Rle_trans; [apply Rplus_le_compat_l; apply Hd| apply Rle_refl ].
rewrite one_plus_d_mul_g1; try lia.
unfold g1; field_simplify.
rewrite Rplus_assoc.
eapply Rplus_le_compat.
eapply Rmult_le_compat; try apply g_pos.
apply Rmult_le_pos; [apply default_abs_ge_0| apply pos_INR ].
eapply Rmult_le_compat; try apply default_abs_ge_0; try  apply pos_INR.
apply Req_le; auto.
apply le_INR; lia.
apply Req_le; f_equal; auto; lia.
set (n:= length v2).
replace (INR (S n)) with (INR n + 1)%R. 
apply Req_le; nra.
apply transitivity with (INR (n + 1)).
rewrite plus_INR; simpl; auto. f_equal; simpl; lia.
Qed.


End NAN.
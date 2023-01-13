(*This file contains two theorems: forward and mixed error bounds for 
  the dot product of two floating point lists; the functional model for
  the vanilla dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common dotprod_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

(* forward error bound *)
Lemma dotprod_forward_error:
  forall (t: type) (v1 v2: list (ftype t))
  (Hlen1: (1 <= length v1)%nat)
  (Hlen2: length v1 = length v2)
  (fp : ftype t) (rp rp_abs : R)
  (Hfp: dot_prod_rel (List.combine v1 v2) fp)
  (Hrp: R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp)
  (Hra: R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs)
  (Hin: (forall xy, In xy (List.combine v1 v2) ->
      Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
      Binary.is_finite _ _ (snd xy) = true))
  (Hfin: Binary.is_finite (fprec t) (femax t) fp = true),
  Rabs (FT2R fp - rp) <=  g t (length v1) * Rabs rp_abs + g1 t (length v1) (length v1 - 1).
Proof.
intros ? ? ? ? ?.
rewrite (combine_map _ _ FT2R FR2).
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
rewrite <- H. clear H; revert Hlen1 Hlen2.
induction (List.combine v1 v2).
{
intros;
inversion Hrp;
inversion Hfp;
inversion Hra;
subst.
unfold g, g1; simpl;
rewrite Rminus_eq_0;
rewrite Rabs_R0;
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
rewrite (R_dot_prod_rel_single rp (FR2 a)); auto.
inversion Hfp. inversion H2. subst.
assert ( HFINa:
      (Binary.is_finite (fprec t) (femax t) (BMULT t (fst a) (snd a)) = true /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true)).
  { destruct (BMULT t (fst a) (snd a)); unfold neg_zero; simpl; auto. }
  destruct HFINa as (A & C).
rewrite BPLUS_neg_zero; auto.
pose proof BMULT_accurate' t (fst a) (snd a) A as Hmula.
destruct Hmula as (d' & e' & Hed' & Hd' & He' & B); rewrite B; clear B.
unfold g1, g; simpl.
inversion Hra. inversion H3; subst.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + default_rel t - 1) with (default_rel t) by nra. field_simplify;
field_simplify_Rabs.  unfold FR2. destruct a; simpl.
rewrite <- Rabs_mult. rewrite Rabs_Rabsolu.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
eapply Rle_trans.
apply Rplus_le_compat. apply Rmult_le_compat; try apply Rabs_pos.
apply Rle_refl. apply Hd'. apply He'.
rewrite Rmult_comm.
apply Rplus_le_compat; try nra.
}
(* non-empty l *)
intros; inversion Hfp;
inversion Hrp; inversion Hra; subst.
assert (HFINa:
        Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) by (apply Hin; simpl; auto).
(* IHl *)
assert (Hinl:forall xy : ftype t * ftype t,
       In xy l ->
       Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
       Binary.is_finite (fprec t) (femax t) (snd xy) = true).
{ intros; apply Hin; simpl; auto. }
clear Hin. destruct HFINa as (A & B).
assert (Hfm: Binary.is_finite _ _ (BMULT t (fst a) (snd a)) = true).
{ revert Hfin; subst. destruct (BMULT t (fst a) (snd a)), s;
  simpl; intros; try discriminate; auto. destruct s, s2; try discriminate; auto. }
assert (Hfins: Binary.is_finite (fprec t) (femax t) s = true).
{ revert Hfin; subst. destruct (BMULT t (fst a) (snd a)), s;
  simpl; intros; try discriminate; auto. }
specialize (IHl Hlen1 Hlen2 s s0 s1 H3 H7 H11 Hinl Hfins).
pose proof (BPLUS_accurate' t (BMULT t (fst a) (snd a)) s Hfin) as Hplus.
destruct Hplus as (d' & Hd'& Hplus); rewrite Hplus;
  clear Hplus.
pose proof (BMULT_accurate' t (fst a) (snd a) Hfm) as Hmul.
destruct Hmul as (d & e & Hed & Hd& He& Hmul); rewrite Hmul;
  clear Hmul.
(* algebra *)
apply length_not_empty_nat in H.
destruct a; cbv [ FR2 Rabsp fst snd].
set (D:= default_rel t);
set (E:= default_abs t).
simpl.
set (n:= length l) in *.
set (F:= FT2R f * FT2R f0).
field_simplify_Rabs.
replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s * d' + FT2R s - s0) with
((F * d * d' + F * d + F * d' + FT2R s * d') + (FT2R s - s0) + (1 + d') * e) by nra.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [  apply Rplus_le_compat; [eapply Rle_trans;
  [ apply Rabs_triang | ] |]  | ].
apply Rplus_le_compat_l; apply IHl .
rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He].
rewrite  Rplus_assoc.
eapply Rle_trans;
  [  apply Rplus_le_compat_r ; eapply Rle_trans; [ apply Rabs_triang | ] | ].
apply Rplus_le_compat_l; rewrite Rabs_mult; rewrite Rmult_comm;
  apply Rmult_le_compat; [ apply Rabs_pos| apply Rabs_pos| apply Hd' | ].
{ apply Rabs_le_minus in IHl. assert (Hs: Rabs (FT2R s) <=
      g t (length l) * Rabs s1 + g1 t (length l) (length l - 1) + Rabs s1).
{ eapply Rle_trans. apply IHl. apply Rplus_le_compat_l.
apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
apply Hs. }
field_simplify.
fold D E n.
rewrite !Rplus_assoc. 
replace (Rabs (F * d * d' + (F * d + F * d')) +
(D * g t n * Rabs s1 +
 (D * Rabs s1 +
  (D * g1 t n (n - 1) +
   (Rabs s1 * g t n + (g1 t n (n - 1) + Rabs (1 + d') * E)))))) with
(Rabs (F * d * d' + (F * d + F * d')) + ((1+ D) * g t n * Rabs s1 + D * Rabs s1) +
 (D * g1 t n (n - 1) + (g1 t n (n - 1) + Rabs (1 + d') * E))) by nra.
apply Rplus_le_compat.
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0) + s1)) with
(Rabs ( FT2R f *  FT2R f0) +  Rabs s1).
rewrite !Rmult_plus_distr_l.
apply Rplus_le_compat.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [ apply Rplus_le_compat; [rewrite !Rabs_mult| eapply Rle_trans; [apply Rabs_triang| ]] | ].
apply Rmult_le_compat; [rewrite <- Rabs_mult; apply Rabs_pos | apply Rabs_pos|  |  apply Hd'].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rplus_le_compat; rewrite Rabs_mult.
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd' ].
fold D F. replace (Rabs F * D * D + (Rabs F * D + Rabs F * D)) with
  ( ((1 + D)*(1+D) - 1) * Rabs F ) by nra.
apply Rmult_le_compat_r; try apply Rabs_pos; unfold D, g.
apply Rplus_le_compat; try nra.
rewrite <- tech_pow_Rmult.
apply Rmult_le_compat_l.
eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1.
eapply Rle_trans with ((1 + default_rel t)^1); try nra.
apply Rle_pow; auto.
eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1.
unfold D; apply Req_le; rewrite one_plus_d_mul_g.
repeat f_equal;  try lia.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1) at 2; auto.
symmetry.
rewrite Rabs_pos_eq; rewrite <-  Rabs_mult; auto. 
apply Rplus_le_le_0_compat; try apply Rabs_pos.
rewrite <- Rplus_assoc.
eapply Rle_trans; [apply Rplus_le_compat_l; 
  apply Rmult_le_compat_r; [ unfold E; apply default_abs_ge_0| eapply Rle_trans] | ].
apply Rabs_triang. rewrite Rabs_R1. 
apply  Rplus_le_compat_l; apply Hd'.
rewrite !Rmult_plus_distr_r. rewrite Rmult_1_l; unfold E.
rewrite <- !Rplus_assoc.
replace (D * g1 t n (n - 1) + g1 t n (n - 1)) with (g1 t n (n-1) * (1+D)) by nra; unfold D;
rewrite one_plus_d_mul_g1; auto.
rewrite Rplus_assoc.
replace (default_abs t + default_rel t * default_abs t) with 
  ((1+default_rel t) * default_abs t) by nra.
eapply Rle_trans; [apply plus_d_e_g1_le; auto| apply Req_le; f_equal;lia].
unfold FR2; simpl; auto.
Qed.


(* mixed error bound *)
Lemma dotprod_mixed_error:
  forall (t: type) (v1 v2: list (ftype t))
  (Hlen1: (1 <= length v1)%nat)
  (Hlen2: length v1 = length v2)
  (fp : ftype t) (rp : R)
  (Hfp: dot_prod_rel (List.combine v1 v2) fp)
  (Hrp: R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp)
  (Hin: (forall xy, In xy (List.combine v1 v2) ->
      Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
      Binary.is_finite _ _ (snd xy) = true))
  (Hfin: Binary.is_finite (fprec t) (femax t) fp = true),
  exists (u : list R) (eta : R),
    length u = length v2 /\
    R_dot_prod_rel (List.combine u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n <= length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g t (length v2))  /\
    Rabs eta <= g1 t (length v2) (length v2).
Proof.
intros t v1 v2 Hlen.
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
revert Hlen. revert v1. induction v2.
{ simpl; intros; rewrite Hlen2 in Hlen; pose proof (Nat.nle_succ_0 0); try contradiction. }
intros.
  destruct v1; intros.
  (* v1 empty is false *)
  { pose proof Nat.neq_0_succ (length v2); try contradiction. }
  (* v1 non-empty but either (a :: []) or (a :: l) *)
    assert (Hv1: v1 = [] \/ v1 <> []).
    { destruct v1; auto. right.
    eapply hd_error_some_nil; simpl; auto. }
    assert (Hlen1: length v1 = length v2) by (simpl in Hlen2; auto).
    destruct Hv1.
    assert (v2 = []). { simpl in Hlen2; apply length_zero_iff_nil;  
          apply length_zero_iff_nil in H; rewrite H in Hlen1; auto. }
    subst; clear Hlen1.
{ (* case singleton lists *)
clear IHv2. inversion Hfp; subst. inversion Hrp; subst.
inversion H2; inversion H3; subst; clear H2 H3.
 simpl in Hrp, Hfp, Hfin; unfold fst, snd.
assert (FINmul: Binary.is_finite (fprec t) (femax t) (BMULT t f a) = true).
{ destruct (BMULT t f a); unfold neg_zero in *; simpl; try discriminate; auto. }
rewrite BPLUS_neg_zero in *; auto.
pose proof BMULT_accurate' t f a FINmul as Hacc.
destruct Hacc as (d & e & Hed & Hd & He & Hacc).
exists [FT2R f * (1  +d)], e; repeat split.
{ simpl. rewrite Hacc. replace (FT2R f * FT2R a * (1 + d) + e - e) with
  (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil. }
{ intros; exists d; split; auto. simpl in H. 
  destruct n. { simpl; auto. } 
  apply le_S_n in H; apply Nat.le_0_r in H; subst; simpl; nra.
eapply Rle_trans; [apply Hd| apply d_le_g_1; simpl; auto].
}
eapply Rle_trans; [apply He|]. apply e_le_g1; simpl in *; auto.
} 
(* case cons lists*)
(* apply IH *)
pose proof (length_not_empty v1 H) as Hlen3.
inversion Hfp; inversion Hrp;  subst.
unfold fst, snd in Hfin, Hrp, Hfp; unfold fst, snd.
assert (HFINa: Binary.is_finite (fprec t) (femax t) f = true /\
        Binary.is_finite (fprec t) (femax t) a = true) by 
        (specialize (Hin (f,a)); apply Hin; simpl; auto).
destruct HFINa as (A & B).
set (l:=(combine v1 v2)).
(* IHl *)
assert (Hinl :forall xy : ftype t * ftype t,
       In xy l ->
       Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
       Binary.is_finite (fprec t) (femax t) (snd xy) = true).
{ intros; apply Hin; simpl; auto. }
clear Hin.
assert (Hfm: Binary.is_finite _ _ (BMULT t f a) = true).
{ revert Hfin; subst. destruct (BMULT t f a), s;
  simpl; intros; try discriminate; auto. destruct s, s1; try discriminate; auto. }
assert (Hfins: Binary.is_finite (fprec t) (femax t) s = true).
{ revert Hfin; subst. destruct (BMULT t f a), s;
  simpl; intros; try discriminate; auto. }
specialize (IHv2 v1 Hlen3 Hlen1 s s0 H3 H7 Hinl Hfins).
(* construct u *)
pose proof (BPLUS_accurate' t (BMULT t f a) s Hfin) as Hplus.
destruct Hplus as (d' & Hd'& Hplus); rewrite Hplus;
  clear Hplus.
pose proof (BMULT_accurate' t f a Hfm) as Hmul.
destruct Hmul as (d & e & Hed & Hd& He& Hmul); rewrite Hmul;
  clear Hmul.
destruct IHv2 as (u & eta & Hlenu & Hurel & Hun & Heta).
exists (FT2R f * (1+d) * (1 + d') :: map (Rmult (1+d')) u), 
  (e * (1 + d') + eta * (1 + d')).
repeat split.
{ simpl. rewrite map_length; auto. }
{ pose proof dot_prod_combine_map_Rmult (1+d') u (map FT2R v2) (FT2R s - eta).
rewrite map_length in H0. specialize (H0 Hlenu Hurel); simpl.
replace
 ((FT2R f * FT2R a * (1 + d) + e + FT2R s) * (1 + d') -
   (e * (1 + d') + eta * (1 + d')))
with
 (FT2R f * (1 + d) * (1 + d') * FT2R a  + (FT2R s - eta) * (1 + d')) by nra.
apply R_dot_prod_rel_cons; rewrite Rmult_comm; auto. }
{ intros. destruct n. simpl.
{ simpl. exists ((1 + d) * (1 + d') -1); split.
  { field_simplify; nra. } 
  { field_simplify_Rabs. eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang | apply Hd' ] |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rplus_le_compat; [|apply Hd] |  ].
    rewrite Rabs_mult. apply Rmult_le_compat; 
        [apply Rabs_pos | apply Rabs_pos | apply Hd | apply Hd'].
    eapply Rle_trans with ((1 + default_rel t) * (1 + default_rel t) - 1); try nra.
    unfold g. apply Rplus_le_compat; try nra. 
    rewrite <- tech_pow_Rmult; apply Rmult_le_compat; try nra; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
    eapply Rle_trans with ((1 + default_rel t) ^ 1); try nra.
    apply Rle_pow; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
     rewrite <- Hlen1; auto. }
}
simpl in H0; assert (Hn: (n <= length v2)%nat) by lia.
specialize (Hun n Hn);
   destruct Hun as (delta & Hun & Hdelta). simpl;
replace 0 with (Rmult  (1+d') 0) by nra. rewrite map_nth.
rewrite Hun.
exists ( (1+d') * (1+delta) -1).
split; [nra | ].
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply Hdelta] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd'.
apply Hdelta.
apply Hd'.
replace (default_rel t * g t (length v2) + default_rel t + g t (length v2)) with
((1 + default_rel t) * g t (length v2) *1 + default_rel t *1) by nra.
rewrite one_plus_d_mul_g.
rewrite Rmult_1_r.
apply Req_le; f_equal; lia.
}
simpl.
eapply Rle_trans; [apply Rabs_triang| ].
eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult| rewrite Rabs_mult] | ].
eapply Rmult_le_compat; try apply Rabs_pos.
apply He.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
eapply Rmult_le_compat; try apply Rabs_pos.
apply Heta.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
rewrite Rplus_comm. rewrite one_plus_d_mul_g1'.
assert (Hp: (1 <= S (length v2))%nat) by lia.
rewrite Hlen1 in Hlen3.
pose proof plus_d_e_g1_le' t (length v2) (S (length v2)) Hlen3 Hp as HYP; clear Hp.
eapply Rle_trans; [| apply HYP]; apply Req_le; nra.
Qed.

End NAN.
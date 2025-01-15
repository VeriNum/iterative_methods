(* This file contains floating point functional models for the summation of
  two lists, as well as theorems regarding their equivalence. *)

From vcfloat Require Import RAux FPStdLib.
Require Import List.
Import List ListNotations.

Require Import common.

Require Import Reals.
Open Scope R.


Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_R := @sum_rel R 0%R Rplus.

Lemma sum_rel_R_abs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> s1 <= s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold sum.
eapply Rplus_le_compat.
apply Rle_abs.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl;
auto.
Qed.

Lemma sum_rel_R_Rabs_pos : 
forall l s,
sum_rel_R (map Rabs l) s -> 0 <= s.
Proof.
induction  l.
-
intros.
inversion H; nra.
-
intros.
inversion H; subst; clear H.
unfold sum.
fold sum_rel_R in H3.
specialize (IHl s0 H3).
apply Rplus_le_le_0_compat; auto;
  try apply Rabs_pos.
Qed.

Lemma sum_rel_R_Rabs_eq :
forall l s,
sum_rel_R (map Rabs l) s -> Rabs s = s.
Proof.
induction  l.
-
intros.
inversion H.
rewrite Rabs_R0.
nra.
-
intros.
inversion H; subst; clear H.
unfold sum.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
eapply Req_le.
apply IHl.
fold sum_rel_R in H3.
auto.
Qed.


Lemma sum_rel_R_Rabs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
unfold sum.
eapply Rle_trans.
apply Rabs_triang.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0).
eapply Rplus_le_compat; try nra.
eapply Rle_trans with (Rabs s0).
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl; auto.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
Qed.


Lemma sum_rel_R_single :
forall (a : R) (fs : R), sum_rel_R [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum; nra.
Qed.

Lemma sum_rel_R_single' :
forall (a : R) , sum_rel_R [a] a.
Proof.
intros.
unfold sum_rel_R.
replace a with (a + 0) at 2 by nra. 
apply sum_rel_cons. apply sum_rel_nil.
Qed. 

Section NAN.

Definition sum_rel_F {NAN: FPCore.Nans} := @sum_rel (ftype Tsingle) (-0)%F32 BPLUS.

From vcfloat Require Import IEEE754_extra.

Lemma plus_zero {NAN: FPCore.Nans}  a:
Binary.is_finite _ _ a = true -> 
(a + -0)%F32 = a.
Proof.
destruct a; simpl; auto;
intros; try discriminate; auto;
destruct s;
cbv; auto.
Qed.

Lemma sum_rel_F_single {NAN: FPCore.Nans}:
forall (a : ftype Tsingle) (fs : ftype Tsingle)
  (HFIN: Binary.is_finite _ _ a = true),
  sum_rel_F [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum.
apply plus_zero; auto.
Qed.

Lemma sum_rel_R_fold : forall l rs, 
   sum_rel_R l rs -> rs = fold_right Rplus 0 l.
Proof. 
induction l.
intros; inversion H; simpl; auto.
intros; inversion H. 
fold sum_rel_R in H3.
specialize (IHl s H3).
subst; simpl.
unfold sum; auto.
Qed.

Lemma sum_map_Rmult (l : list R) (s a: R):
sum_rel_R l s -> 
sum_rel_R (map (Rmult a) l) (a * s). 
Proof. 
revert l s a. induction l.
{ intros. simpl. inversion H; subst; rewrite Rmult_0_r; auto. }
intros. inversion H. destruct l.
{ simpl; unfold sum. inversion H3; subst. rewrite Rplus_0_r.
  apply sum_rel_R_single'. }
fold sum_rel_R in H3. specialize (IHl s0 a0 H3).
unfold sum; simpl. rewrite Rmult_plus_distr_l; apply sum_rel_cons.
fold sum_rel_R. simpl in IHl; auto.
Qed.


Definition sum_rel_Ft {NAN: FPCore.Nans} (t: type) := @sum_rel (ftype t) neg_zero BPLUS.

Lemma sum_rel_Ft_single {NAN: FPCore.Nans} t fs a:
Binary.is_finite _ _ fs = true ->
sum_rel_Ft t [a] fs -> fs = a.
Proof.
intros.
inversion H0.
inversion H4; subst.
unfold sum, BPLUS; destruct a; try discriminate; 
  simpl; auto.
destruct s; simpl; auto.
Qed.


Lemma is_finite_in {NAN: FPCore.Nans} (t : type) :
  forall (l : list (ftype t)) fs,
  sum_rel_Ft t l fs ->
  let e  := default_abs t in
  let d  := default_rel t in 
  let ov := powerRZ 2 (femax t) in
  Binary.is_finite (fprec t) (femax t) fs = true ->
  forall a, In a l -> Binary.is_finite (fprec t) (femax t) a = true.
Proof.
induction l.
simpl; intros; auto.
intros. 
destruct H1; subst.
inversion H.
rewrite <- H2 in H0. clear H2.
unfold sum in H0.
destruct a0, s; auto.
destruct s, s0; simpl in H0; try discriminate.
inversion H.
fold (@sum_rel_Ft NAN t) in H5.
assert (Binary.is_finite (fprec t) (femax t) s = true).
unfold sum in H3.
rewrite <- H3 in H0. clear H3.
destruct a, s; auto.
destruct s, s0; simpl in H0; try discriminate.
specialize (IHl s H5 H6).
apply IHl; auto.
Qed.



Lemma sum_rel_Ft_fold {NAN: FPCore.Nans} : forall t l fs, 
   sum_rel_Ft t l fs -> fs = fold_right BPLUS neg_zero l.
Proof. 
induction l.
intros; inversion H; simpl; auto.
intros; inversion H. 
fold (@sum_rel_Ft NAN t) in H3.
specialize (IHl s H3).
subst; simpl.
unfold sum; auto.
Qed.


End NAN.
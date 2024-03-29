(* This file contains basic definitions and lemmas common to all other files in 
  the repository. *)

Require Import Flocq.Core.Raux.
Require vcfloat.VCFloat.
From vcfloat Require Import RAux FPStdLib Float_lemmas.

Open Scope R.

Definition rounded t r:=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

Section NAN.

Definition default_rel (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma default_rel_sep_0 t : 
  default_rel t <> 0.
Proof. 
unfold default_rel; apply Rabs_lt_pos.
rewrite Rabs_pos_eq; [apply Rmult_lt_0_compat; try nra; apply bpow_gt_0 | 
  apply Rmult_le_pos; try nra; apply bpow_ge_0].
Qed.

Lemma default_rel_gt_0 t : 
  0 < default_rel t.
Proof. 
unfold default_rel.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Lemma default_rel_ge_0 t : 
  0 <= default_rel t.
Proof. apply Rlt_le; apply default_rel_gt_0; auto. Qed.

Lemma default_rel_plus_1_ge_1 t :
1 <= 1 + default_rel t.
Proof. 
rewrite Rplus_comm. 
apply Rcomplements.Rle_minus_l; field_simplify.
apply default_rel_ge_0.
Qed.

Lemma default_rel_plus_1_ge_1' t n:
1 <= (1 + default_rel t) ^ n.
Proof. 
induction n; simpl; auto; try nra.
eapply Rle_trans with (1 * 1); try nra.
apply Rmult_le_compat; try nra.
apply default_rel_plus_1_ge_1.
Qed.

Lemma default_abs_gt_0 t : 
  0 < default_abs t.
Proof. 
unfold default_abs.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Lemma default_abs_ge_0 t :
  0 <= default_abs t.
Proof. apply Rlt_le; apply default_abs_gt_0; auto. Qed.

Definition g (t: type) (n: nat) : R := ((1 + (default_rel t )) ^ n - 1).

Lemma g_pos t n: 
  0 <= g t n. 
Proof. 
unfold g. induction n.
simpl; nra. eapply Rle_trans; [apply IHn| apply Rplus_le_compat; try nra].
simpl. eapply Rle_trans with (1 * (1+default_rel t)^n); try nra.
apply Rmult_le_compat; try nra. rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
field_simplify. apply default_rel_ge_0.
Qed.

Lemma le_g_Sn t n : 
  g t n <= g t (S n).
Proof. 
induction n; unfold g; simpl.
  { field_simplify. apply default_rel_ge_0. }
  unfold g in IHn. eapply Rplus_le_compat; try nra.
  eapply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  rewrite tech_pow_Rmult. apply Rle_pow; try lia.
  rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
  field_simplify; apply default_rel_ge_0. 
Qed.

Lemma d_le_g t n:
default_rel t <= g t (n + 1).
Proof. unfold g. induction n; simpl; field_simplify; try nra.
eapply Rle_trans; [apply IHn|].
apply Rplus_le_compat_r.
replace (default_rel t * (1 + default_rel t) ^ (n + 1) + (1 + default_rel t) ^ (n + 1))
with 
((1 + default_rel t) ^ (n + 1) * (default_rel t  + 1)) by nra.
eapply Rle_trans with ((1 + default_rel t) ^ (n + 1) * 1); try nra.
eapply Rmult_le_compat; try nra.
{ apply pow_le. apply Fourier_util.Rle_zero_pos_plus1. apply default_rel_ge_0. }
apply Rcomplements.Rle_minus_l. field_simplify; apply default_rel_ge_0.
Qed.

Lemma d_le_g_1 t n:
(1<= n)%nat -> default_rel t <= g t n.
Proof. 
intros; unfold g. 
eapply Rle_trans with ((1 + default_rel t)^1 - 1).
field_simplify; nra.
apply Rplus_le_compat; try nra.
apply Rle_pow; try lia.
apply default_rel_plus_1_ge_1.
Qed.


Lemma one_plus_d_mul_g t a n:
  (1 + default_rel t) * g t n * a + default_rel t * a  = g t (n + 1) * a.
Proof. unfold g. rewrite Rmult_minus_distr_l. rewrite tech_pow_Rmult. 
field_simplify. f_equal. rewrite Rmult_comm; repeat f_equal; lia.
Qed.
   

Definition g1 (t: type) (n1: nat) (n2: nat) : R := 
  INR n1 * default_abs t * (1 + g t n2 ).

Lemma g1_pos t n m : 0 <= g1 t n m. 
Proof. unfold g1.
apply Rmult_le_pos; try apply pos_INR.
apply Rmult_le_pos; try apply pos_INR.
apply default_abs_ge_0. unfold g; field_simplify.
apply pow_le.
apply Fourier_util.Rle_zero_pos_plus1.
apply default_rel_ge_0. 
Qed.

Lemma one_plus_d_mul_g1 t n:
(1 <= n )%nat ->
g1 t n (n - 1) * (1 + default_rel t)  =  g1 t n n.
Proof.
intros.
unfold g1, g; field_simplify.
symmetry. replace n with (S (n-1)) at 2.
rewrite <- tech_pow_Rmult.
field_simplify; nra.
rewrite <- Nat.sub_succ_l; auto.
simpl; lia.
Qed.

Lemma one_plus_d_mul_g1' t n m:
g1 t n m * (1 + default_rel t)  =  g1 t n (S m).
Proof.
intros.
unfold g1, g; field_simplify.
symmetry. 
rewrite <- tech_pow_Rmult.
field_simplify; nra.
Qed.

Lemma e_le_g1 t n:
(1 <= n )%nat ->
default_abs t <= g1 t n n.
Proof.
intros; unfold g1. eapply Rle_trans with (1 * default_abs t * 1); try nra.
apply Rmult_le_compat; try nra.
rewrite Rmult_1_l.
apply default_abs_ge_0.
apply Rmult_le_compat; try nra.
apply default_abs_ge_0.
replace 1 with (INR 1) by (simpl; nra).
apply le_INR; auto.
rewrite Rplus_comm.
apply Rcomplements.Rle_minus_l.
field_simplify; apply g_pos.
Qed.

Lemma plus_d_e_g1_le' t n m:
(1 <= n )%nat -> (1 <= m)%nat ->
g1 t n m + (1 + default_rel t) * default_abs t <= g1 t (S n) m.
Proof.
intros; replace (S n) with (n + 1)%nat by lia.
unfold g1; field_simplify.
replace (INR (n + 1)) with (INR n + 1).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r. rewrite <- Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
rewrite Rmult_comm.
rewrite Rplus_comm.
rewrite Rmult_assoc.
rewrite  Rmult_comm.
rewrite !Rplus_assoc.
apply Rplus_le_compat_l.
rewrite  Rmult_comm.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
rewrite  Rmult_comm.
apply Rmult_le_compat_l.
apply default_abs_ge_0.
apply d_le_g_1; auto.
rewrite Nat.add_comm. 
rewrite S_O_plus_INR. simpl; nra.
Qed.

Lemma plus_d_e_g1_le t n:
(1 <= n )%nat ->
g1 t n n + (1 + default_rel t) * default_abs t <= g1 t (S n) n.
Proof.
pose proof plus_d_e_g1_le' t n n; auto.
Qed. 

Lemma plus_e_g1_le t n:
g1 t n n + default_abs t <= g1 t (S n) n.
Proof.
replace (S n) with (n + 1)%nat by lia.
unfold g1; field_simplify.
replace (INR (n + 1)) with (INR n + 1).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r. rewrite <- Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
rewrite Rmult_comm.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
eapply Rle_trans with (default_abs t * INR n * g t n + 0); try nra.
apply Rplus_le_compat; try nra.
apply Rmult_le_pos.
apply default_abs_ge_0.
apply g_pos.
rewrite Nat.add_comm. 
rewrite S_O_plus_INR. simpl; nra. 
Qed.


Lemma defualt_abs_le_fmax t :
default_abs t <= bpow Zaux.radix2 (femax t).
Proof.
replace (bpow Zaux.radix2 (femax t)) with (1 * bpow Zaux.radix2 (femax t)) by nra.
unfold default_abs; apply Rmult_le_compat; try nra.
apply bpow_ge_0.
apply bpow_le.
apply Z.le_sub_le_add_r.
apply Z.le_sub_le_add_r.
eapply Z.le_trans with (fprec t + fprec t + femax t)%Z; 
  [ | repeat apply Zplus_le_compat_r; apply Z.lt_le_incl; apply fprec_lt_femax].
eapply Z.le_trans with (fprec t + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_l;apply Z.lt_le_incl; apply fprec_lt_femax ].
eapply Z.le_trans with (1 + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_r;apply Z.lt_le_incl;apply fprec_gt_one].
eapply Z.le_trans with (1 + 1 + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_r; repeat apply Zplus_le_compat_l; apply Z.lt_le_incl;
apply fprec_gt_one].
eapply Z.le_trans with (1 + 1 + 1)%Z;
[ lia |  repeat apply Zplus_le_compat_r; repeat apply Zplus_le_compat_l; apply Z.lt_le_incl;
apply fprec_gt_one].
Qed.

Lemma bpow_femax_lb t : 
4 <= bpow Zaux.radix2 (femax t).
Proof. 
pose proof fprec_gt_one t.
pose proof fprec_lt_femax t.
assert (1 < femax t)%Z.
eapply Z.lt_trans with (fprec t); auto.
eapply Rle_trans with (bpow Zaux.radix2 2).
unfold bpow; simpl; nra.
apply bpow_le; lia.
Qed.

Lemma bpow_fprec_lb t : 
2 <= bpow Zaux.radix2 (fprec t).
Proof. 
pose proof fprec_gt_one t.
eapply Rle_trans with (bpow Zaux.radix2 1).
unfold bpow; simpl; nra.
apply bpow_le; lia.
Qed.

Lemma default_abs_ub t :
default_abs t <= 1.
Proof.
unfold default_abs.
pose proof bpow_gt_0 Zaux.radix2 (femax t).
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
replace (3 - femax t - fprec t)%Z with (3 +- femax t +- fprec t)%Z by lia.
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
replace (/ 2 * bpow Zaux.radix2 3) with 4; [|simpl;nra].
rewrite !bpow_opp, !Rcomplements.Rle_div_r. 
field_simplify; try nra.
eapply Rle_trans; [| apply Rmult_le_compat ;[ | | apply bpow_fprec_lb | apply bpow_femax_lb  ]]; try nra.
apply Rlt_gt. 
replace (/ bpow Zaux.radix2 (femax t)) with (1 / bpow Zaux.radix2 (femax t)) by nra.
apply Rdiv_lt_0_compat; try nra.
apply Rlt_gt;
replace (/ bpow Zaux.radix2 (fprec t)) with (1 / bpow Zaux.radix2 (fprec t)) by nra;
apply Rdiv_lt_0_compat; try nra.
Qed.

Lemma default_rel_ub t :
default_rel t <= 1.
Proof.
unfold default_rel.
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
rewrite Rmult_comm.
rewrite <- !Rmult_assoc.
replace (bpow Zaux.radix2 1 * / 2) with 1; [|simpl;nra].
rewrite !bpow_opp, !Rcomplements.Rle_div_r. 
field_simplify; try nra.
replace 1 with  (bpow Zaux.radix2 0).
apply bpow_le.
pose proof fprec_gt_one t; lia.
simpl; auto.
apply Rlt_gt;
replace (/ bpow Zaux.radix2 (fprec t)) with (1 / bpow Zaux.radix2 (fprec t)) by nra;
apply Rdiv_lt_0_compat; try nra.
Qed.


Lemma default_rel_plus_1_gt_1 t :
1 < 1 + default_rel t.
Proof.
rewrite Rplus_comm. 
apply Rcomplements.Rlt_minus_l; field_simplify.
apply default_rel_gt_0.
Qed.

Lemma default_rel_plus_1_gt_0 t :
0 < 1 + default_rel t.
Proof.
eapply Rlt_trans with 1; [nra | ].
apply default_rel_plus_1_gt_1.
Qed.


Lemma mult_d_e_g1_le' t n m:
(1 <= n )%nat -> (1 <= m)%nat ->
g1 t n m * (1 + default_rel t)  + default_abs t <= g1 t (S n) (S m).
Proof.
intros; replace (S n) with (n + 1)%nat by lia.
replace (S m) with (m + 1)%nat by lia.
unfold g1, g; field_simplify.
replace (INR (n + 1)) with (INR n + 1) by 
  (rewrite Nat.add_comm; rewrite S_O_plus_INR; simpl; nra).
replace (INR (m + 1)) with (INR m + 1) by
  (rewrite Nat.add_comm; rewrite S_O_plus_INR; simpl; nra).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r. replace
(INR n * default_abs t * (1 + default_rel t) ^ m * default_rel t +
INR n * default_abs t * (1 + default_rel t) ^ m) with
(INR n * default_abs t * (1 + default_rel t) ^ m * (1 + default_rel t)) by nra.
rewrite !Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite !Rmult_assoc.
rewrite Rmult_comm.
rewrite !Rmult_assoc.
apply Rmult_le_compat_l. 
apply default_abs_ge_0.
rewrite <- !Rmult_assoc.
rewrite Rmult_comm.
apply Rmult_le_compat_l; [apply pos_INR| ].
rewrite Rmult_comm.
rewrite tech_pow_Rmult.
replace (S m) with (m + 1)%nat by lia; nra.
replace (default_abs t) with (default_abs t * 1) at 1 by nra.
apply Rmult_le_compat_l; [apply  default_abs_ge_0 | ].
apply default_rel_plus_1_ge_1'.
Qed.



Lemma g1n_le_g1Sn t n:
(1 <= n )%nat ->
g1 t n (n - 1) <= g1 t (S n) (S (n - 1)).
Proof.
intros;
replace (S n) with (n + 1)%nat by lia.
unfold g1; field_simplify.
replace (INR (n + 1)) with (INR n + 1).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r. 
apply Rplus_le_compat.
apply Rmult_le_compat; [
apply Rmult_le_pos; [apply pos_INR | apply default_abs_ge_0 ] | 
  apply g_pos | | ].
rewrite Rplus_comm;
apply Rcomplements.Rle_minus_l; field_simplify; apply default_abs_ge_0.
replace ((n + 1 - 1))%nat with (S (n-1))%nat by lia.
apply le_g_Sn. 
rewrite Rplus_comm;
apply Rcomplements.Rle_minus_l; field_simplify; apply default_abs_ge_0.
rewrite Nat.add_comm. 
rewrite S_O_plus_INR. simpl; nra. 
Qed.

Lemma Rplus_le_lt_compat a1 a2 b1 b2 :
 a1 <= a2 -> b1 < b2 ->  a1 + b1 < a2 + b2.
Proof.  nra. Qed.

Lemma g1n_lt_g1Sn t n:
(1 <= n )%nat ->
g1 t n (n - 1) < g1 t (S n) (S (n - 1)).
Proof.
intros;
replace (S n) with (n + 1)%nat by lia.
unfold g1; field_simplify.
replace (INR (n + 1)) with (INR n + 1).
rewrite !Rmult_plus_distr_l.
rewrite !Rmult_1_r.
assert (INR n * default_abs t < default_abs t * INR n + default_abs t).
{ apply Rle_lt_trans with (INR n * default_abs t + 0) ; try nra.
apply Rplus_le_lt_compat; try nra.
apply default_abs_gt_0. }
apply Rplus_le_lt_compat; try nra.
apply Rmult_le_compat; [
apply Rmult_le_pos; [apply pos_INR | apply default_abs_ge_0 ] | 
  apply g_pos | | ].
rewrite Rplus_comm;
apply Rcomplements.Rle_minus_l; field_simplify; apply default_abs_ge_0.
apply le_g_Sn.
rewrite Nat.add_comm. 
rewrite S_O_plus_INR. simpl; nra. 
Qed.


Definition error_rel (t: type) (n: nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    (g t (n-1)) * (Rabs r + e/d)
  else 0%R.

End NAN.
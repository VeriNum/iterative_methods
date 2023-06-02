(* The main theorem in this file is "finite_fma_from_bounded". It states that under
some restrictions on the elements of the vectors, an fma dot product will never overflow *)

Require Import vcfloat.VCFloat vcfloat.FPLib.
Require Import List.
Import ListNotations.
Require Import common dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.
Require Import fma_dot_acc.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

(* the overflow threshold *)
Definition fmax (t: type) := bpow Zaux.radix2 (femax t).

(* the square of the bounds we use on each element of the combined vector
 that we perform an fma dot product on *)
Definition fun_bnd (t : type) (n : nat) :=
let x := (fmax t - default_abs t) / (1 + default_rel t) - g1 t n (n-1) in
let y := 1 / (1 + INR n * (g t (n - 1) + 1)) in x * y.

(* start helper lemmas on R *)
Lemma rdiv_lt (a b: R) :
  0 < b -> 0 < a -> b < a -> / a < / b. 
Proof. 
intros.
replace (/b) with (1/b) by nra.
apply Rdiv_lt_right; auto.
rewrite Rmult_comm.
apply Rdiv_lt_left; auto.
nra.
Qed.

Lemma rdiv_le (a b: R) :
  0 < b -> 0 < a -> b <= a -> / a <= / b. 
Proof. 
intros. 
replace (/b) with (1/b) by nra.
apply Rcomplements.Rle_div_r; auto.
rewrite Rmult_comm.
apply Rdiv_le_left; auto.
nra.
Qed.

Lemma rdiv_mult_eq :
forall a b, b <> 0 -> a/b = a * (1/b) .
Proof.
(intros; field_simplify; nra).
Qed.

Lemma Rminus_le_minus a b c :
 b <= c -> a - c <= a - b.
Proof.  nra. Qed.

Lemma Rminus_lt_minus a b c :
 b < c -> a - c < a - b.
Proof.  nra. Qed.
(* end helper lemmas on R *)


(* start facts about the bound fun_bnd *)
Lemma fun_bnd_pos_1 : 
forall t n
(Hn : g1 t (n + 1) n <= fmax t), 
0 <= (fmax t - default_abs t) / (1 + default_rel t) - g1 t n (n-1).
Proof.
intros;
apply Rle_0_minus. apply Generic_proof.Rdiv_le_mult_pos;
[apply default_rel_plus_1_gt_0 | apply Rminus_plus_le_minus].
assert (Hn': (n=0)%nat \/ (1<=n)%nat) by lia; destruct Hn'; subst.
{ simpl. unfold g1, g. simpl; field_simplify. apply defualt_abs_le_fmax. }
assert (Hn': (n=1)%nat \/ (1 < n)%nat) by lia; destruct Hn'; subst.
{ simpl. unfold g1, g. simpl; field_simplify.
eapply Rle_trans.
apply Rplus_le_compat. 
apply Rmult_le_compat.
apply default_abs_ge_0. 
apply default_rel_ge_0.
apply default_abs_ub.
apply default_rel_ub.
apply Rmult_le_compat_l; try nra.
apply default_abs_ub.
eapply Rle_trans; [| apply bpow_femax_lb]; nra. }
eapply Rle_trans. apply mult_d_e_g1_le'; try lia. 
replace (S n) with (n + 1)%nat by lia.
replace (S (n - 1)) with n by lia; auto.
Qed.


Lemma fun_bnd_le (t : type) (n : nat) :
forall (Hn : g1 t (S n + 1) (S n) <= fmax t), 
fun_bnd t (S n) <= fun_bnd t n.
Proof.
assert (Hn': (n=0)%nat \/ (1<=n)%nat) by lia; destruct Hn'; subst.
{ intros; simpl. unfold fun_bnd. apply Rmult_le_compat; try apply Rabs_pos.
apply fun_bnd_pos_1; auto. simpl. unfold g. simpl; field_simplify; nra.
apply Rminus_le_minus. simpl. unfold g1, g; field_simplify; simpl.
field_simplify. apply default_abs_ge_0.
simpl; unfold g; field_simplify; simpl; try nra. }
intros; unfold fun_bnd.
assert (0 < 1 + INR (S n) * (g t (S n - 1) + 1)).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
assert (
INR n * g t (n - 1) + INR n + 1 > 0).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rplus_le_lt_0_compat; [| apply lt_0_INR; lia].
apply Rmult_le_pos; try apply pos_INR.
apply g_pos. }
apply Rmult_le_compat; try apply Rabs_pos.
apply fun_bnd_pos_1; auto.
apply Rdiv_le_0_compat_Raux; try nra.
apply Rminus_le_minus.
replace (S n -1)%nat with (S (n-1))%nat by lia.
apply g1n_le_g1Sn; auto.
apply Rcomplements.Rle_div_r.
apply Rlt_gt.
replace (/ (1 + INR (S n) * (g t (S n - 1) + 1))) with 
  (1/(1 + INR (S n) * (g t (S n - 1) + 1))) by nra.
apply Rdiv_lt_0_compat; try nra.
field_simplify; try nra.
apply Rcomplements.Rle_div_r; try nra.
rewrite Rmult_1_l.
apply Rplus_le_compat; try nra.
apply Rplus_le_compat.
apply Rmult_le_compat; [ apply pos_INR | apply g_pos | | ].
apply le_INR; lia.
replace (S n - 1)%nat with (S (n-1))%nat by lia.
apply le_g_Sn.
apply le_INR; lia.
Qed.

Lemma fun_bound_pos t n :
forall (Hn : g1 t (n + 1) n <= fmax t), 
0 <= fun_bnd t n. 
Proof.
intros;
unfold fun_bnd; apply Rmult_le_pos.
apply fun_bnd_pos_1; auto.
apply Rdiv_le_0_compat_Raux; try nra.
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos.
Qed.
(* end facts about the bound fun_bnd *)


(* main theorem *)
Lemma finite_fma_from_bounded : 
  forall (t: type) `{STD: is_standard t} (v1 v2: list (ftype t))
  (fp : ftype t) 
  (Hfp: fma_dot_prod_rel (List.combine v1 v2) fp)
  (Hn : g1 t (S  (length (List.combine v1 v2)) + 1) (S (length (List.combine v1 v2))) <= fmax t),
  (forall x, In x (List.combine v1 v2) -> finite (fst x) /\ finite (snd x) /\ 
    Rabs (FT2R (fst x)) < sqrt  (fun_bnd t (length (List.combine v1 v2))) /\
    Rabs (FT2R (snd x)) < sqrt  (fun_bnd t (length (List.combine v1 v2))))-> 
  finite fp. 
Proof.
intros ? ? ? ?.
induction (List.combine v1 v2).
{ intros; inversion Hfp; subst; simpl; auto. unfold Zconst.
   rewrite finite_is_finite, is_finite_Binary, float_of_ftype_of_float. reflexivity. }
{ intros. inversion Hfp; subst.
assert (Hn' : g1 t (S (length l) + 1) (S (length l)) <= fmax t).
{ eapply Rle_trans; [ | apply Hn]; simpl. set (n:= (length l + 1)%nat).
  replace (length l) with (n-1)%nat by lia.
  replace (S(n-1))%nat with (S n - 1)%nat by lia; apply g1n_le_g1Sn; lia. }
assert (Hin: forall x : (ftype t * ftype t),
       In x l -> finite (fst x) /\ finite (snd x) /\
       Rabs (FT2R (fst x)) < sqrt (fun_bnd t (length l)) /\
       Rabs (FT2R (snd x)) < sqrt (fun_bnd t (length l))).
  { intros. repeat split; [apply H; simpl; auto | apply H; simpl; auto  | | ]. 
    eapply Rlt_le_trans; [apply H; simpl; auto | apply sqrt_le_1_alt; apply fun_bnd_le; auto  ].
    eapply Rlt_le_trans; [apply H; simpl; auto | apply sqrt_le_1_alt; apply fun_bnd_le; auto ]. }
assert (Hfina :finite (fst a) /\finite (snd a)) by
  (split; apply H; simpl; auto); destruct Hfina as (Hfina1 & Hfina2).
specialize (IHl s H3 Hn' Hin). 
apply is_finite_fma_no_overflow'; auto. 
unfold fma_no_overflow, rounded.
destruct (generic_round_property t (FT2R (fst a) * FT2R (snd a) + FT2R s)) as 
  (del & eps & Hed & Hd & He & Hrn );
rewrite Hrn; clear Hrn.
destruct (dotprod_rel_R_exists_fma t l s H3) as (rs & Hrs).
destruct (sum_rel_R_abs_exists_fma t l s H3) as (rs_abs & Habs).
pose proof fma_dotprod_forward_error NAN t (fst (List.split l)) (snd (List.split l))
  (length_split l) s rs rs_abs as Hacc. 
rewrite (combine_map R R Rabs Rabsp) in Hacc.
rewrite !(combine_map (ftype t) R FT2R FR2) in Hacc.
rewrite !combine_split in Hacc.
specialize (Hacc H3 Hrs Habs IHl).
apply Rabs_le_minus in Hacc.
rewrite split_length_l in *.
set (n:=(length l)) in *.
assert (Hacc' : Rabs (FT2R s) <= (g t n + 1) * rs_abs + g1 t n (n - 1)).
{ eapply Rle_trans; [apply Hacc| field_simplify; apply Rplus_le_compat].
apply Rplus_le_compat_r. apply Rmult_le_compat_l. apply g_pos.
rewrite (@R_dot_prod_rel_Rabs_eq (map FR2 l)); try nra; auto.
rewrite <- (@R_dot_prod_rel_Rabs_eq (map FR2 l)); try nra; auto.
apply (@dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. } clear Hacc.
pose proof dotprodR_rel_bound' as C.
pose proof dotprodR_rel_bound'' as D.
eapply Rle_lt_trans; [apply Rabs_triang |].
rewrite Rabs_mult.
eapply Rle_lt_trans; [apply Rplus_le_compat |]. 
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans; [apply Rabs_triang |].
apply Rplus_le_compat.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
apply Rlt_le; apply H; simpl; auto.
apply Rlt_le; apply H; simpl; auto.
eapply Rle_trans.
apply Hacc'.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l. 
apply Rplus_le_le_0_compat; try nra. apply g_pos.
apply D. 
apply fun_bound_pos.
apply Hn'.
apply Habs.
intros; split; apply Rlt_le; apply H; simpl; auto.
assert (HD: Rabs (1 + del) <= (1 + default_rel t )).
{ eapply Rle_trans; [apply Rabs_triang| rewrite Rabs_R1; apply Rplus_le_compat_l].
eapply Rle_trans; [apply Hd |];  nra. }
apply HD.
apply He.
rewrite sqrt_def.
{
(*algebra*)
unfold fun_bnd.
replace (length (a :: l)) with (S n) by (simpl; lia).
set (x:= (g t ((S n) - 1) + 1)).
set (y:= (1 + INR (S n) * x)).
set (z:= g1 t (S n) ((S n) - 1)).
set (u := ((fmax t - default_abs t) / (1 + default_rel t) - z) * (1 / y)).
rewrite <- !Rplus_assoc.
replace (( u + (g t n + 1) * (INR (length l) *  u)))
  with ( u * (1 + (g t n + 1) * (INR (length l))))
  by nra.
apply Rcomplements.Rlt_minus_r.
apply Rcomplements.Rlt_div_r. 
apply Rlt_gt; apply default_rel_plus_1_gt_0.
apply Rcomplements.Rlt_minus_r.
assert (0 < 1 + (g t n + 1) * INR (length l)).
{ apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
apply Rcomplements.Rlt_div_r; auto.
assert (0 < 1 / (1 + INR (S (length l)) * (g t (S (length l) - 1) + 1))).
{ apply Rcomplements.Rdiv_lt_0_compat; try nra.
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
assert (0 < 1 + INR (S n) * (g t (S n - 1) + 1)).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
rewrite rdiv_mult_eq; try nra.
unfold u, z, y, x.
apply Rmult_lt_compat.
apply fun_bnd_pos_1; auto.
apply Rlt_le; auto.
unfold fmax.
apply Rminus_lt_minus.
replace n with (length l).
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl. subst.
simpl. unfold g1, g; field_simplify; simpl. field_simplify; apply default_abs_gt_0.
apply length_not_empty_nat in H4.
replace (S (length l) - 1)%nat with (S (length l - 1))%nat by lia.
apply g1n_lt_g1Sn; auto.
subst n; auto.
apply Rcomplements.Rlt_div_r.
apply Rlt_gt.
replace (/ (1 + INR (S n) * (g t (S n - 1) + 1))) with 
  (1/(1 + INR (S n) * (g t (S n - 1) + 1))) by nra.
apply Rdiv_lt_0_compat; try nra. 
field_simplify; try nra.
apply Rcomplements.Rlt_div_r; try nra.
rewrite Rmult_1_l.
apply Rplus_lt_le_compat; try nra.
apply Rplus_le_lt_compat.
rewrite Rmult_comm.
apply Rmult_le_compat; [ apply pos_INR | apply g_pos | | ].
apply le_INR; lia.
replace (S n - 1)%nat with (n)%nat by lia; try nra.
unfold n. 
apply lt_INR; lia.
}
apply fun_bound_pos; auto.
intros; simpl; auto.
intros; simpl; auto.
}
Qed.


End NAN.
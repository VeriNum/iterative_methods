From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import ssreflect ssralg all_algebra seq.
From Iterative Require Import dot_prod_defn.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Section WITHNANS.
Context {NANS: Nans}.


Lemma real_lt_1 :
forall a b c,
a <= b -> b < c -> a < c.
Proof. intros; apply Rle_lt_trans with b; auto. Qed.



Lemma x_pow_gt_0:
  forall (x:R) (n:nat),
  0 < x -> 0 < x^n.
Proof.
intros. induction n.
+ simpl. nra.
+ simpl. apply Rmult_lt_0_compat; nra.
Qed.

Print prove_roundoff_bound.
Lemma prove_rndoff' :
  forall (a b : ftype Tsingle) vmap n,
  (1 < n )%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  prove_roundoff_bound (@bmap Tsingle n) (vmap a b) (@sum_expr Tsingle a b) 
     ( Rabs (rval (env_ (vmap a b)) (@sum_expr Tsingle a b)) * u0 + u).
Proof.
intros.
prove_roundoff_bound.
- (* first subgoal requires that we 
show no overflow for all subexpressions *)
prove_rndval.
set (ty := Tsingle).
set (nr := INR n) . 
(*
we need to show that |(a+b)*(1+d)+e|< overflow by 
appropriately bounding |a| and |b| in bmap.
|a| + |b| < (overflow - e) / (1+d)
*)
try apply Rabs_le in BOUND, BOUND0.
assert (Rabs (1 + u2) <= 1 + u0) as Hu2. 
{ unfold u0. simpl. 
  apply Rle_trans with 
  (Rabs 1 + Rabs u2). 
  + apply Rabs_triang.
  + rewrite Rabs_R1. apply Rplus_le_compat_l. nra.
}
apply Rlt_Rminus.
rewrite Rmult_1_l. 
eapply real_lt_1; [eapply Rabs_triang | 
    rewrite Rabs_mult; eapply real_lt_1; [ eapply Rplus_le_compat; 
          [eapply Rmult_le_compat; try apply Rabs_pos; 
                      [eapply Rle_trans; [apply Rabs_triang | eapply Rplus_le_compat; 
                                      [apply BOUND0| apply BOUND]] 
                          | eapply Rle_trans; [ apply Hu2 | apply Rle_refl] ] | apply H0 ] | ]].
apply Rle_lt_trans with 
(((F' / INR n + 2* u/ u0) + (F' * (INR n -1)/ INR n + 2* u / u0)) * (1+ u0) +
/ 2 *
/ 713623846352979940529142984724747568191373312).
+ assert (/ IZR (2 ^ 150) = / 2 * / 713623846352979940529142984724747568191373312).
  { nra. } rewrite H2. clear H2.
  apply Rplus_le_compat_r. apply Rmult_le_compat_r.
  * unfold u0; simpl; nra.
  * apply Rplus_le_compat_r.  unfold u,u0. simpl.
    apply Rplus_le_compat_r.
    assert (F' / INR n = (F' / INR n) * 1). { nra. } rewrite H2.
    assert (F' / (INR n *(1 + / 2 * / IZR (Z.pow_pos 2 23)) ^ n) = 
            F' * / (INR n *(1 + / 2 * / IZR (Z.pow_pos 2 23)) ^ n)).
    { nra. } rewrite H3. rewrite Rinv_mult_distr. 
    assert (F' * (/ INR n * / (1 + / 2 * / IZR (Z.pow_pos 2 23))^ n) = 
            (F' * / INR n) * / (1 + / 2 * / IZR (Z.pow_pos 2 23))^ n).
    { nra. } rewrite H4. apply Rmult_le_compat_l.
    ++ apply Rmult_le_pos.
       -- unfold F', F_max. simpl; nra.
       -- apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR;lia.
    ++ replace 1 with (/1) by nra. apply Rlt_le, Rinv_lt_contravar.
       replace (/1) with 1 by nra. apply Rmult_lt_0_compat. nra.
       apply pow_lt. simpl;nra. 
       replace (/1) with 1 by nra. apply Rlt_pow_R1. simpl;nra.
       lia.
    ++ apply not_0_INR. lia.
    ++ apply pow_nonzero. simpl;nra. 
+ assert (((F' / INR n  + 2* u/u0) +
            (F' * (INR n - 1) / INR n +  2* u / u0)) = 
           F' + 4 * u / u0).
  { assert (F' * (INR n - 1) / INR n = F' * (INR n / INR n) - F' / INR n).
    { nra. } rewrite H2. 
    assert (INR n / INR n = 1). { apply Rinv_r. apply not_0_INR. lia. }
    rewrite H3; nra.
  } rewrite H2. 
  unfold u, u0, F', F_max; simpl; nra.
-
prove_roundoff_bound2. 
try apply Rabs_le in BOUND, BOUND0.
match goal with |- context[Rabs ?a <= _] =>
field_simplify a
end.
assert (He0: Rabs e0 <= u).
{ eapply Rle_trans. apply E. subst u; simpl; nra. }
assert (Hd: Rabs d <= u0).
{ eapply Rle_trans. apply E0. subst u0; simpl; nra. }
replace (v_a * d + v_b * d + e0) with ((v_a + v_b) * d + e0) by nra.
eapply Rle_trans; [
apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult; eapply Rle_trans;
  [apply Rmult_le_compat; 
      [ apply Rabs_pos | apply Rabs_pos |   apply Rle_refl | apply Hd ] | 
  apply Rle_refl ]  | apply He0 ] | ]  ].
nra.
Qed.



Lemma reflect_reify_sumF : 
  forall a b,
  fval (env_ (vmap a b)) (@sum_expr Tsingle a b) = sum Tsingle a b .
Proof. reflexivity. Qed.

Lemma reflect_reify_sumR : 
  forall a b,
  rval (env_ (vmap a b)) (@sum_expr Tsingle a b) = FT2R a + FT2R b .
Proof. reflexivity. Qed.


Lemma prove_rndoff:
  forall (a b : ftype Tsingle) (n : nat),
  let ty:= Tsingle in let nr := INR n in 
( 1 < n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
boundsmap_denote (@bmap Tsingle n) (vmap a b)  ->
   Rabs (FT2R (sum Tsingle a b) - (FT2R a + FT2R b)) <= 
     ( Rabs ( FT2R a + FT2R b ) * u0 + u) .
Proof.
intros ? ? ? ? ? Hn ? ? HBMD.
pose proof prove_rndoff' a b  vmap  n Hn HBMD.
unfold roundoff_error_bound in H.
rewrite <- reflect_reify_sumR.
rewrite <- reflect_reify_sumF.
destruct H as (H1 & H2); eapply Rle_trans; [apply H2| subst u0 u; nra].
Qed.

Definition Flist_to_Rlist {ty} (L : list ( ftype ty)) :=
  map (fun a => (FT2R a)) L.


Definition Flist_to_Rlist_abs {ty} (L : list ( ftype ty)) :=
  map (fun a => Rabs (FT2R a)) L.

Lemma Rabs_list_rel {ty} (L : list ( ftype ty)):
  Rabs (sum_fixR (Flist_to_Rlist L)) <= sum_fixR (Flist_to_Rlist_abs L).
Proof.
induction L.
+ simpl. rewrite Rabs_R0. nra.
+ simpl.
  apply Rle_trans with 
  (Rabs (FT2R a) + Rabs (sum_fixR (Flist_to_Rlist L))).
  apply Rabs_triang.
  apply Rplus_le_compat; nra.
Qed.


Lemma INR_n_ge_1:
  forall (n:nat), (1 <= n)%nat -> / INR n <= 1.
Proof.
intros. 
assert (n = 1%nat \/ (1 < n)%nat).
{ lia. } destruct H0.
+ rewrite H0. simpl. nra.
+ apply Rlt_le. 
  assert (1 = /1). by nra.
  rewrite H1. apply  Rinv_1_lt_contravar.
  nra. by apply lt_1_INR.
Qed.


Lemma Rlt_2 :
forall a b, 1 < b -> 0 < a -> a /b  < a.
Proof.
intros.
apply (Rdiv_lt_left b a a). auto; try lra.
assert (a <= a * 1) by nra. 
eapply (real_lt_1); try apply H1.
apply Rmult_lt_compat_l; auto.
Qed.


Lemma R_div_mult_eq : 
forall a b c, c <> 0 -> b = c -> a/b * c = a. 
Proof. intros. subst. field. auto. Qed.

Ltac simpl_overflow :=
let e:= fresh "e" in let u:= fresh "u" in let d:= fresh "d" in 
set (e := (femax Tsingle)) ;
set (u:= (/ 2 * bpow Zaux.radix2 (3 - e - fprec Tsingle))) ;
set (d:=/ 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ;
simpl in e, u, d;
subst e u d.



Lemma C_ge_0 (m n:nat):
  0 <= C m n.
Proof.
unfold C. apply Rmult_le_pos.
+ apply pos_INR.
+ rewrite Rinv_mult_distr.
  - apply Rmult_le_pos; 
    (apply Rlt_le, Rinv_0_lt_compat; apply lt_0_INR, lt_O_fact).
  - apply not_0_INR. apply fact_neq_0.
  - apply not_0_INR. apply fact_neq_0.
Qed.


Lemma fact_bound:
  forall m n:nat,
  (n <= m)%nat -> 
  INR (fact m) / INR (fact (m - n)) <= INR (m ^ n).
Proof.
intros.
induction n.
+ simpl. 
  assert ((m - 0)%nat = m). { lia. } rewrite H0.
  assert (INR (fact m) / INR (fact m) = 1).
  { apply Rinv_r. apply not_0_INR. apply fact_neq_0. }
  rewrite H1. nra.
+ simpl.
  assert ((n <= m)%nat).
  { apply le_trans with (S n). lia. lia. } specialize (IHn H0).
  rewrite mult_INR. 
  assert (INR (fact (m - S n)) =  INR (fact (m - n)) * / INR (m - n) ).
  { assert ((m-n)%nat = S (m - S n)).
    { lia. } 
    assert (fact (m - n) = fact (S (m - S n))).
    { by rewrite H1. } rewrite H2. simpl.
    assert ((fact (m - S n)+ (m - S n) * fact (m - S n))%nat = 
            ((m - n) * fact (m - S n))%nat).
    { lia. } rewrite H3. rewrite mult_INR.
    assert (INR (m - n) * INR (fact (m - S n)) * / INR (m - n) = 
            INR (fact (m - S n)) * (INR (m - n) */ INR (m - n))).
    { nra. } rewrite H4. rewrite Rinv_r. nra.
    apply not_0_INR;lia.
  } rewrite H1. 
  assert (INR (fact m) / (INR (fact (m - n)) * / INR (m - n)) = 
          INR (fact m) * / (INR (fact (m - n)) * / INR (m - n))).
  { nra. } rewrite H2. rewrite Rinv_mult_distr.
  - rewrite Rinv_involutive.
    * assert (INR (fact m) * (/ INR (fact (m - n)) * INR (m - n)) = 
              (INR (fact m) / INR (fact (m - n))) * INR (m - n)).
      { nra. } rewrite H3.
      apply Rle_trans with 
      (INR (m ^ n) * INR (m - n)).
      ++ apply Rmult_le_compat_r.
         -- apply pos_INR. 
         -- apply IHn.
      ++ rewrite Rmult_comm. apply Rmult_le_compat_r.
         -- apply pos_INR.
         -- apply le_INR; lia.
    * apply not_0_INR;lia.
  - apply not_0_INR, fact_neq_0.
  - apply Rinv_neq_0_compat. apply not_0_INR;lia.
Qed.

Lemma pow_2_gt_0:
  forall n:nat,
  (0 < 2 ^ n)%nat.
Proof.
intros.
induction n; simpl;lia.
Qed.


Lemma fact_low_bound:
  forall n:nat,
  (1 < n)%nat ->
  (INR (2 ^ n) < INR (fact n * (n + 1))%nat).
Proof.
intros.
induction n.
+ contradict H. lia.
+ assert (n = 1%nat \/ (1 < n)%nat). { lia. } destruct H0.
  - rewrite H0. simpl. nra.
  - specialize (IHn H0). simpl.
    assert ((2 ^ n + 0)%nat = (2^n)%nat). { lia. } rewrite H1.
    assert (((fact n + n * fact n) * S (n + 1))%nat = 
              ((n+1) * (fact n * S (n+1)))%nat).
    { lia. } rewrite H2. 
    apply Rlt_trans with 
    (INR (2 * (fact n * (n + 1)))).
    * apply lt_INR. apply INR_lt in IHn. lia.
    * rewrite !mult_INR. apply Rmult_lt_compat.
      ++ simpl;nra.
      ++ apply Rmult_le_pos; apply pos_INR.
      ++ apply lt_INR. lia.
      ++ apply Rmult_lt_compat_l.
         -- apply lt_0_INR. apply lt_O_fact.
         -- apply lt_INR;lia.
Qed.


Lemma pow_INR:
  forall (m n: nat),
  INR (m ^ n) = (INR m)^n.
Proof.
intros. induction n.
+ simpl. nra.
+ simpl. rewrite mult_INR IHn. nra.
Qed.

Lemma pow_invert_1: forall x y z :R,
  (0 < z) ->  x <= y / z -> x * z <= y.
Proof.
intros.
replace y with (y * 1) by nra.
assert (1 = /z * z).
{ symmetry. apply Rinv_l. nra. } rewrite H1.
replace (y * (/z * z)) with ((y / z) * z) by nra.
apply Rmult_le_compat_r.
+ nra.
+ nra.
Qed.


Lemma pow_invert: forall x y z :R,
  (0 < z) -> x * z <= y -> x <= y / z.
Proof.
intros.
replace x with (x * 1) by nra.
assert (1 = z * /z).
{ symmetry. apply Rinv_r. nra. } rewrite H1.
replace (x * (z * / z)) with ((x * z) / z) by nra.
apply Rmult_le_compat_r.
+ apply Rlt_le, Rinv_0_lt_compat; nra.
+ nra.
Qed.

Lemma pow_invert_eq:
  forall x y z :R,
  (0 <> z) -> x * z = y -> x = y / z.
Proof.
intros.
replace x with (x * 1) by nra.
assert (1 = z * /z).
{ symmetry. apply Rinv_r. nra. } rewrite H1.
replace (x * (z * / z)) with ((x * z) / z) by nra.
nra.
Qed.


Require Import Coq.ZArith.Znat.
Lemma ratio_gt_0:
  forall m:nat, 
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (m < Z.to_nat (Z.pow_pos 2 23))%nat ->
  0 < (1 - INR m * u0 / INR 2).
Proof.
intros.
replace (INR 2) with 2 by (simpl;nra).
assert (INR m * u0 < 2 -> 0 < 1 - INR m * u0 / 2).
{ nra. } apply H0.
unfold u0. simpl.
assert (INR m < 2 * 2 * IZR (Z.pow_pos 2 23) ->
        INR m * (/ 2 * / IZR (Z.pow_pos 2 23)) < 2).
{ simpl; nra. } apply H1.
apply Rlt_trans with 
(INR (Z.to_nat (Z.pow_pos 2 23))).
+ apply lt_INR;lia.
+ rewrite INR_IZR_INZ. 
  assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
  { lia. } rewrite H2. nra.
Qed.
  
Lemma delta_bound:
  forall m:nat, 
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (m < Z.to_nat (Z.pow_pos 2 23))%nat ->
  ((1 + u0) ^ m - 1) < 2.
Proof.
intros.
assert ((1 + u0) ^ m  < 3 -> (1 + u0) ^ m - 1 < 2).
{ nra. } apply H0.
assert (1+u0 = u0 + 1). { nra. } rewrite H1. clear H1.
rewrite binomial.
apply Rle_lt_trans with
(sum_f_R0 (fun i : nat => (INR (m ^ i) / INR (fact i)) * u0 ^ i * 1 ^ (m - i)) m).
+ apply sum_Rle. intros.
  rewrite Rmult_assoc. 
  match goal with |-context[_ <= ?a * ?b * ?c]=>
    replace (a * b * c) with (a * (b * c)) by nra
  end. apply Rmult_le_compat.
  - apply C_ge_0 .
  - apply Rmult_le_pos. try apply Rlt_le,x_pow_gt_0;try nra.
    unfold u0; simpl;nra. apply Rlt_le,x_pow_gt_0. nra.
  - unfold C. 
    assert (INR (fact m) / (INR (fact n) * INR (fact (m - n))) = 
              (INR (fact m) / INR (fact (m-n))) * / INR (fact n)).
    { assert (INR (fact m) / (INR (fact n) * INR (fact (m - n))) = 
              INR (fact m) * / (INR (fact n) * INR (fact (m - n)))).
      { nra. } rewrite H2. 
      rewrite Rinv_mult_distr; try nra; try apply not_0_INR, fact_neq_0.
    } rewrite H2. apply Rmult_le_compat_r.
    * apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR. apply lt_O_fact.
    * apply fact_bound;lia.
  - nra.
+ assert (m = 0%nat \/ (0 < m)%nat). { lia. } destruct H1.
  - rewrite H1. simpl. nra.
  - apply Rle_lt_trans with 
    (1 + INR m *u0 * sum_f_R0 (fun i: nat => INR (m^i) * u0^i / INR (2^i)) (m-1)%nat).
    * rewrite decomp_sum.
      ++ simpl.
         assert (1 / 1 * 1 * 1 ^ (m - 0) = 1). { rewrite pow1. nra. }
         rewrite H2. clear H2.
         apply Rplus_le_compat_l.
         rewrite scal_sum. 
         assert ((m - 1)%nat = (Init.Nat.pred m)). { lia. } rewrite H2.
         apply sum_Rle. intros.
         rewrite !mult_INR. rewrite pow1.
         assert (INR m * INR (m ^ n) / INR (fact n + n * fact n) *
                    (u0 * u0 ^ n) * 1 = 
                 ( INR (m ^ n) / INR (fact n + n * fact n) * u0^n) * 
                 (INR m * u0)).
         { nra. } rewrite H4. apply Rmult_le_compat_r.
         -- apply Rmult_le_pos. apply pos_INR. unfold u0;simpl;nra.
         -- rewrite Rmult_assoc. 
            assert (INR (m ^ n) * u0 ^ n / INR (2 ^ n) = 
                    INR (m ^ n) * ( / INR (2 ^ n) * u0^n)).
            { nra. } rewrite H5. apply Rmult_le_compat_l.
            ** apply pos_INR.
            ** apply Rmult_le_compat_r; 
                  first by apply Rlt_le,x_pow_gt_0; unfold u0; simpl; nra.
               assert (n = 0%nat \/ (0 < n)%nat).
               { lia. } destruct H6. 
               +++ rewrite H6. simpl. nra.
               +++ assert (n = 1%nat \/ (1 < n)%nat). { lia. } destruct H7.
                   --- rewrite H7. simpl. nra.
                   --- apply Rlt_le, Rinv_lt_contravar.
                       *** apply Rmult_lt_0_compat. apply lt_0_INR. 
                           apply pow_2_gt_0. apply lt_0_INR.
                           assert ((fact n + n * fact n)%nat = (fact n * (n+1))%nat).
                           { lia. } rewrite H8.
                           apply Nat.mul_pos_pos. apply lt_O_fact. lia. 
                       *** assert ((fact n + n * fact n)%nat = (fact n * (n+1))%nat).
                           { lia. } rewrite H8. apply fact_low_bound; lia.
      ++ lia.
   * assert (sum_f_R0 (fun i : nat =>
                          INR (m ^ i) * u0 ^ i / INR (2 ^ i))  (m - 1) = 
             sum_f_R0 (fun i : nat => (INR m * u0 / INR 2)^i) (m-1)).
     { apply sum_eq. intros.
       rewrite !pow_INR. rewrite [in RHS]Rpow_mult_distr.
       rewrite Rpow_mult_distr. rewrite -Rinv_pow. nra.
       simpl; nra.
     } rewrite H2. clear H2.
     assert ((m - 1)%nat = (Init.Nat.pred m)). { lia. } rewrite H2.
     pose proof (GP_finite (INR m * u0 / INR 2) (Init.Nat.pred m) ).
     apply pow_invert_eq in H3.
     ++ rewrite H3.
        assert ((Init.Nat.pred m + 1)%nat = m). { lia. } rewrite H4.
        assert ((INR m * u0 * / ( INR m * u0 / INR 2 - 1)) *  
                  ((INR m * u0 / INR 2) ^ m - 1) < 2 -> 1 +
                  INR m * u0 *
                  (((INR m * u0 / INR 2) ^ m - 1) /
                   (INR m * u0 / INR 2 - 1)) < 3).
        { intros. nra. } apply H5. clear H5.
        assert (INR m * u0 * / (INR m * u0 / INR 2 - 1) *
                    ((INR m * u0 / INR 2) ^ m - 1) = 
                 INR m * u0 * / (1 - INR m * u0 / INR 2) *
                    (1 - (INR m * u0 / INR 2) ^ m )).
        { assert ((INR m * u0 / INR 2 - 1) = - ((1 - INR m * u0 / INR 2))).
          { nra. } rewrite H5.
          assert (((INR m * u0 / INR 2)^m - 1) = - ((1 - (INR m * u0 / INR 2)^m))).
          { nra. } rewrite H6. 
          rewrite -Ropp_inv_permute. 
          + nra.
          + pose proof (ratio_gt_0 m H). simpl in H7. unfold u0; simpl; nra.
        } rewrite H5.
        replace 2 with (2 * 1) by nra.
        apply Rmult_lt_compat.
        -- apply Rmult_le_pos.
           ** apply Rmult_le_pos; try apply pos_INR; try (unfold u0; simpl;nra).
           ** apply Rlt_le, Rinv_0_lt_compat. replace (1* 1) with 1 by nra.  apply ratio_gt_0. lia.
        -- assert ((INR m * u0 / INR 2) ^ m <= 1 -> 
                    0 <= 1 - (INR m * u0 / INR 2) ^ m).
           { nra. }  apply H6.
           assert (1 = 1^m). { by rewrite pow1. } rewrite H7.
           apply pow_incr. split.
           ** apply Rmult_le_pos.
              +++ apply Rmult_le_pos; try apply pos_INR; try (unfold u0;simpl;nra).
              +++ simpl;nra.
           ** assert (0 < (1 - INR m * u0 / INR 2) -> 
                        INR m * u0 / INR 2 <= 1).
              { nra. } apply H8. apply ratio_gt_0. lia.
        --  assert (2 = (2 * (1 - INR m * u0 / INR 2)) * / (1 - INR m * u0 / INR 2)).
            { match goal with |-context[_ = (?a * ?b) * ?c]=>
                replace ((a*b)*c) with (a * (b * c)) by nra
              end. rewrite Rinv_r.
              nra.
              pose proof (ratio_gt_0 m H). simpl in H6. unfold u0; simpl; nra.
            } rewrite H6.
            apply Rmult_lt_compat_r.
            ** apply Rinv_0_lt_compat,ratio_gt_0; lia.
            ** replace (INR 2) with 2 by (simpl;nra).
               assert (2 * (1 - INR m * u0 / 2) = 2 - INR m * u0).
               { nra. } rewrite H7.
               assert (INR m * u0 < 1 -> INR m * u0 < 2 - INR m * u0).
               { nra. } apply H8. 
               apply Rlt_le_trans with
               (INR (Z.to_nat (Z.pow_pos 2 23)) * u0).
               +++ apply Rmult_lt_compat_r. unfold u0;simpl;nra.
                   apply lt_INR;lia.
               +++  rewrite INR_IZR_INZ. 
                    assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
                    { lia. } rewrite H9. unfold u0;simpl;nra.
         -- assert ( 0 < (INR m * u0 / INR 2) ^ m ->
                     1 - (INR m * u0 / INR 2) ^ m < 1).
            { nra. } apply H6. apply x_pow_gt_0. 
            apply Rmult_lt_0_compat.
            ** apply Rmult_lt_0_compat.
               +++ apply lt_0_INR. lia.
               +++ unfold u0;simpl;nra.
            ** simpl;nra.
     ++ pose proof (ratio_gt_0 m H). simpl in H4. unfold u0; simpl; nra.
Qed.



(** Error bound for multiplication **)
Lemma prove_rndoff'' :
  forall (a b : ftype Tsingle) vmap n,
  (1 < n )%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (n < Z.to_nat (Z.pow_pos 2 23))%nat ->
  prove_roundoff_bound (@bmap_prod Tsingle n) (vmap a b) (@prod_expr Tsingle a b) 
     ( Rabs (rval (env_ (vmap a b)) (@prod_expr Tsingle a b)) * u0 + u).
Proof.
intros ? ? ? ? ? ? ? Hn.  
prove_roundoff_bound.
-
prove_rndval.
try apply Rabs_le in BOUND, BOUND0.
repeat rewrite Rmult_1_l. 
assert (Rabs (1 + u2) <= 1 + u0) as Hu2. 
{ unfold u0. simpl. 
  apply Rle_trans with 
  (Rabs 1 + Rabs u2). 
  + apply Rabs_triang.
  + rewrite Rabs_R1. apply Rplus_le_compat_l. nra.
}
apply Rlt_Rminus.
eapply real_lt_1; [eapply Rabs_triang | 
    rewrite Rabs_mult; eapply real_lt_1; [ eapply Rplus_le_compat; 
          [eapply Rmult_le_compat; try apply Rabs_pos; [ rewrite Rabs_mult ; apply Rmult_le_compat;
            try apply Rabs_pos; [ apply BOUND0 | apply BOUND ]
              | apply Hu2 ] | apply H0] | idtac]].
rewrite sqrt_sqrt.
simpl in  u , u0.
apply Rle_lt_trans with 
((F' / (1+u0) -
   / 2 * / IZR (Z.pow_pos 2 149)) * 
  (1 + u0) +
  / 2 *
  / 713623846352979940529142984724747568191373312).
+ assert (/ IZR (2 ^ 150) = / 2 * / 713623846352979940529142984724747568191373312).
  { nra. } rewrite H2. clear H2.  
  apply Rplus_le_compat_r. apply Rmult_le_compat_r.
  * unfold u0; simpl; nra.
  * apply Rplus_le_compat_r.
    apply Rmult_le_compat_l.
    unfold F', F_max; simpl; nra.
    assert (n=2%nat \/ (2 < n)%nat).
    { lia. } destruct H2.
    ++ rewrite H2. unfold u0; simpl; nra.
    ++ apply Rlt_le, Rinv_lt_contravar.
       -- apply Rmult_lt_0_compat.
          ** unfold u0; simpl; nra.
          ** apply Rmult_lt_0_compat.
             apply lt_0_INR. lia.
             apply x_pow_gt_0. simpl; nra.
       -- assert (1 + u0 = INR 1 * (1+u0)^1).
          { simpl; nra. } rewrite H3.
          assert ((INR 1 * (1 + u0) ^ 1) ^ n = (1+u0)^n).
          { by rewrite -H3. } rewrite H4.
          apply Rmult_lt_compat.
          ** simpl; nra.
          ** unfold u0; simpl; nra.
          ** apply lt_INR; lia.
          ** apply Rlt_pow. unfold u0;simpl;nra. lia.
+ unfold F', F_max, u0;simpl;nra.
+ apply Rge_le. apply Rge_minus. apply Rle_ge.
  simpl in u, u0. fold u u0.
  apply pow_invert.
  * apply Rmult_lt_0_compat. apply lt_0_INR. lia. 
    apply x_pow_gt_0. unfold u0; simpl; nra.
  * apply Rle_trans with 
    (u * (INR n * 3)).
    ++ repeat apply Rmult_le_compat_l.
       -- unfold u; simpl; nra.
       -- apply pos_INR.
       -- apply Rlt_le. 
          pose proof  (delta_bound n). specialize (H2 Hn).
          simpl in H2. fold u0 in H2.
          nra.
    ++ replace (u * (INR n * 3)) with (INR n * (3 * u)) by nra.
       apply pow_invert_1.
       -- unfold u;simpl;nra.
       -- apply Rle_trans with 
            (IZR (Z.pow_pos 2 23)).
          ** apply Rlt_le. rewrite INR_IZR_INZ. apply IZR_lt. lia.
          ** unfold u. simpl. unfold F', F_max; simpl; nra.
-
prove_roundoff_bound2.
apply Rabs_le in BOUND.
apply Rabs_le in BOUND0.
match goal with |- context[Rabs ?a <= _] =>
field_simplify a
end.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
replace (v_a * v_b * d) with ((v_a * v_b) * d) by nra.
rewrite Rabs_mult.
apply Rplus_le_compat_l.
apply E.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat; try apply Rabs_pos.
apply Rle_refl.
apply E0.
subst u0 u.
apply Rplus_le_compat; try simpl; try field_simplify; nra. 
Qed.


Lemma reflect_reify_prodF : 
  forall a b,
  fval (env_ (vmap a b)) (@prod_expr Tsingle a b) = prod Tsingle a b .
Proof. reflexivity. Qed.

Lemma reflect_reify_prodR : 
  forall a b,
  rval (env_ (vmap a b)) (@prod_expr Tsingle a b) = FT2R a * FT2R b .
Proof. reflexivity. Qed.


Lemma prove_rndoff_prod:
  forall (a b : ftype Tsingle) (n : nat),
  let ty:= Tsingle in let nr := INR n in 
  ( 1 < n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (n < Z.to_nat (Z.pow_pos 2 23))%nat ->
  boundsmap_denote (@bmap_prod Tsingle n) (vmap a b) ->
   Rabs (FT2R (prod Tsingle a b) - (FT2R a * FT2R b)) <= 
     ( Rabs ( FT2R a * FT2R b ) * u0 + u) .
Proof.
intros ? ? ? ? ? Hn ? ? ? HBMD.
pose proof prove_rndoff'' a b vmap n Hn H HBMD.
unfold roundoff_error_bound in H0.
rewrite <- reflect_reify_prodR.
rewrite <- reflect_reify_prodF.
destruct H0 as (H1 & H2); try apply H2.
Qed.


Lemma sum_abs_ge_0:
  forall (L1 : list (ftype Tsingle)) ,
  0 <= sum_fixR (Flist_to_Rlist_abs L1).
Proof.
intros.
induction L1.
+ simpl. nra.
+ simpl. apply Rplus_le_le_0_compat.
  apply Rabs_pos. apply IHL1.
Qed.

Lemma u_bound:
  forall (m:nat) (u:R),
  0 < u -> 
  (1 < m)%nat -> 
  u <= (1+u)^m - 1.
Proof.
intros.
induction m.
+ contradict H0. lia.
+ simpl.
  assert (m = 1%nat \/ (1< m)%nat). { lia. } destruct H1.
  - rewrite H1. nra.
  - specialize (IHm H1).
    assert ((1 + u) * ((1 + u) ^ m) - 1 = 
          (1 + u) * ((1 + u) ^ m - 1) + u).
    { nra. } rewrite H2.
    apply Rle_trans with ((1+u) * u + u).
    * nra.
    * apply Rplus_le_compat_r.
      apply Rmult_le_compat_l.
      nra. nra.
Qed.



Lemma Rabs_ineq:
 forall x a:R, Rabs x <= a -> -a <= x <= a.
Proof.
intros.
destruct H.
+ apply Rabs_def2 in H. nra.
+ pose proof (Rcase_abs x) as Hr.
  destruct Hr.
  - rewrite Rabs_left in H; nra. 
  - rewrite Rabs_right in H; nra.
Qed.


Lemma Rabs_triang_inv_impl: 
  forall x y z:R, 
  Rabs (x - y) <= z ->Rabs x - Rabs y <= z.
Proof.
intros. apply Rle_trans with (Rabs (x - y)). 
apply Rabs_triang_inv . nra.
Qed.


Lemma list_sum:
  forall (L1 : list (ftype Tsingle)) (x:R) (n:nat),
  0 <= x ->
  (forall a: ftype Tsingle,
          In a L1 ->
          Rabs (FT2R a) <= x / INR n) ->
  sum_fixR (Flist_to_Rlist_abs L1) <= x  * (INR (length L1)) / (INR n).
Proof.
intros.
induction L1.
+ simpl. nra.
+ assert (sum_fixR (Flist_to_Rlist_abs (a :: L1)) = 
            Rabs (FT2R a) +  sum_fixR (Flist_to_Rlist_abs L1)).
  { by simpl. } rewrite H1.
  assert (forall a : ftype Tsingle,
            In a L1 ->
            Rabs (FT2R a) <= x / INR n).
  { intros.
    specialize (H0 a0).
    assert (In a0 (a :: L1)). { simpl. auto. } specialize (H0 H3).
    apply H0.
  } specialize (IHL1 H2).
  specialize (H0 a).
  assert (In a (a :: L1)). { simpl. auto. } specialize (H0 H3).
  apply Rle_trans with
  ( x / INR n + x * INR (length L1) / INR n).
  - apply Rplus_le_compat; nra. 
  - assert (INR (length (a :: L1)) = INR (length L1) + 1).
    { simpl. 
      destruct (length L1).
      + simpl. nra.
      + nra.
    } rewrite H4. nra.
Qed.


Lemma lenght_elem {ty : Type}:
  forall (l : list ty),
  length l = 1%nat ->
  exists a, l = [a].
Proof.
intros. destruct l.
+ contradict H. simpl. lia.
+ exists t. 
  assert (l = [:: ] \/ l <> [::]).
  { destruct l.
    + by left.
    + by right. 
  } destruct H0.
  - rewrite H0. auto.
  - contradict H. simpl. destruct l.
    * contradict H0. auto.
    * simpl. auto.
Qed.
  

Lemma float_FT2R_real: 
  forall L1: list (ftype Tsingle), 
  length L1 = 1%nat ->
  FT2R (sum_fixF Tsingle L1) = sum_fixR (Flist_to_Rlist L1).
Proof.
intros. 
pose proof (lenght_elem L1 H).
destruct H0 as [a H0].
rewrite H0. simpl. auto. nra.
Qed.


Lemma lenght_elem_gt_1 {ty : Type}:
  forall (l : list ty),
  (length l > 1)%nat ->
  exists a b, l = [a] ++ b /\ (length b >=1)%nat .
Proof.
intros. destruct l.
+ contradict H. simpl. lia.
+ exists t, l.  simpl. split.
  - auto.
  - destruct l.
    * simpl in H. contradict H. lia.
    * simpl. lia.
Qed.



Lemma prove_rndoff_n_sum_aux :
  forall (L1 : list (ftype Tsingle)) ,
  let n:= length L1 in 
  (1 < n )%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (n < Z.to_nat (Z.pow_pos 2 23))%nat ->
  (forall a : ftype Tsingle,
              In a L1 ->
              Binary.is_finite (fprec Tsingle) (femax Tsingle) a = true /\
              Rabs (FT2R a) <=  (F' / (INR (n+1) * (1+u0)^(n+1)))) ->
  is_finite (fprec Tsingle) (femax Tsingle)
  (sum_fixF Tsingle L1) = true /\
  Rabs (FT2R (sum_fixF Tsingle L1) - sum_fixR (Flist_to_Rlist L1)) <= 
      (sum_fixR (Flist_to_Rlist_abs L1)) * ((1 + u0)^(n-1) - 1) + 
      u * ((1 + u0)^(n-1) - 1) / u0.
Proof.
intros ? ? ? ? ? ? Ha.
induction L1.
+ simpl. rewrite Rminus_0_r. rewrite Rabs_R0. 
  assert ((1 - 1) = 0). { nra. } rewrite H1. nra.
+ (*simpl in IHL1. *)
  remember (length L1) as m.
  assert (n = (m+1)%nat). { unfold n. simpl. rewrite Heqm. lia. }
  assert (L1 = [:: ] \/ L1 <> [::]).
  { destruct L1.
    + by left.
    + by right. 
  } destruct H2.
  - rewrite H2 in Heqm. simpl in Heqm. rewrite Heqm in H1.
    simpl in H1. rewrite H1 in H. contradict H. lia.
  - simpl.
    assert ((1 <= m)%nat).
    { rewrite Heqm. destruct L1.
      + by contradict H2.
      + simpl. lia.
    } assert (m = 1%nat \/ (1 < m)%nat). { lia.  } 
    destruct H4.
    * rewrite H4 in Heqm. rewrite -Heqm. simpl.
      rewrite Rmult_1_r. 
      pose proof (prove_rndoff a (sum_fixF Tsingle L1) 2%nat).
      simpl in H5.
      assert ((1 < 2)%nat). { lia. } specialize (H5 H6).
      assert (boundsmap_denote (@bmap  Tsingle 2)
                  (vmap a (sum_fixF Tsingle L1))).
      { apply boundsmap_denote_i.
         2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
         repeat apply list_forall_cons; try apply list_forall_nil;
          (eexists; split; [|split;[|split]]; try reflexivity; auto;
            try unfold List.nth; try nra; auto).
        + symmetry in Heqm. 
          pose proof (lenght_elem L1 Heqm).
          destruct H7 as [b H7]. rewrite H7. simpl.
          specialize (Ha b). rewrite H7 in Ha.
          assert ( In b [a; b]). { simpl. auto. } specialize (Ha H8).
          apply Ha.
        + apply Rabs_ineq. symmetry in Heqm.
          pose proof (lenght_elem L1 Heqm).
          destruct H7 as [b H7].
          rewrite H7. simpl. rewrite H7 in Ha.
          specialize (Ha b). simpl in u,u0. fold u u0.
          assert ( In b [a; b]). { simpl; auto. }
          specialize (Ha H8). 
          rewrite H4 in H1. simpl in H1. rewrite H1 in Ha.
          apply Rle_trans with 
          (F' / (INR (2 + 1) * (1 + u0) ^ (2 + 1))).
          - nra.
          - match goal with |-context[?a <= _]=>
            replace a with (a+0) by nra
            end. apply Rplus_le_compat.
            * assert ( F' * (1 + 1 - 1) / (1 + 1) = F' / 2). 
              { nra. } rewrite H9. apply Rmult_le_compat_l.
              ++ unfold F', F_max; simpl; nra.
              ++ unfold u0; simpl; nra.
            * unfold u,u0; simpl; nra.
        + specialize (Ha a). 
          assert (In a (a :: L1)). { simpl. auto. }
          specialize (Ha H7). apply Ha.
        + apply Rabs_ineq. specialize (Ha a).
          assert (In a (a :: L1)).
          { simpl; auto. } specialize (Ha H7).
          assert ( n = 2%nat).
          { unfold n. simpl. auto. } rewrite H8 in Ha.
          unfold u0 in Ha. 
          apply Rle_trans with 
          ( F' /
             (INR (2 + 1) *
              (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))
              ^ (2 + 1))).
          - nra.
          - unfold F', F_max, u0. simpl; nra. 
     } specialize (H5 H7). 
     symmetry in Heqm.
     pose proof (lenght_elem L1 Heqm).
     destruct H8 as [b H8]. rewrite H8. simpl. rewrite H8 in H5.
     simpl in H5. rewrite !Rplus_0_r.
     assert( (u * (1 + u0 - 1) / u0) = (/ 2 * / IZR (Z.pow_pos 2 149))).
     { unfold u, u0. simpl; nra. } rewrite H9.
     assert ((1 + u0 - 1) = (/ 2 * / IZR (Z.pow_pos 2 23))).
     { by unfold u0; simpl; nra. } rewrite H10. split.
     ** destruct (prove_rndoff' a b vmap 2%nat).
        +++ lia.
        +++ apply boundsmap_denote_i.
               2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
               repeat apply list_forall_cons; try apply list_forall_nil;
                (eexists; split; [|split;[|split]]; try reflexivity; auto;
                  try unfold List.nth; try nra; auto).
            --- apply Ha. rewrite H8. simpl; auto. 
            --- apply Rabs_ineq. specialize (Ha b).
               assert (In b [a; b]). { simpl; auto. } rewrite H8 in Ha. specialize (Ha H11).
               destruct Ha.
               apply Rle_trans with 
               (F' / (INR (n + 1) * (1 + u0) ^ (n + 1))).
               -- nra.
               -- match goal with |-context[ ?a <= _ ]=>
                    replace a with (a+ 0) by nra
                  end. apply Rplus_le_compat.
                  *** assert (F' * (INR 2 - 1) / INR 2 = F' *( (INR 2 - 1) / INR 2)).
                     { nra. } rewrite H14.
                     apply Rmult_le_compat_l.
                      unfold F', F_max; simpl; nra.
                      apply Rlt_le. 
                      assert ((INR 2 - 1) / INR 2 = / INR 2). { simpl;nra. }
                      rewrite H15. rewrite Rinv_mult_distr.
                      ---- assert (/ INR 2 = / INR 2 * / 1). { nra. } rewrite H16.
                          apply Rmult_lt_compat.
                          **** apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR;lia.
                          **** apply Rlt_le, Rinv_0_lt_compat. apply x_pow_gt_0. 
                              unfold u0; simpl; nra.
                          **** apply Rinv_lt_contravar. apply Rmult_lt_0_compat.
                              simpl;nra. apply lt_0_INR;lia. apply lt_INR. lia.
                          **** apply Rinv_lt_contravar. 
                              apply Rmult_lt_0_compat. nra. 
                              apply x_pow_gt_0. unfold u0;simpl;nra.
                              apply Rlt_pow_R1. unfold u0;simpl;nra. lia.
                      ---- apply not_0_INR. lia.
                      ---- apply pow_nonzero.  unfold u0;simpl;nra.
                  *** simpl; nra.
             --- apply Ha. simpl;auto.
             --- apply Rabs_ineq. specialize (Ha a).
                 assert (In a (a :: L1)). { simpl;auto. } specialize (Ha H11).
                 destruct Ha as [ifHa Ha].
                 apply Rle_trans with 
                 (F' / (INR (n + 1) * (1 + u0) ^ (n + 1))).
                 ---- nra.
                 ---- apply Rle_trans with (F' /(INR 2 *
                                             (1 + / 2 *  bpow Zaux.radix2
                                                  (- fprec Tsingle + 1)) ^ 2)).
                      **** apply Rmult_le_compat_l.
                            unfold F', F_max; simpl; nra.
                            apply Rlt_le.
                            apply Rinv_lt_contravar. 
                            *** apply Rmult_lt_0_compat. unfold u0; simpl; nra.
                               apply Rmult_lt_0_compat.
                               apply lt_0_INR;lia. 
                               apply x_pow_gt_0. unfold u0;simpl;nra.
                            *** apply Rmult_lt_compat.
                               simpl; nra. unfold u0; simpl; nra.
                               apply lt_INR;lia. apply Rlt_pow. 
                               unfold u0;simpl;nra. lia. 
                      **** simpl;nra.
           +++ auto.
     ** apply Rle_trans with 
       (Rabs (FT2R a + FT2R b) *
           (/ 2 * / IZR (Z.pow_pos 2 23)) +
           / 2 * / IZR (Z.pow_pos 2 149)).
       ++ nra.
       ++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
          nra. apply Rabs_triang.
   * assert ( match L1 with
               | [] => a
               | (_ :: _)%SEQ =>
                   sum Tsingle a (sum_fixF Tsingle L1)
               end  = sum Tsingle a (sum_fixF Tsingle L1)).
     { pose proof (lenght_elem_gt_1 L1).
       assert ((length L1 > 1)%nat). { lia. } specialize (H5 H6). clear H6.
       destruct H5 as [b [L2 H5]]. destruct H5 as [H5 LH5].
       rewrite H5. simpl. auto.
     } rewrite H5. clear H5.
     specialize (IHL1 H4).
     assert ((m < Z.to_nat (Z.pow_pos 2 23))%nat).
     { apply lt_trans with n. lia. lia. } specialize (IHL1 H5).
    assert (forall a : ftype Tsingle,
              In a L1 ->
              Binary.is_finite (fprec Tsingle)
                (femax Tsingle) a = true /\
              Rabs (FT2R a) <=
              F' / (INR n * (1 + u0) ^ n)).
    { intros. specialize (Ha a0).
      assert (In a0 (a :: L1)).
      { simpl. right. auto.
      } apply Ha in H7. split. apply H7.
      apply Rle_trans with 
      (F' / (INR (n+1) * (1 + u0) ^ (n+1))).
      nra. apply Rmult_le_compat_l.
      unfold F', F_max; simpl; nra.
      apply Rlt_le. apply Rinv_lt_contravar.
      + rewrite Rmult_assoc. apply Rmult_lt_0_compat.
        - apply lt_0_INR. lia.
        - apply Rmult_lt_0_compat. apply x_pow_gt_0.
          unfold u0; simpl; nra.
          apply Rmult_lt_0_compat. apply lt_0_INR; lia.
          apply x_pow_gt_0. unfold u0; simpl; nra.
      + apply Rmult_lt_compat.
        - apply pos_INR.
        - apply Rlt_le.
          apply x_pow_gt_0. unfold u0; simpl; nra.
        - apply lt_INR. lia.
        - apply Rlt_pow. unfold u0; simpl; nra. lia.
    } rewrite -H1 in IHL1. specialize (IHL1 H6).
    split.
    ** destruct (prove_rndoff' a (sum_fixF Tsingle L1) vmap n).
       +++ lia.
       +++ apply boundsmap_denote_i.
           2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
           repeat apply list_forall_cons; try apply list_forall_nil;
            (eexists; split; [|split;[|split]]; try reflexivity; auto;
              try unfold List.nth; try nra; auto).
           --- apply IHL1.
           --- apply Rabs_ineq. destruct IHL1 as [ifHL IHL1].
               apply Rabs_triang_inv_impl in IHL1.
               assert (forall x y z:R, x - y <= z -> x <= y + z).
               { intros. nra. } apply H7 in IHL1.
               apply Rle_trans with
               (sum_fixR (Flist_to_Rlist_abs L1) +
                 (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                  u * ((1 + u0) ^ (m-1) - 1) / u0)).
               *** apply Rle_trans with 
                   (Rabs (sum_fixR (Flist_to_Rlist L1)) +
                     (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                      u * ((1 + u0) ^ (m-1) - 1) / u0)).
                  ++++ nra.
                  ++++ apply Rplus_le_compat_r. apply Rabs_list_rel.
               *** match goal with |-context[?a + (?a * ?b + ?c) <= _] =>
                  replace (a + (a * b + c)) with (a * (1+b) + c) by nra
                 end. 
                 assert (sum_fixR (Flist_to_Rlist_abs L1) <= 
                          F' / 
                           (1 + u0) ^ n * (INR (length L1)) / (INR n)).
                 { apply (list_sum L1 (F' / ( (1 + u0) ^ n)) n).
                   apply Rmult_le_pos. unfold F', F_max; simpl; nra.
                   apply Rlt_le. apply Rinv_0_lt_compat. apply x_pow_gt_0.
                   unfold u0; simpl; nra.
                   assert (F' / (1 + u0) ^ n / INR n = 
                            F' / (INR n * (1 + u0) ^ n)).
                   { assert (/ (INR n * (1 + u0) ^ n) = / INR n * / (1+u0)^n).
                     { apply Rinv_mult_distr. apply not_0_INR. lia.
                       apply pow_nonzero . unfold u0; simpl; nra.
                     }
                     assert (F' / (INR n * (1 + u0) ^ n) = F' * /(INR n * (1 + u0) ^ n)).
                     { nra. } rewrite H9. rewrite H8. nra.
                   } rewrite H8. auto. apply H6.
                 } rewrite -Heqm in H8.
                 apply Rplus_le_compat.
                 ++++ assert ((1 + ((1 + u0) ^ (m-1) - 1)) = (1+u0)^(m-1)).
                   { nra. } rewrite H9. 
                   apply Rle_trans with 
                    ((F' / (1 + u0) ^ n * INR m / INR n) * (1+u0)^(m-1)).
                   ++ apply Rmult_le_compat_r.
                      -- apply Rlt_le. apply x_pow_gt_0. unfold u0;simpl;nra.
                      -- nra.
                   ++ assert ((INR n - 1) = INR m).
                      { rewrite H1. rewrite plus_INR. simpl;nra. }
                      rewrite H10. 
                      assert (F' / (1 + u0) ^ n * INR m / INR n * (1 + u0) ^ (m-1) = 
                                (F'* (1+u0)^(m-1) / (1+u0)^n) * (INR m / INR n)).
                      { nra. } rewrite H11. 
                      match goal with |-context[_ <= ?a * ?b / ?c]=>
                        replace (a * b / c) with (a * (b / c)) by nra
                      end.  apply Rmult_le_compat_r.
                      -- apply Rmult_le_pos. apply pos_INR. 
                         apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR.
                         lia.
                      -- replace F' with (F' * 1) by nra.
                         replace (F' * 1 * (1 + u0) ^ (m-1) / (1 + u0) ^ n)
                         with (F' * ((1+u0)^(m-1) / (1+u0)^n)) by nra.
                         apply Rmult_le_compat_l. unfold F', F_max;simpl;nra.
                         assert (1 = (1+u0)^n / (1+u0)^n).
                         { symmetry. apply Rinv_r. apply pow_nonzero.
                           unfold u0; simpl; nra.
                         } rewrite H12.
                         assert (((1 + u0) ^ n / (1 + u0) ^ n + u0) ^ (m-1) /
                                    ((1 + u0) ^ n / (1 + u0) ^ n + u0) ^ n = 
                                  (1+u0)^(m-1) / (1+u0)^n).
                         { by rewrite -H12. } rewrite H13.
                         apply Rmult_le_compat_r. 
                         apply Rlt_le, Rinv_0_lt_compat.
                         apply x_pow_gt_0. unfold u0; simpl; nra.
                         apply Rlt_le. apply Rlt_pow. 
                         unfold u0; simpl; nra. lia. 
                  ++++ assert (u * ((1 + u0) ^ (m-1) - 1) / u0 = ((1+u0)^(m-1)-1) * (u/u0)).
                      { nra. } rewrite H9. fold u u0.
                      assert (2 * u / u0 = 2 * (u/u0)).
                      { nra. } rewrite H10. apply Rmult_le_compat_r.
                      unfold u, u0; simpl; nra.
                      apply Rlt_le, delta_bound.
                      apply lt_trans with m; lia. 
           --- apply Ha. simpl;auto.
           --- apply Rabs_ineq. fold u0. specialize (Ha a).
              assert (In a (a :: L1)). { simpl; auto. } specialize (Ha H7).
              apply Rle_trans with 
              (F' / (INR (n + 1) * (1 + u0) ^ (n + 1))).
              *** nra.
              *** apply Rle_trans with (F' / (INR n * (1 + u0) ^ n)).
                  apply Rmult_le_compat_l. unfold F', F_max; simpl; nra.
                  apply Rlt_le. apply Rinv_lt_contravar. 
                ++++ apply Rmult_lt_0_compat.
                  ++ apply Rmult_lt_0_compat.
                     -- apply lt_0_INR. lia.
                     -- apply x_pow_gt_0. unfold u0; simpl; nra.
                  ++ apply Rmult_lt_0_compat. 
                     -- apply lt_0_INR. lia.
                     -- apply x_pow_gt_0. unfold u0; simpl; nra.
                ++++ apply Rmult_lt_compat.
                  ++ apply pos_INR.
                  ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                  ++ apply lt_INR. lia.
                  ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                ++++  unfold u0; simpl;nra.
       +++ auto.
    ** apply Rle_trans with
       (Rabs(FT2R (sum Tsingle a (sum_fixF Tsingle L1)) -
                (FT2R a + FT2R (sum_fixF Tsingle L1))) + 
        Rabs ((FT2R a + FT2R (sum_fixF Tsingle L1)) -
               (FT2R a + sum_fixR (Flist_to_Rlist L1)))).
        -- assert ((FT2R (sum Tsingle a (sum_fixF Tsingle L1)) -
                        (FT2R a + sum_fixR (Flist_to_Rlist L1))) = 
                      (FT2R (sum Tsingle a (sum_fixF Tsingle L1)) - 
                        (FT2R a + FT2R (sum_fixF Tsingle L1))) + 
                      ((FT2R a + FT2R (sum_fixF Tsingle L1)) - 
                       (FT2R a + sum_fixR (Flist_to_Rlist L1)))).
           { nra. } rewrite H7. apply Rabs_triang.
        -- destruct IHL1 as [ifH IHL1].
           pose proof (prove_rndoff a (sum_fixF Tsingle L1) n).
           specialize (H7 H). simpl in H7.
           assert (boundsmap_denote (@bmap Tsingle n)
                          (vmap a (sum_fixF Tsingle L1))).
           { apply boundsmap_denote_i.
             2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
             repeat apply list_forall_cons; try apply list_forall_nil;
              (eexists; split; [|split;[|split]]; try reflexivity; auto;
                try unfold List.nth; try nra; auto).
             + apply Rabs_ineq. 
               apply Rabs_triang_inv_impl in IHL1.
               assert (forall x y z:R, x - y <= z -> x <= y + z).
               { intros. nra. } apply H8 in IHL1.
               apply Rle_trans with
               (sum_fixR (Flist_to_Rlist_abs L1) +
                 (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                  u * ((1 + u0) ^ (m-1) - 1) / u0)).
               - apply Rle_trans with 
                 (Rabs (sum_fixR (Flist_to_Rlist L1)) +
                   (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                    u * ((1 + u0) ^ (m-1) - 1) / u0)).
                  * nra.
                  * apply Rplus_le_compat_r. apply Rabs_list_rel.
               - match goal with |-context[?a + (?a * ?b + ?c) <= _] =>
                  replace (a + (a * b + c)) with (a * (1+b) + c) by nra
                 end. 
                 assert (sum_fixR (Flist_to_Rlist_abs L1) <= 
                          F' / 
                           (1 + u0) ^ n * (INR (length L1)) / (INR n)).
                 { apply (list_sum L1 (F' / ( (1 + u0) ^ n)) n).
                   apply Rmult_le_pos. unfold F', F_max; simpl; nra.
                   apply Rlt_le. apply Rinv_0_lt_compat. apply x_pow_gt_0.
                   unfold u0; simpl; nra.
                   assert (F' / (1 + u0) ^ n / INR n = 
                            F' / (INR n * (1 + u0) ^ n)).
                   { assert (/ (INR n * (1 + u0) ^ n) = / INR n * / (1+u0)^n).
                     { apply Rinv_mult_distr. apply not_0_INR. lia.
                       apply pow_nonzero . unfold u0; simpl; nra.
                     }
                     assert (F' / (INR n * (1 + u0) ^ n) = F' * /(INR n * (1 + u0) ^ n)).
                     { nra. } rewrite H10. rewrite H9. nra.
                   } rewrite H9. auto. apply H6.
                 } rewrite -Heqm in H9.
                 apply Rplus_le_compat.
                 * assert ((1 + ((1 + u0) ^ (m-1) - 1)) = (1+u0)^(m-1)).
                   { nra. } rewrite H10. 
                   apply Rle_trans with 
                    ((F' / (1 + u0) ^ n * INR m / INR n) * (1+u0)^(m-1)).
                   ++ apply Rmult_le_compat_r.
                      -- apply Rlt_le. apply x_pow_gt_0. unfold u0;simpl;nra.
                      -- nra.
                   ++ assert ((INR n - 1) = INR m).
                      { rewrite H1. rewrite plus_INR. simpl;nra. }
                      rewrite H11. 
                      assert (F' / (1 + u0) ^ n * INR m / INR n * (1 + u0) ^ (m-1) = 
                                (F'* (1+u0)^(m-1) / (1+u0)^n) * (INR m / INR n)).
                      { nra. } rewrite H12. 
                      match goal with |-context[_ <= ?a * ?b / ?c]=>
                        replace (a * b / c) with (a * (b / c)) by nra
                      end.  apply Rmult_le_compat_r.
                      -- apply Rmult_le_pos. apply pos_INR. 
                         apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR.
                         lia.
                      -- replace F' with (F' * 1) by nra.
                         replace (F' * 1 * (1 + u0) ^ (m-1) / (1 + u0) ^ n)
                         with (F' * ((1+u0)^(m-1) / (1+u0)^n)) by nra.
                         apply Rmult_le_compat_l. unfold F', F_max;simpl;nra.
                         assert (1 = (1+u0)^n / (1+u0)^n).
                         { symmetry. apply Rinv_r. apply pow_nonzero.
                           unfold u0; simpl; nra.
                         } rewrite H13.
                         assert (((1 + u0) ^ n / (1 + u0) ^ n + u0) ^ (m-1) /
                                    ((1 + u0) ^ n / (1 + u0) ^ n + u0) ^ n = 
                                  (1+u0)^(m-1) / (1+u0)^n).
                         { by rewrite -H13. } rewrite H14.
                         apply Rmult_le_compat_r. 
                         apply Rlt_le, Rinv_0_lt_compat.
                         apply x_pow_gt_0. unfold u0; simpl; nra.
                         apply Rlt_le. apply Rlt_pow. 
                         unfold u0; simpl; nra. lia. 
                  * assert (u * ((1 + u0) ^ (m-1) - 1) / u0 = ((1+u0)^(m-1)-1) * (u/u0)).
                    { nra. } rewrite H10. fold u u0.
                    assert (2 * u / u0 = 2 * (u/u0)).
                    { nra. } rewrite H11. apply Rmult_le_compat_r.
                    unfold u, u0; simpl; nra.
                    apply Rlt_le, delta_bound.
                    apply lt_trans with m; lia.
              + specialize (Ha a). apply Ha. simpl; auto.
            + apply Rabs_ineq. fold u0. specialize (Ha a).
              assert (In a (a :: L1)). { simpl; auto. } specialize (Ha H8).
              apply Rle_trans with 
              (F' / (INR (n + 1) * (1 + u0) ^ (n + 1))).
              - nra.
              - apply Rle_trans with (F' / (INR n * (1 + u0) ^ n)).
                apply Rmult_le_compat_l. unfold F', F_max; simpl; nra.
                apply Rlt_le. apply Rinv_lt_contravar. 
                * apply Rmult_lt_0_compat.
                  ++ apply Rmult_lt_0_compat.
                     -- apply lt_0_INR. lia.
                     -- apply x_pow_gt_0. unfold u0; simpl; nra.
                  ++ apply Rmult_lt_0_compat. 
                     -- apply lt_0_INR. lia.
                     -- apply x_pow_gt_0. unfold u0; simpl; nra.
                * apply Rmult_lt_compat.
                  ++ apply pos_INR.
                  ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                  ++ apply lt_INR. lia.
                  ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                * unfold u0;simpl;nra.
           } specialize (H7 H8).
           apply Rle_trans with 
           ( (Rabs (FT2R a + FT2R (sum_fixF Tsingle L1)) *
               (/ 2 * / IZR (Z.pow_pos 2 23)) +
               / 2 * / IZR (Z.pow_pos 2 149)) + 
             ( sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                 u * ((1 + u0) ^ (m-1) - 1) / u0)).
           *** apply Rplus_le_compat.
              +++ apply H7.
              +++ assert ((FT2R a + FT2R (sum_fixF Tsingle L1) -
                            (FT2R a + sum_fixR (Flist_to_Rlist L1))) = 
                          FT2R (sum_fixF Tsingle L1) - 
                          sum_fixR (Flist_to_Rlist L1)).
                 { nra. } rewrite H9. apply IHL1.
           *** apply Rle_trans with 
              ((Rabs (FT2R a) + Rabs (FT2R (sum_fixF Tsingle L1))) *
                (/ 2 * / IZR (Z.pow_pos 2 23)) +
                / 2 * / IZR (Z.pow_pos 2 149) +
                (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                 u * ((1 + u0) ^ (m-1) - 1) / u0)).
              +++ repeat apply Rplus_le_compat. apply Rmult_le_compat_r.
                 nra. apply Rabs_triang. nra. nra. nra.
              +++ assert (Rabs (FT2R (sum_fixF Tsingle L1)) - 
                         Rabs (sum_fixR (Flist_to_Rlist L1)) <= 
                         sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                          u * ((1 + u0) ^ (m-1) - 1) / u0).
                 { apply Rle_trans with (Rabs
                                 (FT2R (sum_fixF Tsingle L1) -
                                  sum_fixR (Flist_to_Rlist L1))).
                   apply Rabs_triang_inv. nra.
                 } 
                 assert (Rabs (FT2R (sum_fixF Tsingle L1)) <=
                              Rabs (sum_fixR (Flist_to_Rlist L1)) + 
                              sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                              u * ((1 + u0) ^ (m-1) - 1) / u0).
                 { nra. } 
                 assert (Rabs (FT2R (sum_fixF Tsingle L1)) <=
                         sum_fixR (Flist_to_Rlist_abs L1) + 
                         sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                          u * ((1 + u0) ^ (m-1) - 1) / u0).
                 { apply Rle_trans with 
                    (Rabs (sum_fixR (Flist_to_Rlist L1)) +
                       sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                       u * ((1 + u0) ^ (m-1) - 1) / u0).
                   + nra.
                   + repeat apply Rplus_le_compat_r. apply Rabs_list_rel.
                 } 
                 apply Rle_trans with 
                 ((Rabs (FT2R a) + 
                   (sum_fixR (Flist_to_Rlist_abs L1) +
                         sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                         u * ((1 + u0) ^ (m-1) - 1) / u0))*
                    (/ 2 * / IZR (Z.pow_pos 2 23)) +
                    / 2 * / IZR (Z.pow_pos 2 149) +
                    (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                     u * ((1 + u0) ^ (m-1) - 1) / u0)).
                  --- repeat apply Rplus_le_compat_r. apply Rmult_le_compat_r; nra.
                  --- assert ((Rabs (FT2R a) +
                               (sum_fixR (Flist_to_Rlist_abs L1) +
                                sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                                u * ((1 + u0) ^ (m-1) - 1) / u0)) *
                              (/ 2 * / IZR (Z.pow_pos 2 23)) +
                              / 2 * / IZR (Z.pow_pos 2 149) +
                              (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ (m-1) - 1) +
                               u * ((1 + u0) ^ (m-1) - 1) / u0) = 
                              (Rabs (FT2R a) * (/ 2 * / IZR (Z.pow_pos 2 23))) +
                              (sum_fixR (Flist_to_Rlist_abs L1) *
                                ((/ 2 * / IZR (Z.pow_pos 2 23)) + 
                                  (/ 2 * / IZR (Z.pow_pos 2 23)) * ((1 + u0) ^ (m-1) - 1)+
                                  ((1 + u0) ^ (m-1) - 1)) +
                               (((/ 2 * / IZR (Z.pow_pos 2 149)) +  u * ((1 + u0) ^ (m-1) - 1) / u0) +
                                 (/ 2 * / IZR (Z.pow_pos 2 23)) * (u * ((1 + u0) ^ (m-1) - 1) / u0)))).
                      { nra. } rewrite -Heqm H12. clear H12.
                      assert ((m-0)%nat = m). { lia. } rewrite H12. clear H12.
                      assert ((Rabs (FT2R a) + sum_fixR (Flist_to_Rlist_abs L1)) *
                                ((1 + u0) ^ m - 1) +
                                u * ((1 + u0) ^ m - 1) / u0 = 
                              (Rabs (FT2R a) * ((1 + u0) ^ m - 1)) +
                              (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                               u * ((1 + u0) ^ m - 1) / u0)).
                      { nra. } rewrite H12. clear H12.
                      repeat apply Rplus_le_compat.
                      **** apply Rmult_le_compat_l.
                          apply Rabs_pos.
                          simpl in u, u0. rewrite -/u -/u0.  
                          apply u_bound. unfold u0. nra. lia.
                      **** apply Rmult_le_compat_l.
                          ---- apply sum_abs_ge_0.
                          ---- simpl in u, u0. fold u u0. 
                               assert (u0 + u0 * ((1 + u0) ^ (m - 1) - 1) = 
                                          u0 * (1+u0)^(m-1)). { nra. } rewrite H12.
                               assert (u0 * (1 + u0) ^ (m - 1) + ((1 + u0) ^ (m - 1) - 1) =
                                          (1+u0) * (1+u0)^(m-1) - 1).
                               { nra. } rewrite H13.
                               assert ( m = S (m-1)). { lia. } rewrite H14. simpl.
                               assert ((m - 1 - 0)%nat = (m-1)%nat). { lia. } rewrite H15.
                               nra. 
                      **** simpl in u, u0. fold u u0.
                          assert ( m = S (m-1)). { lia. } rewrite H12. simpl.
                          assert ((m - 1 - 0)%nat = (m-1)%nat). { lia. } rewrite H13.
                          assert (u + u * ((1 + u0) ^ (m - 1) - 1) / u0 +
                                      u0 * (u * ((1 + u0) ^ (m - 1) - 1) / u0) = 
                                  u + u * ((1+u0) * ((1 + u0) ^ (m - 1) - 1)) / u0).
                          { nra. } rewrite H14.
                          assert (u + u * ((1 + u0) * ((1 + u0) ^ (m - 1) - 1)) / u0 = 
                                   (u * u0) / u0 + u * ((1 + u0) * ((1 + u0) ^ (m - 1) - 1)) / u0).
                          { assert ( (u * u0) / u0 = u). { unfold u, u0; simpl; nra. }
                            rewrite H15. nra.
                          } rewrite H15.
                          assert (u * u0 / u0 +
                                    u * ((1 + u0) * ((1 + u0) ^ (m - 1) - 1)) / u0 = 
                                   u * (u0 + ((1 + u0) * ((1 + u0) ^ (m - 1) - 1))) / u0).
                          { nra. } rewrite H16. nra.
Qed.



Lemma x_pow: forall (x:R) (n:nat),
  0 <= x ->
  0 <= x^n.
Proof.
intros. 
induction n.
+ simpl. nra.
+ simpl. apply Rmult_le_pos; nra.
Qed.


Lemma x_pow_minus_1: forall (x:R) (n:nat),
  1 <= x ->
  0 <= x^n - 1.
Proof.
intros. 
induction n.
+ simpl. nra.
+ simpl.
  assert (x * x ^ n - 1 = x * (x^n - 1) + (x - 1)).
  { nra. } rewrite H0.
  apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos. nra. nra.
  - nra.
Qed.

Definition Flist_to_Rlist_pair {ty} (L : list ( (ftype ty) * (ftype ty))) :=
  map (fun a => (FT2R (fst a), FT2R (snd a))) L.

Definition Flist_to_Rlist_pair_abs {ty} (L : list ( (ftype ty) * (ftype ty))) :=
  map (fun a => (Rabs (FT2R (fst a)), Rabs (FT2R (snd a)))) L.



Lemma x_bound_S:
  forall (x:R) (m:nat),
  0 < x -> 
  x * x + 2 * x <= (1 + x) * (1 + x) ^ (m + 1) - 1.
Proof.
intros.
induction m.
+ simpl. nra.
+ apply Rle_trans with ((1 + x) * (1 + x) ^ (m + 1) - 1).
  - apply IHm.
  - apply Rplus_le_compat_r.
    assert ((1 + x) * (1 + x) ^ (m + 1) = 
             1* ((1 + x) * (1 + x) ^ (m + 1))).
    { nra. } rewrite H0.
    assert ((1 + x) * (1 + x) ^ (S m + 1) = 
             (1+x) * ((1 + x) * (1 + x) ^ (m + 1))).
    { simpl. nra. } rewrite H1. apply Rmult_le_compat_r.
    nra. nra.
Qed.

Lemma sum_abs_pair_rel:
  forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
  0 <= sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)).
Proof.
intros.
induction L.
+ simpl. nra.
+ simpl. 
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  apply IHL.
Qed.


Lemma sum_abs_pair_le:
forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
Rabs (dot_prodR (Flist_to_Rlist_pair L)) <=
dot_prodR (Flist_to_Rlist_pair_abs L).
Proof.
intros.
induction L.
+ simpl. unfold dot_prodR. simpl.
  rewrite Rabs_R0. nra.
+ simpl. unfold dot_prodR. simpl. 
  apply Rle_trans with
  (Rabs (FT2R (fst a) * FT2R (snd a)) + 
   Rabs (dot_prodR (Flist_to_Rlist_pair L))).
  - apply Rabs_triang.
  - apply Rplus_le_compat. rewrite Rabs_mult. nra.
    apply IHL.
Qed.


Lemma side_switch:
  forall (x y z:R),
  x - y <= z -> x <= y+z.
Proof.
intros. nra.
Qed.


Lemma list_sum_pair:
  forall (L1 : list ((ftype Tsingle) * (ftype Tsingle)) ) (x:R),
  0 <= x ->
  (forall a: (ftype Tsingle) *(ftype Tsingle) ,
          In a L1 ->
          Binary.is_finite (fprec Tsingle) (femax Tsingle) (fst a) = true /\
          Binary.is_finite (fprec Tsingle) (femax Tsingle) (snd a) = true /\
          Rabs (FT2R (fst a)) <= x  /\
          Rabs (FT2R (snd a)) <= x ) ->
  sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L1)) <= x^2  * (INR (length L1)).
Proof.
intros.
induction L1.
+ simpl. nra.
+ assert (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs (a :: L1))) = 
          Rabs (FT2R (fst a)) * Rabs (FT2R (snd a)) +
          sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L1))).
  { simpl; nra. } rewrite H1. clear H1.
  assert (forall a : ftype Tsingle * ftype Tsingle,
            In a L1 ->
            Binary.is_finite (fprec Tsingle)
              (femax Tsingle) (fst a) = true /\
            Binary.is_finite (fprec Tsingle)
              (femax Tsingle) (snd a) = true /\
            Rabs (FT2R (fst a)) <= x  /\
            Rabs (FT2R (snd a)) <= x ).
  { intros. specialize (H0 a0).
    assert (In a0 (a :: L1)).
    { simpl; auto. } specialize (H0 H2). apply H0.
  } specialize (IHL1 H1).
  specialize (H0 a).
  assert (In a (a :: L1)). { simpl; auto. } specialize (H0 H2).
  destruct H0 as [Ha1 Ha2].
  apply Rle_trans with 
  ( x^2 + x ^ 2 * INR (length L1)).
  - apply Rplus_le_compat. simpl. rewrite Rmult_1_r.
    apply Rmult_le_compat; try nra;try apply Rabs_pos.
    nra.
  - assert (INR (length (a :: L1)) = INR (length L1) + 1).
    { simpl. 
      destruct (length L1).
      + simpl. nra.
      + nra.
    } rewrite H0. nra.
Qed.


Lemma F_bound_rel:
let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u <=
F' / (INR 2 * (1 + u0) ^ 2) - u.
Proof.
intros.
unfold F',F_max,u,u0;simpl;nra.
Qed.


Lemma two_lt_n:
  (2 < Pos.to_nat 8388608)%nat.
lia.
Qed.

(**

  l1, l2 of size n
  1 < n < 2^p -1
  (forall a \in L1 /\ b \in L2, 
      a & b are finite and 
      a,b <= sqrt (F' / (n+1 * (1+d)^(n+1)))
  ) ,
  \rnd_error (fl (l1 * l2) - rl(l1 *l2)) <=
    rl(l1 *l2) * ((1+d)^(n-1) - 1) + n * e * (1+d)^(n-1) + 
    e /d * ((1+d)^(n-1) - 1) /\
  fl(l1* l2) is finite
**)
Lemma forward_error_dot_aux:
  forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
  let ty := Tsingle in 
  let n:= length L in 
  let nr := INR n in
  (1 < n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (n < Z.to_nat (Z.pow_pos 2 23) - 1)%nat ->
  (forall a b : ftype Tsingle,
              In (a,b) L  ->
              Binary.is_finite (fprec Tsingle)
              (femax Tsingle) a = true /\
              Binary.is_finite (fprec Tsingle)
                (femax Tsingle) b = true /\
              Rabs (FT2R a) <=  sqrt( F' / ((nr+1) * (1+u0)^(n+1)) - u ) /\
              Rabs (FT2R b) <=  sqrt( F' / ((nr+1) * (1+u0)^(n+1)) - u )) ->
  is_finite (fprec Tsingle) (femax Tsingle)
  (dot_prodF _ L) = true /\
  Rabs (FT2R (dot_prodF _ L) - dot_prodR (Flist_to_Rlist_pair L)) <=
  (dot_prodR (Flist_to_Rlist_pair_abs L)) * ((1 + u0)^n -1) + 
  nr * u * (1+u0)^(n-1) + u * ((1+u0)^(n-1) -1) / u0.
Proof.
intros.
induction L.
+ simpl in n. rewrite /n in H. contradict H. lia. 
+ unfold dot_prodF, dot_prodR. simpl. 
  remember (length L) as m.
  assert (n = (m+1)%nat). { unfold n. simpl. rewrite Heqm. lia. }
  assert (L = [:: ] \/ L <> [::]).
  { destruct L.
    + by left.
    + by right. 
  } destruct H3.
  - rewrite H3 //= in Heqm. rewrite Heqm //= in H2.
    rewrite H2 in H. contradict H. lia.
  - unfold dot_prodF, dot_prodR. simpl.
    assert ( match prod_fixF Tsingle L with
             | [] => prod Tsingle (fst a) (snd a)
             | (_ :: _)%SEQ =>
                 sum Tsingle (prod Tsingle (fst a) (snd a))
                   (sum_fixF Tsingle (prod_fixF Tsingle L))
             end = sum Tsingle (prod Tsingle (fst a) (snd a))
            (sum_fixF Tsingle (prod_fixF Tsingle L))).
    { destruct L.
      + contradict H3. auto.
      + simpl. auto.
    } rewrite H4. clear H4. 
    assert ((1 <= m)%nat).
    { rewrite Heqm. destruct L.
      + contradict H3. auto.
      + simpl. lia. 
    } destruct H4.
    * symmetry in Heqm.
      pose proof (lenght_elem L Heqm).
      destruct H4 as [b H4].
      rewrite H4. simpl. rewrite !Rplus_0_r. split.
      ++ destruct (prove_rndoff' (prod Tsingle (fst a) (snd a))
                                  (prod Tsingle (fst b) (snd b)) vmap 2%nat).
         -- lia.
         -- apply boundsmap_denote_i.
             2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
             repeat apply list_forall_cons; try apply list_forall_nil;
              (eexists; split; [|split;[|split]]; try reflexivity; auto;
                try unfold List.nth; try nra; auto).
             ** destruct (prove_rndoff'' (fst b) (snd b) vmap 2%nat).
                +++ lia.
                +++ apply two_lt_n.
                +++ apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                     --- specialize (H1 (fst b) (snd b)).
                          rewrite H4 in H1.
                          assert (In (fst b, snd b) [a; b]).
                          { destruct b. simpl. auto. } specialize (H1 H5).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst b) (snd b)).
                         assert (In (fst b, snd b) [a; b]).
                         { destruct b. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
                         unfold nr in Hb2.
                          simpl in H2. rewrite H2 in Hb2.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                     --- specialize (H1 (fst b) (snd b)).
                          rewrite H4 in H1.
                          assert (In (fst b, snd b) [a; b]).
                          { destruct b. simpl. auto. } specialize (H1 H5).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst b) (snd b)).
                         assert (In (fst b, snd b) [a; b]).
                         { destruct b. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
                         unfold nr in Hb1.
                          simpl in H2. rewrite H2 in Hb1.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                +++ auto.
             ** apply Rabs_ineq.
                remember (fst b) as b1.
                remember (snd b) as b2.
                specialize (H1 b1 b2).
                assert (In (b1, b2) (a :: L)).
                { rewrite H4. rewrite Heqb1 Heqb2. destruct b. simpl; auto. }
                specialize (H1 H5).
                destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
                assert ((1<2)%nat). { lia. }
                pose proof (prove_rndoff_prod b1 b2 2%nat H1).
                simpl in H6.
                assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. }
                specialize (H6 H7).
                assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap b1 b2)).
                { apply boundsmap_denote_i.
                   2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                   repeat apply list_forall_cons; try apply list_forall_nil;
                    (eexists; split; [|split;[|split]]; try reflexivity; auto;
                      try unfold List.nth; try nra; auto).
                  + apply Rabs_ineq. fold u u0. unfold nr in Hb2.
                    simpl in H2. rewrite H2 in Hb2.
                    apply Rle_trans with 
                    (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                    - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    - apply sqrt_le_1_alt.
                      apply  F_bound_rel.
                  + apply Rabs_ineq. fold u u0. unfold nr in Hb1.
                    simpl in H2. rewrite H2 in Hb1. 
                    apply Rle_trans with 
                    (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                    - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    - apply sqrt_le_1_alt.
                      apply F_bound_rel.
                } specialize (H6 H8).
                apply Rabs_triang_inv_impl in H6.
                apply side_switch in H6.
                apply Rle_trans with 
                (Rabs (FT2R b1 * FT2R b2) +
                   (Rabs (FT2R b1 * FT2R b2) *
                    (/ 2 * / IZR (Z.pow_pos 2 23)) +
                    / 2 * / IZR (Z.pow_pos 2 149))).
                +++ nra.
                +++ fold u u0. simpl in u,u0. fold u u0.
                   assert (Rabs (FT2R b1 * FT2R b2) +
                                (Rabs (FT2R b1 * FT2R b2) * u0 + u) = 
                           (Rabs (FT2R b1) * Rabs (FT2R b2)) * (1+u0) + u).
                   { rewrite !Rabs_mult. nra. } rewrite H9.
                   apply Rle_trans with
                   ( (sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u) * sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u)) 
                      * (1 + u0) + u ).
                   --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                      unfold u0; simpl; nra.
                      apply Rmult_le_compat.
                      *** apply Rabs_pos.
                      *** apply Rabs_pos.
                      *** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                      *** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                   --- rewrite sqrt_def;
                      unfold nr; rewrite H2; unfold F', F_max, u, u0; simpl; nra.
              ** destruct (prove_rndoff'' (fst a) (snd a) vmap 2%nat).
                +++ lia.
                +++ apply two_lt_n.
                +++ apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                     --- specialize (H1 (fst a) (snd a)).
                          rewrite H4 in H1.
                          assert (In (fst a, snd a) [a; b]).
                          { destruct a. simpl. auto. } specialize (H1 H5).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) [a; b]).
                         { destruct a. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                         unfold nr in Ha2.
                          simpl in H2. rewrite H2 in Ha2.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                     --- specialize (H1 (fst a) (snd a)).
                          rewrite H4 in H1.
                          assert (In (fst a, snd a) [a; b]).
                          { destruct a. simpl. auto. } specialize (H1 H5).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) [a; b]).
                         { destruct a. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                         unfold nr in Ha1.
                          simpl in H2. rewrite H2 in Ha1.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                +++ auto.
             ** apply Rabs_ineq.
                remember (fst a) as a1.
                remember (snd a) as a2.
                specialize (H1 a1 a2).
                assert (In (a1, a2) (a :: L)).
                { rewrite H4. rewrite Heqa1 Heqa2. destruct a. simpl; auto. }
                specialize (H1 H5).
                destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                assert ((1<2)%nat). { lia. }
                pose proof (prove_rndoff_prod a1 a2 2%nat H1).
                simpl in H6.
                assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. }
                specialize (H6 H7).
                assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
                { apply boundsmap_denote_i.
                   2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                   repeat apply list_forall_cons; try apply list_forall_nil;
                    (eexists; split; [|split;[|split]]; try reflexivity; auto;
                      try unfold List.nth; try nra; auto).
                  + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                    simpl in H2. rewrite H2 in Ha2.
                    apply Rle_trans with 
                    (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                    - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                    - apply sqrt_le_1_alt.
                      apply  F_bound_rel.
                  + apply Rabs_ineq. fold u u0. unfold nr in Ha1.
                    simpl in H2. rewrite H2 in Ha1. 
                    apply Rle_trans with 
                    (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                    - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                    - apply sqrt_le_1_alt.
                      apply F_bound_rel.
                } specialize (H6 H8).
                apply Rabs_triang_inv_impl in H6.
                apply side_switch in H6.
                apply Rle_trans with 
                (Rabs (FT2R a1 * FT2R a2) +
                   (Rabs (FT2R a1 * FT2R a2) *
                    (/ 2 * / IZR (Z.pow_pos 2 23)) +
                    / 2 * / IZR (Z.pow_pos 2 149))).
                +++ nra.
                +++ fold u u0. simpl in u,u0. fold u u0.
                   assert (Rabs (FT2R a1 * FT2R a2) +
                                (Rabs (FT2R a1 * FT2R a2) * u0 + u) = 
                           (Rabs (FT2R a1) * Rabs (FT2R a2)) * (1+u0) + u).
                   { rewrite !Rabs_mult. nra. } rewrite H9.
                   apply Rle_trans with
                   ( (sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u) * sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u)) 
                      * (1 + u0) + u ).
                   --- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                      unfold u0; simpl; nra.
                      apply Rmult_le_compat.
                      *** apply Rabs_pos.
                      *** apply Rabs_pos.
                      *** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                      *** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                   --- rewrite sqrt_def;
                      unfold nr; rewrite H2; unfold F', F_max, u, u0; simpl; nra.
            -- auto. 
         ++ pose proof (prove_rndoff (prod Tsingle (fst a) (snd a)) 
                      (prod Tsingle (fst b) (snd b)) 2%nat).
          assert ((1 < 2)%nat). { lia. } specialize (H5 H6).
          simpl in H5.
          assert (boundsmap_denote (@bmap Tsingle 2)
                     (vmap (prod Tsingle (fst a) (snd a))
                        (prod Tsingle (fst b) (snd b)))).
          { apply boundsmap_denote_i.
               2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
               repeat apply list_forall_cons; try apply list_forall_nil;
                (eexists; split; [|split;[|split]]; try reflexivity; auto;
                  try unfold List.nth; try nra; auto).
            + destruct (prove_rndoff'' (fst b) (snd b) vmap 2%nat).
                +++ lia.
                +++ apply two_lt_n.
                +++ apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                     --- specialize (H1 (fst b) (snd b)).
                          rewrite H4 in H1.
                          assert (In (fst b, snd b) [a; b]).
                          { destruct b. simpl. auto. } specialize (H1 H7).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst b) (snd b)).
                         assert (In (fst b, snd b) [a; b]).
                         { destruct b. simpl. auto. } specialize (H1 H7).
                         fold u u0. destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
                         unfold nr in Hb2.
                          simpl in H2. rewrite H2 in Hb2.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                     --- specialize (H1 (fst b) (snd b)).
                          rewrite H4 in H1.
                          assert (In (fst b, snd b) [a; b]).
                          { destruct b. simpl. auto. } specialize (H1 H7).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst b) (snd b)).
                         assert (In (fst b, snd b) [a; b]).
                         { destruct b. simpl. auto. } specialize (H1 H7).
                         fold u u0. destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
                         unfold nr in Hb1.
                          simpl in H2. rewrite H2 in Hb1.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                +++ auto.
            + apply Rabs_ineq. 
              remember (fst b) as b1.
              remember (snd b) as b2.
              specialize (H1 b1 b2).
              assert (In (b1, b2) (a :: L)).
              { rewrite H4. rewrite Heqb1 Heqb2. destruct b. simpl; auto. }
              specialize (H1 H7).
              destruct H1 as [Hfb1 [Hfb2 [Hb1 Hb2]]].
              pose proof (prove_rndoff_prod b1 b2 2%nat H6).
              simpl in H1.
              assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. }
              specialize (H1 H8).
              assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap b1 b2)).
              { apply boundsmap_denote_i.
                 2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                 repeat apply list_forall_cons; try apply list_forall_nil;
                  (eexists; split; [|split;[|split]]; try reflexivity; auto;
                    try unfold List.nth; try nra; auto).
                + apply Rabs_ineq. fold u u0. unfold nr in Hb2.
                  simpl in H2. rewrite H2 in Hb2.
                  apply Rle_trans with 
                  (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                  - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                  - apply sqrt_le_1_alt.
                    apply  F_bound_rel.
                + apply Rabs_ineq. fold u u0. unfold nr in Hb1.
                  simpl in H2. rewrite H2 in Hb1. 
                  apply Rle_trans with 
                  (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                  - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                  - apply sqrt_le_1_alt.
                    apply F_bound_rel.
              } specialize (H1 H9).
              apply Rabs_triang_inv_impl in H1.
              apply side_switch in H1.
              apply Rle_trans with 
              (Rabs (FT2R b1 * FT2R b2) +
                 (Rabs (FT2R b1 * FT2R b2) *
                  (/ 2 * / IZR (Z.pow_pos 2 23)) +
                  / 2 * / IZR (Z.pow_pos 2 149))).
              ++ nra.
              ++ fold u u0. simpl in u,u0. fold u u0.
                 assert (Rabs (FT2R b1 * FT2R b2) +
                              (Rabs (FT2R b1 * FT2R b2) * u0 + u) = 
                         (Rabs (FT2R b1) * Rabs (FT2R b2)) * (1+u0) + u).
                 { rewrite !Rabs_mult. nra. } rewrite H10.
                 apply Rle_trans with
                 ( (sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u) * sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u)) 
                    * (1 + u0) + u ).
                 -- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                    unfold u0; simpl; nra.
                    apply Rmult_le_compat.
                    ** apply Rabs_pos.
                    ** apply Rabs_pos.
                    ** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                    ** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                 -- rewrite sqrt_def;
                    unfold nr; rewrite H2; unfold F', F_max, u, u0; simpl; nra.
            + destruct (prove_rndoff'' (fst a) (snd a) vmap 2%nat).
                +++ lia.
                +++ apply two_lt_n.
                +++ apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                     --- specialize (H1 (fst a) (snd a)).
                          rewrite H4 in H1.
                          assert (In (fst a, snd a) [a; b]).
                          { destruct a. simpl. auto. } specialize (H1 H7).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) [a; b]).
                         { destruct a. simpl. auto. } specialize (H1 H7).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                         unfold nr in Ha2.
                          simpl in H2. rewrite H2 in Ha2.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                     --- specialize (H1 (fst a) (snd a)).
                          rewrite H4 in H1.
                          assert (In (fst a, snd a) [a; b]).
                          { destruct a. simpl. auto. } specialize (H1 H7).
                          apply H1.
                     --- apply Rabs_ineq.
                         rewrite H4 in H1.  specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) [a; b]).
                         { destruct a. simpl. auto. } specialize (H1 H7).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                         unfold nr in Ha1.
                          simpl in H2. rewrite H2 in Ha1.
                          apply Rle_trans with 
                          (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                          *** apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                          *** apply sqrt_le_1_alt. apply F_bound_rel.
                +++ auto. 
            + apply Rabs_ineq.
              remember (fst a) as a1.
              remember (snd a) as a2.
              specialize (H1 a1 a2).
              assert (In (a1, a2) (a :: L)).
              { left. rewrite Heqa1 Heqa2. destruct a. simpl. auto.  }
              specialize (H1 H7).
              destruct H1 as [Haf1 [Haf2 [Ha1 Ha2]]].
              pose proof (prove_rndoff_prod a1 a2 2%nat H6).
              simpl in H1.
              assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. }
              specialize (H1 H8).
              assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
              { apply boundsmap_denote_i.
                 2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                 repeat apply list_forall_cons; try apply list_forall_nil;
                  (eexists; split; [|split;[|split]]; try reflexivity; auto;
                    try unfold List.nth; try nra; auto).
                + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                  simpl in H2. rewrite H2 in Ha2.
                  apply Rle_trans with 
                  (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                  - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                  - apply sqrt_le_1_alt. apply F_bound_rel.
                + apply Rabs_ineq. fold u u0. unfold nr in Ha1.
                  simpl in H2. rewrite H2 in Ha1.
                  apply Rle_trans with 
                  (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                  - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                  - apply sqrt_le_1_alt. apply F_bound_rel.
              } specialize (H1 H9).
              apply Rabs_triang_inv_impl in H1.
              apply side_switch in H1.
              apply Rle_trans with 
              (Rabs (FT2R a1 * FT2R a2) +
                 (Rabs (FT2R a1 * FT2R a2) *
                  (/ 2 * / IZR (Z.pow_pos 2 23)) +
                  / 2 * / IZR (Z.pow_pos 2 149))).
              ++ nra.
              ++ fold u u0. simpl in u,u0. fold u u0.
                 assert (Rabs (FT2R a1 * FT2R a2) +
                              (Rabs (FT2R a1 * FT2R a2) * u0 + u) = 
                         (Rabs (FT2R a1) * Rabs (FT2R a2)) * (1+u0) + u).
                 { rewrite !Rabs_mult. nra. } rewrite H10.
                 apply Rle_trans with
                 ( (sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u) * sqrt (F' / (nr * (1 + u0) ^ (n+1)) - u)) 
                    * (1 + u0) + u ).
                 -- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                    unfold u0; simpl; nra.
                    apply Rmult_le_compat.
                    ** apply Rabs_pos.
                    ** apply Rabs_pos.
                    ** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                    ** apply Rle_trans with 
                          (sqrt (F' / ((nr + 1) * (1 + u0) ^ (n + 1)) - u)).
                          ++++ nra.
                          ++++ apply sqrt_le_1_alt . apply Rplus_le_compat_r.
                               apply Rmult_le_compat_l. unfold F',F_max; simpl;nra.
                               apply Rlt_le. apply Rinv_lt_contravar.
                                ----- apply Rmult_lt_0_compat.
                                      ***** apply Rmult_lt_0_compat. unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                      ***** apply Rmult_lt_0_compat. 
                                            unfold nr.
                                            rewrite H2. simpl; nra. apply x_pow_gt_0.
                                            unfold u0; simpl; nra.
                                ----- apply Rmult_lt_compat_r . apply x_pow_gt_0.
                                            unfold u0; simpl; nra. nra.
                 -- rewrite sqrt_def;
                    unfold nr; rewrite H2; unfold F', F_max, u, u0; simpl; nra.
             } specialize (H5 H7). 
            apply Rle_trans with 
            (Rabs
             (FT2R
                (sum Tsingle (prod Tsingle (fst a) (snd a)) (prod Tsingle (fst b) (snd b))) -
              (FT2R (prod Tsingle (fst a) (snd a)) + FT2R (prod Tsingle (fst b) (snd b)))) + 
              Rabs ((FT2R (prod Tsingle (fst a) (snd a)) + FT2R (prod Tsingle (fst b) (snd b))) -
                     (FT2R (fst a) * FT2R (snd a) + FT2R (fst b) * FT2R (snd b)))).
            -- assert ((FT2R
                           (sum Tsingle (prod Tsingle (fst a) (snd a))
                              (prod Tsingle (fst b) (snd b))) -
                         (FT2R (fst a) * FT2R (snd a) +
                          FT2R (fst b) * FT2R (snd b))) = 
                       (FT2R
                         (sum Tsingle (prod Tsingle (fst a) (snd a))
                            (prod Tsingle (fst b) (snd b))) -
                       (FT2R (prod Tsingle (fst a) (snd a)) +
                        FT2R (prod Tsingle (fst b) (snd b)))) +
                        (FT2R (prod Tsingle (fst a) (snd a)) +
                           FT2R (prod Tsingle (fst b) (snd b)) -
                           (FT2R (fst a) * FT2R (snd a) +
                            FT2R (fst b) * FT2R (snd b)))).
               { nra. } rewrite H8. clear H8. apply Rabs_triang.
             -- apply Rle_trans with 
                (( Rabs
                       (FT2R (prod Tsingle (fst a) (snd a)) +
                        FT2R (prod Tsingle (fst b) (snd b))) *
                     (/ 2 * / IZR (Z.pow_pos 2 23)) +
                     / 2 * / IZR (Z.pow_pos 2 149)) + Rabs
                  (FT2R (prod Tsingle (fst a) (snd a)) +
                   FT2R (prod Tsingle (fst b) (snd b)) -
                   (FT2R (fst a) * FT2R (snd a) +
                    FT2R (fst b) * FT2R (snd b)))).
                ** by apply Rplus_le_compat_r.
                ** pose proof (prove_rndoff_prod (fst a) (snd a) 2%nat).
                   specialize (H8 H6).
                   simpl in H8.
                   assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. } 
                   specialize (H8 H9).
                   remember (fst a) as a1.
                   remember (snd a) as a2.
                   assert (Rabs (FT2R a1) <=
                             sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) /\
                             Rabs (FT2R a2) <=
                             sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                   { specialize (H1 a1 a2).
                      assert (In (a1, a2) (a :: L)).
                      { left. rewrite Heqa1 Heqa2. destruct a. simpl. auto.  }
                      specialize (H1 H10). nra.
                   } destruct H10 as [Ha1 Ha2].
                    pose proof (prove_rndoff_prod a1 a2 2%nat H6).
                    assert ((2 < Pos.to_nat 8388608)%nat). { apply two_lt_n. }
                    specialize (H10 H11).
                    assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
                    { apply boundsmap_denote_i.
                       2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                       repeat apply list_forall_cons; try apply list_forall_nil;
                        (eexists; split; [|split;[|split]]; try reflexivity; auto;
                          try unfold List.nth; try nra; auto).
                      + specialize (H1 a1 a2).
                        rewrite H4 in H1.
                        assert (In (a1, a2) [a; b]).
                        { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H12).
                        apply H1.
                      + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                        simpl in H2. rewrite H2 in Ha2.
                        apply Rle_trans with 
                        (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                        - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                        - apply sqrt_le_1_alt. apply F_bound_rel.
                      + specialize (H1 a1 a2).
                        rewrite H4 in H1.
                        assert (In (a1, a2) [a; b]).
                        { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H12).
                        apply H1.
                      + apply Rabs_ineq. fold u u0. unfold nr in Ha1.
                        simpl in H2. rewrite H2 in Ha1.
                        apply Rle_trans with 
                        (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                        - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                        - apply sqrt_le_1_alt.
                          apply F_bound_rel.
                    } specialize (H10 H12).
                   pose proof (prove_rndoff_prod (fst b) (snd b) 2%nat).
                   specialize (H13 H6).
                   simpl in H13.
                   specialize (H13 H11).
                   remember (fst b) as b1.
                   remember (snd b) as b2.
                   assert (Rabs (FT2R b1) <=
                             sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) /\
                             Rabs (FT2R b2) <=
                             sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                   { specialize (H1 b1 b2).
                      assert (In (b1, b2) (a :: L)).
                      { rewrite H4. rewrite Heqb1 Heqb2. destruct b. simpl; auto. }
                      specialize (H1 H14). nra.
                   } destruct H14 as [Hb1 Hb2].
                    pose proof (prove_rndoff_prod b1 b2 2%nat H6).
                    specialize (H14 H9).
                    assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap b1 b2)).
                    { apply boundsmap_denote_i.
                       2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                       repeat apply list_forall_cons; try apply list_forall_nil;
                        (eexists; split; [|split;[|split]]; try reflexivity; auto;
                          try unfold List.nth; try nra; auto).
                      + specialize (H1 b1 b2).
                        rewrite H4 in H1.
                        assert (In (b1, b2) [a; b]).
                        { destruct b. rewrite Heqb1 Heqb2. simpl. auto. } specialize (H1 H15).
                        apply H1.
                      + apply Rabs_ineq. fold u u0. unfold nr in Hb2.
                        simpl in H2. rewrite H2 in Hb2.
                        apply Rle_trans with 
                        (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                        - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                        - apply sqrt_le_1_alt. apply F_bound_rel.
                      + specialize (H1 b1 b2).
                        rewrite H4 in H1.
                        assert (In (b1, b2) [a; b]).
                        { destruct b. rewrite Heqb1 Heqb2. simpl. auto. } specialize (H1 H15).
                        apply H1.
                      + apply Rabs_ineq. fold u u0. unfold nr in Hb1.
                        simpl in H2. rewrite H2 in Hb1.
                        apply Rle_trans with 
                        (sqrt (F' / (INR 2 * (1 + u0) ^ (2 + 1)) - u)).
                        - apply Rle_trans with 
                              (sqrt (F' / ((INR 2 + 1) * (1 + u0) ^ (2 + 1)) - u)).  
                              ++++ nra.
                              ++++ apply sqrt_le_1_alt. unfold F',F_max,u,u0; simpl; nra.
                    
                        - apply sqrt_le_1_alt.
                          apply F_bound_rel.
                    } specialize (H14 H15).
                    apply Rle_trans with  (((Rabs (FT2R (prod Tsingle a1 a2)) + Rabs (FT2R (prod Tsingle b1 b2))) * 
                             (/ 2 * / IZR (Z.pow_pos 2 23)) + / 2 * / IZR (Z.pow_pos 2 149)) + 
                            ( Rabs (FT2R (prod Tsingle a1 a2) - FT2R a1 * FT2R a2) + 
                              Rabs (FT2R (prod Tsingle b1 b2) - FT2R b1 * FT2R b2))).
                    *** apply Rplus_le_compat.
                       +++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                           nra. apply Rabs_triang.
                       +++ assert ((FT2R (prod Tsingle a1 a2) + FT2R (prod Tsingle b1 b2) -
                                    (FT2R a1 * FT2R a2 + FT2R b1 * FT2R b2)) = 
                                   (FT2R (prod Tsingle a1 a2) - FT2R a1 * FT2R a2) + 
                                   (FT2R (prod Tsingle b1 b2) - FT2R b1 * FT2R b2)).
                           { nra. } rewrite H16. apply Rabs_triang.
                    *** fold u u0 in H10, H14. 
                       apply Rle_trans with
                       ((((Rabs (FT2R a1 * FT2R a2) * (1+ u0) + u) + 
                         (Rabs (FT2R b1 * FT2R b2) * (1+ u0) + u)) *
                         (/ 2 * / IZR (Z.pow_pos 2 23)) + 
                         (/ 2 * / IZR (Z.pow_pos 2 149))) +
                       ((Rabs (FT2R a1 * FT2R a2) * u0 + u) +
                        (Rabs (FT2R b1 * FT2R b2) * u0 + u))). 
                       ++++ apply Rplus_le_compat.
                            ---- apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                                 nra. apply Rplus_le_compat.
                                 **** apply Rabs_triang_inv_impl in H10. nra.
                                 **** apply Rabs_triang_inv_impl in H14. nra.
                            ---- apply Rplus_le_compat;nra.
                       ++++ unfold nr. simpl in H2. rewrite H2.
                            simpl in u, u0. fold u u0.
                            rewrite !Rabs_mult. 
                            change (INR 2) with 2. 
                            assert (u * ((1 + u0) * 1 - 1) / u0 = u).
                            { unfold u, u0; simpl; nra. } rewrite H16. nra.
       * split.
         ++ destruct (prove_rndoff' (prod Tsingle (fst a) (snd a))
                                  (sum_fixF Tsingle (prod_fixF Tsingle L)) vmap n).
            -- lia.
            -- apply boundsmap_denote_i.
                 2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                    repeat apply list_forall_cons; try apply list_forall_nil;
                        (eexists; split; [|split;[|split]]; try reflexivity; auto;
                          try unfold List.nth; try nra; auto).
               ** apply IHL. lia. lia.
                  intros. specialize (H1 a0 b).
                  assert (In (a0, b) (a :: L)). 
                  { simpl;auto. } specialize (H1 H6).
                  repeat split; try apply H1.
                  +++ apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      --- nra. 
                      --- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        *** apply Rmult_lt_0_compat.
                          ++++ apply Rmult_lt_0_compat.
                             ---- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             ---- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++++ apply Rmult_lt_0_compat.
                             ---- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             ---- apply x_pow_gt_0. unfold u0; simpl; nra.
                        *** apply Rmult_lt_compat.
                          ++++ apply Rplus_le_le_0_compat. apply pos_INR. nra. 
                          ++++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia.
                          ++++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                  +++ apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      --- nra.
                      --- apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        *** apply Rmult_lt_0_compat.
                          ++++ apply Rmult_lt_0_compat.
                             ---- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             ---- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++++ apply Rmult_lt_0_compat.
                             ---- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             ---- apply x_pow_gt_0. unfold u0; simpl; nra.
                        *** apply Rmult_lt_compat.
                          ++++ apply Rplus_le_le_0_compat. apply pos_INR. nra.
                          ++++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia.
                          ++++ apply Rlt_pow. unfold u0; simpl; nra. lia.
              ** apply Rabs_ineq.
                 assert ((1 < S m)%nat). { lia. } 
                  specialize (IHL H5).
                  assert ((S m < Z.to_nat (Z.pow_pos 2 23) - 1)%nat).
                  { apply lt_trans with n; lia. }
                  specialize (IHL H6).
                  assert ((forall a b : ftype Tsingle,
                             In (a, b) L ->
                             Binary.is_finite (fprec Tsingle)
                               (femax Tsingle) a = true /\
                             Binary.is_finite (fprec Tsingle)
                               (femax Tsingle) b = true /\
                             Rabs (FT2R a) <=
                             sqrt (F' / ((INR (S m) +1) * (1 + u0) ^ (S m + 1)) - u) /\
                             Rabs (FT2R b) <=
                             sqrt (F' / ((INR (S m) +1) * (1 + u0) ^ (S m + 1)) - u))).
                  { intros. specialize (H1 a0 b).
                    assert (In (a0, b) (a :: L)).
                    { simpl. auto.
                    } specialize (H1 H8). destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]]. split. auto.
                    split. auto. split.
                    + apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      - nra.
                      - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        * apply Rmult_lt_0_compat.
                          ++ apply Rmult_lt_0_compat.
                             -- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++ apply Rmult_lt_0_compat.
                             -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                        * apply Rmult_lt_compat.
                          ++ apply Rplus_le_le_0_compat. apply pos_INR. nra.
                          ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia. 
                          ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                    + apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      - nra.
                      - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        * apply Rmult_lt_0_compat.
                          ++ apply Rmult_lt_0_compat.
                             -- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++ apply Rmult_lt_0_compat.
                             -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                        * apply Rmult_lt_compat.
                          ++ apply Rplus_le_le_0_compat. apply pos_INR. nra.
                          ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia. 
                          ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                   } specialize (IHL H7). clear H7. destruct IHL as [ifHL IHL].
                    unfold dot_prodF, dot_prodR in IHL. 
                     apply Rabs_triang_inv_impl in IHL. apply side_switch in IHL.
                     apply Rle_trans with 
                     (Rabs (sum_fixR (prod_fixR (Flist_to_Rlist_pair L))) +
                        (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                         ((1 + u0) ^ S m - 1) +
                         INR (S m) * u * (1 + u0) ^ (S m - 1) +
                         u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                     +++ nra.
                     +++ apply Rle_trans with 
                       (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) +
                              (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                               ((1 + u0) ^ S m - 1) + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                               u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                       *** apply Rplus_le_compat_r. apply sum_abs_pair_le.
                       *** assert (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) +
                                    (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                     ((1 + u0) ^ S m - 1) + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                     u * ((1 + u0) ^ (S m - 1) - 1) / u0) = 
                                 sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) * (1 + u0) ^ S m +
                                 INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                  u * ((1 + u0) ^ (S m - 1) - 1) / u0).
                         { nra. } rewrite H7. clear H7.
                         apply Rle_trans with 
                         (((sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u))^2 * INR (length L)) *
                          (1 + u0) ^ S m + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                            u * ((1 + u0) ^ (S m - 1) - 1) / u0).
                         ++++  apply Rplus_le_compat_r. apply Rplus_le_compat_r. 
                             apply Rmult_le_compat_r.
                             ---- apply Rlt_le, x_pow_gt_0. unfold u0;simpl; nra. 
                             ---- apply (list_sum_pair L (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u))).
                                apply sqrt_pos. intros.
                                specialize (H1 (fst a0) (snd a0)).
                                assert (In (fst a0, snd a0) (a :: L)).
                                { simpl. destruct a0. simpl; auto. }
                                specialize (H1 H8). apply H1.
                         ++++ assert (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) ^ 2 = 
                                    (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                            { assert (forall x:R, x^2 = x * x). { intros. nra. } rewrite H7.
                              apply sqrt_sqrt.
                              apply Rge_le. apply Rge_minus. apply Rle_ge.
                               apply pow_invert.
                                * apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                  apply x_pow_gt_0. unfold u0; simpl; nra.
                                * apply Rle_trans with 
                                  (u * ((INR n + 1) * 3)).
                                  +++ repeat apply Rmult_le_compat_l.
                                     --- unfold u; simpl; nra.
                                     --- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                     --- apply Rlt_le. 
                                         pose proof  (delta_bound (n+1)%nat).
                                         assert ( (n + 1 < Z.to_nat (Z.pow_pos 2 23))%nat).
                                         { lia. } specialize (H8 H9).
                                        fold u0 in H8.
                                        nra.
                                  +++ replace (u * ((INR n+1) * 3)) with ((INR n+1) * (3 * u)) by nra.
                                     apply pow_invert_1.
                                     --- unfold u;simpl;nra.
                                     --- apply Rle_trans with 
                                          (IZR (Z.pow_pos 2 23) + 1).
                                        *** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                        *** unfold u. simpl. unfold F', F_max; simpl; nra.
                            } rewrite H7. rewrite -Heqm. 
                            assert (S m = (n-1)%nat). { lia. } rewrite H8.
                            assert ((n - 1 - 1)%nat = (n-2)%nat). { lia. } rewrite H9.
                            clear H8 H9.
                            assert ((F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) * INR (n - 1) *
                                      (1 + u0) ^ (n - 1) + INR (n - 1) * u * (1 + u0) ^ (n - 2) +
                                      u * ((1 + u0) ^ (n - 2) - 1) / u0 = 
                                    (F' / ((nr+1) * (1 + u0) ^ (n + 1)) * INR (n-1) *(1 + u0) ^ (n - 1)) + 
                                    ((INR (n - 1) * u * (1 + u0) ^ (n - 2) - INR (n - 1) * u  * (1 + u0) ^ (n - 1)) +
                                    u * ((1 + u0) ^ (n - 2) - 1) / u0)).
                            { nra. } rewrite H8. clear H8.
                            apply Rplus_le_compat.
                            ---- unfold nr. 
                               assert (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1) = 
                                       (F' * / ((INR n+1) * (1 + u0) ^ (n + 1))) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1)). { nra. } rewrite H8. clear H8.
                               rewrite Rinv_mult_distr.
                               replace (F' * (INR n - 1) / INR n) with ((F' * (INR n - 1) / INR n) * 1) by nra.
                               assert (F' * (/ (INR n +1) * / (1 + u0) ^ (n + 1)) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1) = 
                                       (F' * (INR n - 1) / (INR n + 1)) * ((1 + u0) ^ (n - 1) /(1 + u0) ^ (n + 1))).
                               { rewrite minus_INR. simpl; nra. lia. } rewrite H8. clear H8.
                               apply Rmult_le_compat.
                               ****  apply Rmult_le_pos.
                                   +++++ apply Rmult_le_pos; try (unfold F', F_max; simpl; nra); try apply pos_INR.
                                       apply Rge_le. apply Rge_minus. apply Rle_ge. 
                                       replace 1 with (INR 1) by (simpl; nra). apply le_INR;lia.
                                   +++++ apply Rlt_le. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat. apply lt_0_INR; lia. nra.
                               **** apply Rmult_le_pos. 
                                    +++++ apply pow_le. unfold u0; simpl; nra.
                                    +++++ apply Rlt_le, Rinv_0_lt_compat. apply x_pow_gt_0.
                                          unfold u0;simpl;nra.
                               **** repeat apply Rmult_le_compat_l.
                                    +++++ apply Rmult_le_pos. unfold F',F_max;simpl;nra.
                                          apply Rge_le, Rge_minus, Rle_ge. 
                                          replace 1 with (INR 1) by (simpl;nra).
                                          apply le_INR. lia.
                                    +++++ apply Rlt_le, Rinv_lt_contravar. apply Rmult_lt_0_compat.
                                          apply lt_0_INR. lia. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                          nra.    
                               **** assert (1 = (1+u0)^(n+1) / (1+u0)^(n+1)).
                                  { symmetry. apply Rinv_r. apply pow_nonzero .
                                    unfold u0;simpl;nra.
                                  } 
                                  assert ( (1 + u0) ^ (n - 1) / (1 + u0) ^ (n + 1) <= 
                                            (1+u0)^(n+1) / (1+u0)^(n+1) ->
                                             (1 + u0) ^ (n - 1) / (1 + u0) ^ (n + 1) <= 1).
                                  { rewrite -H8; nra. } apply H9. apply Rmult_le_compat_r.
                                  +++++ apply Rlt_le, Rinv_0_lt_compat. apply x_pow_gt_0. unfold u0;simpl;nra.
                                  +++++ apply Rle_pow. unfold u0;simpl;nra. lia.
                               **** assert ((0 < INR n + 1) -> INR n + 1 <> 0). { nra. } apply H8.
                                    apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                               **** apply pow_nonzero. unfold u0;simpl;nra.
                            ---- match goal with |-context[ _ <= ?a]=>
                                 replace a with (0 + a) by nra
                               end. apply Rplus_le_compat.
                               **** assert ((n - 1)%nat = (S (n-2))%nat). { lia. }
                                  rewrite H8. 
                                  assert (INR (S (n - 2)) * u * (1 + u0) ^ (n - 2) -
                                            INR (S (n - 2)) * u * (1 + u0) ^ S (n - 2)  =
                                          - (u0 * INR (S (n - 2)) * u * (1 + u0) ^ (n - 2))).
                                  { simpl; nra. } rewrite H9.
                                  apply Rge_le. apply Ropp_0_le_ge_contravar.
                                  repeat apply Rmult_le_pos; try (simpl;nra); try nra; try apply pos_INR;
                                  try (apply Rlt_le, x_pow_gt_0; unfold u0; simpl; nra).
                               **** rewrite -/u -/u0. 
                                  replace (u * ((1 + u0) ^ (n - 2) - 1) / u0) with 
                                  (((1 + u0) ^ (n - 2) - 1) * (u / u0)) by nra.
                                  replace (2 * u / u0) with (2 * (u/u0)) by nra.
                                  apply Rmult_le_compat_r.
                                  +++++ unfold u,u0; simpl; nra.
                                  +++++ apply Rlt_le. apply (delta_bound (n-2)%nat).
                                      apply lt_trans with n; lia.
              ** destruct (prove_rndoff'' (fst a) (snd a) vmap 2%nat).
                +++ lia.
                +++ apply two_lt_n.
                +++ apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                     --- specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) (a :: L)).
                         { destruct a. simpl;auto. } specialize (H1 H5).
                         apply H1.
                     --- apply Rabs_ineq.
                         specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) (a :: L)).
                         { destruct a. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          *** nra.
                          *** apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                            apply Rlt_le. apply  Rinv_lt_contravar .
                            ++++ apply Rmult_lt_0_compat.
                              ---- apply Rmult_lt_0_compat.
                                  **** apply lt_0_INR. lia.
                                  **** apply x_pow_gt_0. unfold u0; simpl; nra.
                              ---- apply Rmult_lt_0_compat.
                                  **** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                  **** apply x_pow_gt_0. unfold u0; simpl; nra.
                            ++++ apply Rmult_lt_compat.
                              ---- apply pos_INR.
                              ---- apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                              ---- unfold nr.
                                   assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                   apply H1. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                              ---- apply Rlt_pow. unfold u0; simpl; nra. lia.
                     --- specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) (a :: L)).
                         { destruct a. simpl;auto. } specialize (H1 H5).
                         apply H1.
                     --- apply Rabs_ineq. 
                         specialize (H1 (fst a) (snd a)).
                         assert (In (fst a, snd a) (a :: L)).
                         { destruct a. simpl. auto. } specialize (H1 H5).
                         fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          *** nra.
                          *** apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                            apply Rlt_le. apply  Rinv_lt_contravar .
                            ++++ apply Rmult_lt_0_compat.
                              ---- apply Rmult_lt_0_compat.
                                  **** apply lt_0_INR. lia.
                                  **** apply x_pow_gt_0. unfold u0; simpl; nra.
                              ---- apply Rmult_lt_0_compat.
                                  **** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                  **** apply x_pow_gt_0. unfold u0; simpl; nra.
                            ++++ apply Rmult_lt_compat.
                              ---- apply pos_INR.
                              ---- apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                              ---- unfold nr. 
                                   assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                   apply H1. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                              ---- apply Rlt_pow. unfold u0; simpl; nra. lia.
                +++ auto. 
             ** apply Rabs_ineq. 
                pose proof (prove_rndoff_prod (fst a) (snd a) 2%nat).
                 assert ((1 < 2)%nat). { lia.  } specialize (H5 H6).
                 assert ((2 < Z.to_nat (Z.pow_pos 2 23))%nat).
                 { lia.  } specialize (H5 H7).
                 remember (fst a) as a1.
                 remember (snd a) as a2.
                 assert (Rabs (FT2R a1) <=
                           sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) /\
                           Rabs (FT2R a2) <=
                           sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                 { specialize (H1 a1 a2).
                    assert (In (a1, a2) (a :: L)).
                    { left. simpl. rewrite Heqa1 Heqa2. destruct a. simpl. auto.  }
                    specialize (H1 H8). nra.
                 } destruct H8 as [Ha1 Ha2].
                  pose proof (prove_rndoff_prod a1 a2 2%nat H6).
                  specialize (H8 H7).
                  assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
                  { apply boundsmap_denote_i.
                     2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                     repeat apply list_forall_cons; try apply list_forall_nil;
                      (eexists; split; [|split;[|split]]; try reflexivity; auto;
                        try unfold List.nth; try nra; auto).
                    + specialize (H1 a1 a2).
                      assert (In (a1, a2) (a :: L)).
                      { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H9).
                      apply H1.
                    + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                      apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      - apply Ha2.
                      - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        * apply Rmult_lt_0_compat.
                          ++ apply Rmult_lt_0_compat.
                             -- apply lt_0_INR. lia.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++ apply Rmult_lt_0_compat.
                             -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                        * apply Rmult_lt_compat.
                          ++ apply pos_INR.
                          ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++ unfold nr. 
                             assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                             apply H9. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                          ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                    + specialize (H1 a1 a2).
                      assert (In (a1, a2) (a :: L)).
                      { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H9).
                      apply H1.
                    + apply Rabs_ineq.
                      fold u u0. unfold nr in Ha2.
                      apply Rle_trans with 
                      (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                      - apply Ha1.
                      - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                        apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                        apply Rlt_le. apply  Rinv_lt_contravar .
                        * apply Rmult_lt_0_compat.
                          ++ apply Rmult_lt_0_compat.
                             -- apply lt_0_INR. lia.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                          ++ apply Rmult_lt_0_compat.
                             -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                             -- apply x_pow_gt_0. unfold u0; simpl; nra.
                        * apply Rmult_lt_compat.
                          ++ apply pos_INR.
                          ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                          ++ unfold nr. 
                             assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                             apply H9. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                          ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                  } specialize (H8 H9).  
                  apply Rabs_triang_inv_impl in H8.  apply side_switch in H8.
                  fold u u0 in H8.
                  apply Rle_trans with 
                  (Rabs (FT2R a1 * FT2R a2) +
                          (Rabs (FT2R a1 * FT2R a2) * u0 + u)).
                  +++ nra.
                  +++ rewrite -/u0.
                     apply Rle_trans with 
                     ((sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) *
                               sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)) * (1 + u0) + u).
                    --- rewrite Rabs_mult. 
                       assert (Rabs (FT2R a1) * Rabs (FT2R a2) +
                                (Rabs (FT2R a1) * Rabs (FT2R a2) * u0 + u) = 
                               (Rabs (FT2R a1) * Rabs (FT2R a2)) * (1 +u0) + u).
                       { nra. } rewrite H10. apply Rplus_le_compat_r.
                       apply Rmult_le_compat_r.
                       unfold u0; simpl; nra.
                       apply Rmult_le_compat; try apply Ha1; try apply Ha2.
                       apply Rabs_pos. apply Rabs_pos.
                    --- rewrite sqrt_def .
                       *** unfold nr.
                          assert ((F' / ((INR n+1) * (1 + u0) ^ (n + 1)) - u) * (1 + u0) + u = 
                                   (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * (1+u0)) - u * u0).
                          { nra. } rewrite H10. 
                          assert (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * (1 + u0) = F' / ((INR n+1) * (1 + u0) ^ n)).
                          { assert (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * (1 + u0) =
                                    F' * ( (1+u0) * / ((INR n+1) * (1 + u0) ^ (n + 1)))).
                            { nra. } rewrite H11.
                            assert (((1 + u0) * / ((INR n+1) * (1 + u0) ^ (n + 1))) = 
                                      / ((INR n+1) * (1 + u0) ^ n)).
                            { rewrite Rinv_mult_distr.
                              + rewrite Rinv_mult_distr.
                                - assert ((1 + u0) * (/ (INR n+1) * / (1 + u0) ^ (n + 1)) = 
                                          / (INR n+1) * ((1+u0) * / (1+u0)^(n+1))).
                                  { nra. } rewrite H12. 
                                  assert (((1 + u0) * / (1 + u0) ^ (n + 1)) = / (1 + u0) ^ n).
                                  { assert ((n+1)%nat = S n). { lia. } rewrite H13. 
                                    assert ((1 + u0) ^ S n = (1+u0) * (1+u0)^n).
                                    { simpl. nra. } rewrite H14. 
                                    rewrite Rinv_mult_distr.
                                    + assert ((1 + u0) * (/ (1 + u0) * / (1 + u0) ^ n) = 
                                              ((1 + u0) / (1+u0)) * / (1 + u0) ^ n). { nra. }
                                      rewrite H15. 
                                      assert ((1 + u0) / (1+u0) = 1).
                                      { apply Rinv_r. unfold u0; simpl; nra. }
                                      rewrite H16. nra.
                                    + unfold u0; simpl; nra.
                                    + apply pow_nonzero. unfold u0; simpl; nra.
                                  } rewrite H13. nra.
                                - assert ((0 < INR n + 1) -> INR n + 1 <> 0). { nra. } 
                                  apply H12. apply Rplus_lt_0_compat. 
                                  apply lt_0_INR. lia. nra.
                                - apply  pow_nonzero. unfold u0; simpl; nra.
                              + assert ((0 < INR n + 1) -> INR n + 1 <> 0). { nra. } 
                                  apply H12. apply Rplus_lt_0_compat. 
                                  apply lt_0_INR. lia. nra.
                              + apply  pow_nonzero. unfold u0; simpl; nra.
                            } rewrite H12. nra.
                          } rewrite H11. 
                          apply Rle_trans with (F' / ((INR n + 1) * (1 + u0) ^ n)).
                          unfold u, u0; simpl; nra. apply Rle_trans with (F' / (INR n * (1 + u0) ^ n)).
                          apply Rmult_le_compat_l.
                          unfold F',F_max;simpl;nra. apply Rlt_le. apply Rinv_lt_contravar.
                          ++++ apply Rmult_lt_0_compat.
                               ---- apply Rmult_lt_0_compat. apply lt_0_INR. lia. apply x_pow_gt_0.
                                    unfold u0;simpl;nra.
                               ---- apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia.
                                    nra. apply x_pow_gt_0. unfold u0;simpl;nra.
                          ++++ apply Rmult_lt_compat_r. apply x_pow_gt_0. unfold u0;simpl;nra.
                               nra.
                          ++++ unfold u0;simpl;nra.
                      ***  apply Rge_le. apply Rge_minus. apply Rle_ge.
                           apply pow_invert.
                            **** apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra. 
                              apply x_pow_gt_0. unfold u0; simpl; nra.
                            **** apply Rle_trans with 
                              (u * ((INR n+1) * 3)).
                              ++++ repeat apply Rmult_le_compat_l.
                                 ---- unfold u; simpl; nra.
                                 ---- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                 ---- apply Rlt_le. 
                                     pose proof  (delta_bound (n+1)%nat).
                                     assert ( (n + 1 < Z.to_nat (Z.pow_pos 2 23))%nat).
                                     { lia. } specialize (H10 H11).
                                    fold u0 in H10.
                                    nra.
                              ++++ replace (u * ((INR n+1) * 3)) with ((INR n+1) * (3 * u)) by nra.
                                 apply pow_invert_1.
                                 ---- unfold u;simpl;nra.
                                 ---- apply Rle_trans with 
                                      (IZR (Z.pow_pos 2 23) +1).
                                    ***** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                    ***** unfold u. simpl. unfold F', F_max; simpl; nra.
              -- auto.
           ++ (** TODO: induction step **)
              assert ((1 < S m)%nat). { lia. } 
              specialize (IHL H5).
              assert ((S m < Z.to_nat (Z.pow_pos 2 23) - 1)%nat).
              { apply lt_trans with n; lia. }
              specialize (IHL H6).
              assert ((forall a b : ftype Tsingle,
                         In (a, b) L ->
                         Binary.is_finite (fprec Tsingle)
                           (femax Tsingle) a = true /\
                         Binary.is_finite (fprec Tsingle)
                           (femax Tsingle) b = true /\
                         Rabs (FT2R a) <=
                         sqrt (F' / ((INR (S m)+1) * (1 + u0) ^ (S m + 1)) - u) /\
                         Rabs (FT2R b) <=
                         sqrt (F' / ((INR (S m) +1)* (1 + u0) ^ (S m + 1)) - u))).
              { intros. specialize (H1 a0 b).
                assert (In (a0, b) (a :: L)).
                { simpl. auto.
                } specialize (H1 H8). destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]]. split. auto.
                split. auto. split.
                + apply Rle_trans with 
                  (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                  - nra.
                  - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                    apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                    apply Rlt_le. apply  Rinv_lt_contravar .
                    * apply Rmult_lt_0_compat.
                      ++ apply Rmult_lt_0_compat.
                         -- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                         -- apply x_pow_gt_0. unfold u0; simpl; nra.
                      ++ apply Rmult_lt_0_compat.
                         -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                         -- apply x_pow_gt_0. unfold u0; simpl; nra.
                    * apply Rmult_lt_compat.
                      ++ apply Rplus_le_le_0_compat. apply pos_INR. nra.
                      ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                      ++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia.
                      ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                + apply Rle_trans with 
                  (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                  - nra.
                  - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                    apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                    apply Rlt_le. apply  Rinv_lt_contravar .
                    * apply Rmult_lt_0_compat.
                      ++ apply Rmult_lt_0_compat.
                         -- apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                         -- apply x_pow_gt_0. unfold u0; simpl; nra.
                      ++ apply Rmult_lt_0_compat.
                         -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                         -- apply x_pow_gt_0. unfold u0; simpl; nra.
                    * apply Rmult_lt_compat.
                      ++ apply Rplus_le_le_0_compat. apply pos_INR. nra.
                      ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                      ++ unfold nr. apply Rplus_lt_compat_r. apply lt_INR. lia.
                      ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
               } specialize (IHL H7). clear H7.
              apply Rle_trans with 
              (Rabs (FT2R
                       (sum Tsingle (prod Tsingle (fst a) (snd a))
                          (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                     (FT2R (prod Tsingle (fst a) (snd a)) + 
                       FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)))) +
               Rabs ((FT2R (prod Tsingle (fst a) (snd a)) + 
                       FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                    (FT2R (fst a) * FT2R (snd a) +
                     sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
               -- assert ((FT2R
                           (sum Tsingle (prod Tsingle (fst a) (snd a))
                              (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                         (FT2R (fst a) * FT2R (snd a) +
                          sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))) =
                         (FT2R
                         (sum Tsingle (prod Tsingle (fst a) (snd a))
                            (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                         (FT2R (prod Tsingle (fst a) (snd a)) + 
                           FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)))) + 
                          ((FT2R (prod Tsingle (fst a) (snd a)) + 
                           FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                          (FT2R (fst a) * FT2R (snd a) +
                           sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
                 { nra. } rewrite H7. clear H7.
                 apply Rabs_triang.
               -- pose proof (prove_rndoff (prod Tsingle (fst a) (snd a))
                              (sum_fixF Tsingle (prod_fixF Tsingle L))).
                 specialize (H7 n).
                 assert ((1 < n)%nat). { lia. } specialize (H7 H8).
                 assert (boundsmap_denote (@bmap ty n)
                          (vmap (prod Tsingle (fst a) (snd a))
                            (sum_fixF Tsingle (prod_fixF Tsingle L)))).
                 { apply boundsmap_denote_i.
                   2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                      repeat apply list_forall_cons; try apply list_forall_nil;
                          (eexists; split; [|split;[|split]]; try reflexivity; auto;
                            try unfold List.nth; try nra; auto).
                   + apply IHL.
                   + apply Rabs_ineq. unfold dot_prodF, dot_prodR in IHL. 
                     destruct IHL as [ifHL IHL].
                     apply Rabs_triang_inv_impl in IHL. apply side_switch in IHL.
                     apply Rle_trans with 
                     (Rabs (sum_fixR (prod_fixR (Flist_to_Rlist_pair L))) +
                        (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                         ((1 + u0) ^ S m - 1) +
                         INR (S m) * u * (1 + u0) ^ (S m - 1) +
                         u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                     - nra.
                     - apply Rle_trans with 
                       (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) +
                              (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                               ((1 + u0) ^ S m - 1) + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                               u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                       * apply Rplus_le_compat_r. apply sum_abs_pair_le.
                       * assert (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) +
                                    (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                     ((1 + u0) ^ S m - 1) + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                     u * ((1 + u0) ^ (S m - 1) - 1) / u0) = 
                                 sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) * (1 + u0) ^ S m +
                                 INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                  u * ((1 + u0) ^ (S m - 1) - 1) / u0).
                         { nra. } rewrite H9. clear H9.
                         apply Rle_trans with 
                         (((sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u))^2 * INR (length L)) *
                          (1 + u0) ^ S m + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                            u * ((1 + u0) ^ (S m - 1) - 1) / u0).
                         ++  apply Rplus_le_compat_r. apply Rplus_le_compat_r. 
                             apply Rmult_le_compat_r.
                             -- apply Rlt_le, x_pow_gt_0. unfold u0;simpl; nra. 
                             -- apply (list_sum_pair L (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u))).
                                apply sqrt_pos. intros.
                                specialize (H1 (fst a0) (snd a0)).
                                assert (In (fst a0, snd a0) (a :: L)).
                                { simpl. destruct a0. simpl; auto. }
                                specialize (H1 H10). apply H1.
                         ++ assert (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) ^ 2 = 
                                    (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                            { assert (forall x:R, x^2 = x * x). { intros. nra. } rewrite H9.
                              apply sqrt_sqrt.
                              apply Rge_le. apply Rge_minus. apply Rle_ge.
                               apply pow_invert.
                                * apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra. 
                                  apply x_pow_gt_0. unfold u0; simpl; nra.
                                * apply Rle_trans with 
                                  (u * ((INR n+1) * 3)).
                                  +++ repeat apply Rmult_le_compat_l.
                                     --- unfold u; simpl; nra.
                                     --- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                     --- apply Rlt_le. 
                                         pose proof  (delta_bound (n+1)%nat).
                                         assert ( (n + 1 < Z.to_nat (Z.pow_pos 2 23))%nat).
                                         { lia. } specialize (H10 H11).
                                        fold u0 in H10.
                                        nra.
                                  +++ replace (u * ((INR n+1) * 3)) with ((INR n+1) * (3 * u)) by nra.
                                     apply pow_invert_1.
                                     --- unfold u;simpl;nra.
                                     --- apply Rle_trans with 
                                          (IZR (Z.pow_pos 2 23) +1 ).
                                        *** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                        *** unfold u. simpl. unfold F', F_max; simpl; nra.
                            } rewrite H9. rewrite -Heqm. 
                            assert (S m = (n-1)%nat). { lia. } rewrite H10.
                            assert ((n - 1 - 1)%nat = (n-2)%nat). { lia. } rewrite H11.
                            clear H10 H11.
                            assert ((F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) * INR (n - 1) *
                                      (1 + u0) ^ (n - 1) + INR (n - 1) * u * (1 + u0) ^ (n - 2) +
                                      u * ((1 + u0) ^ (n - 2) - 1) / u0 = 
                                    (F' / ((nr+1) * (1 + u0) ^ (n + 1)) * INR (n-1) *(1 + u0) ^ (n - 1)) + 
                                    ((INR (n - 1) * u * (1 + u0) ^ (n - 2) - INR (n - 1) * u  * (1 + u0) ^ (n - 1)) +
                                    u * ((1 + u0) ^ (n - 2) - 1) / u0)).
                            { nra. } rewrite H10. clear H10.
                            apply Rplus_le_compat.
                            -- unfold nr. 
                               assert (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1) = 
                                       (F' * / ((INR n+1) * (1 + u0) ^ (n + 1))) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1)). { nra. } rewrite H10. clear H10.
                               rewrite Rinv_mult_distr.
                               replace (F' * (INR n - 1) / INR n) with ((F' * (INR n - 1) / INR n) * 1) by nra.
                               assert (F' * (/ (INR n+1) * / (1 + u0) ^ (n + 1)) * INR (n - 1) *
                                          (1 + u0) ^ (n - 1) = 
                                       (F' * (INR n - 1) / (INR n+1)) * ((1 + u0) ^ (n - 1) /(1 + u0) ^ (n + 1))).
                               { rewrite minus_INR. simpl; nra. lia. } rewrite H10. clear H10.
                                apply Rmult_le_compat.
                               **  apply Rmult_le_pos.
                                   +++ apply Rmult_le_pos; try (unfold F', F_max; simpl; nra); try apply pos_INR.
                                       apply Rge_le. apply Rge_minus. apply Rle_ge. 
                                       replace 1 with (INR 1) by (simpl; nra). apply le_INR;lia.
                                   +++ apply Rlt_le. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat. apply lt_0_INR; lia. nra.
                               ** apply Rmult_le_pos. apply pow_le. unfold u0;simpl;nra.
                                  apply Rlt_le, Rinv_0_lt_compat, x_pow_gt_0. unfold u0;simpl;nra.
                               ** repeat apply Rmult_le_compat_l.
                                  +++ apply Rmult_le_pos. unfold F',F_max;simpl;nra.
                                      apply Rge_le, Rge_minus,Rle_ge. replace 1 with (INR 1) by (simpl;nra).
                                      apply le_INR. lia.
                                  +++ apply Rlt_le. apply Rinv_lt_contravar. apply Rmult_lt_0_compat.
                                      apply lt_0_INR. lia. apply Rplus_lt_0_compat.  apply lt_0_INR. lia. nra. nra.
                              ** assert (1 = (1+u0)^(n+1) / (1+u0)^(n+1)).
                                  { symmetry. apply Rinv_r. apply pow_nonzero .
                                    unfold u0;simpl;nra.

                                  } 
                                  assert ( (1 + u0) ^ (n - 1) / (1 + u0) ^ (n + 1) <= 
                                            (1+u0)^(n+1) / (1+u0)^(n+1) ->
                                             (1 + u0) ^ (n - 1) / (1 + u0) ^ (n + 1) <= 1).
                                  { rewrite -H10; nra. } apply H11. apply Rmult_le_compat_r.
                                  +++ apply Rlt_le, Rinv_0_lt_compat. apply x_pow_gt_0. unfold u0;simpl;nra.
                                  +++ apply Rle_pow. unfold u0;simpl;nra. lia.
                               ** assert (0 < INR n + 1 -> INR n + 1 <> 0). { nra. } apply H10.
                                  apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                               ** apply pow_nonzero. unfold u0;simpl;nra.
                            -- match goal with |-context[ _ <= ?a]=>
                                 replace a with (0 + a) by nra
                               end. apply Rplus_le_compat.
                               ** assert ((n - 1)%nat = (S (n-2))%nat). { lia. }
                                  rewrite H10. 
                                  assert (INR (S (n - 2)) * u * (1 + u0) ^ (n - 2) -
                                            INR (S (n - 2)) * u * (1 + u0) ^ S (n - 2)  =
                                          - (u0 * INR (S (n - 2)) * u * (1 + u0) ^ (n - 2))).
                                  { simpl; nra. } rewrite H11.
                                  apply Rge_le. apply Ropp_0_le_ge_contravar.
                                  repeat apply Rmult_le_pos; try (simpl;nra); try nra; try apply pos_INR;
                                  try (apply Rlt_le, x_pow_gt_0; unfold u0; simpl; nra).
                               ** rewrite -/u -/u0. 
                                  replace (u * ((1 + u0) ^ (n - 2) - 1) / u0) with 
                                  (((1 + u0) ^ (n - 2) - 1) * (u / u0)) by nra.
                                  replace (2 * u / u0) with (2 * (u/u0)) by nra.
                                  apply Rmult_le_compat_r.
                                  +++ unfold u,u0; simpl; nra.
                                  +++ apply Rlt_le. apply (delta_bound (n-2)%nat).
                                      apply lt_trans with n; lia.
                   + destruct (prove_rndoff'' (fst a) (snd a) vmap 2%nat).
                      +++ lia.
                      +++ apply two_lt_n.
                      +++ apply boundsmap_denote_i.
                           2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                           repeat apply list_forall_cons; try apply list_forall_nil;
                            (eexists; split; [|split;[|split]]; try reflexivity; auto;
                              try unfold List.nth; try nra; auto).
                           --- specialize (H1 (fst a) (snd a)).
                               assert (In (fst a, snd a) (a :: L)).
                               { destruct a. simpl;auto. } specialize (H1 H9).
                               apply H1.
                           --- apply Rabs_ineq.
                               specialize (H1 (fst a) (snd a)).
                               assert (In (fst a, snd a) (a :: L)).
                               { destruct a. simpl. auto. } specialize (H1 H9).
                               fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                                apply Rle_trans with 
                                (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                                *** nra.
                                *** apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                                  apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                                  apply Rlt_le. apply  Rinv_lt_contravar .
                                  ++++ apply Rmult_lt_0_compat.
                                    ---- apply Rmult_lt_0_compat.
                                        **** apply lt_0_INR. lia.
                                        **** apply x_pow_gt_0. unfold u0; simpl; nra.
                                    ---- apply Rmult_lt_0_compat.
                                        **** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                        **** apply x_pow_gt_0. unfold u0; simpl; nra.
                                  ++++ apply Rmult_lt_compat.
                                    ---- apply pos_INR.
                                    ---- apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                                    ---- unfold nr.
                                         assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                         apply H1. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                                    ---- apply Rlt_pow. unfold u0; simpl; nra. lia.
                           --- specialize (H1 (fst a) (snd a)).
                               assert (In (fst a, snd a) (a :: L)).
                               { destruct a. simpl;auto. } specialize (H1 H9).
                               apply H1.
                           --- apply Rabs_ineq. 
                               specialize (H1 (fst a) (snd a)).
                               assert (In (fst a, snd a) (a :: L)).
                               { destruct a. simpl. auto. } specialize (H1 H9).
                               fold u u0. destruct H1 as [Hfa1 [Hfa2 [Ha1 Ha2]]].
                                apply Rle_trans with 
                                (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                                *** nra.
                                *** apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                                  apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                                  apply Rlt_le. apply  Rinv_lt_contravar .
                                  ++++ apply Rmult_lt_0_compat.
                                    ---- apply Rmult_lt_0_compat.
                                        **** apply lt_0_INR. lia.
                                        **** apply x_pow_gt_0. unfold u0; simpl; nra.
                                    ---- apply Rmult_lt_0_compat.
                                        **** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                        **** apply x_pow_gt_0. unfold u0; simpl; nra.
                                  ++++ apply Rmult_lt_compat.
                                    ---- apply pos_INR.
                                    ---- apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                                    ---- unfold nr. 
                                         assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                         apply H1. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                                    ---- apply Rlt_pow. unfold u0; simpl; nra. lia.
                      +++ auto. 
                   + apply Rabs_ineq. 
                     pose proof (prove_rndoff_prod (fst a) (snd a) 2%nat).
                     assert ((1 < 2)%nat). { lia.  } specialize (H9 H10).
                     assert ((2 < Z.to_nat (Z.pow_pos 2 23))%nat).
                     { lia.  } specialize (H9 H11).
                     remember (fst a) as a1.
                     remember (snd a) as a2.
                     assert (Rabs (FT2R a1) <=
                               sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) /\
                               Rabs (FT2R a2) <=
                               sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                     { specialize (H1 a1 a2).
                        assert (In (a1, a2) (a :: L)).
                        { left. simpl. rewrite Heqa1 Heqa2. destruct a. simpl. auto.  }
                        specialize (H1 H12). nra.
                     } destruct H12 as [Ha1 Ha2].
                      pose proof (prove_rndoff_prod a1 a2 2%nat H10).
                      specialize (H12 H11).
                      assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
                      { apply boundsmap_denote_i.
                         2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                         repeat apply list_forall_cons; try apply list_forall_nil;
                          (eexists; split; [|split;[|split]]; try reflexivity; auto;
                            try unfold List.nth; try nra; auto).
                        + specialize (H1 a1 a2).
                          assert (In (a1, a2) (a :: L)).
                          { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H13).
                          apply H1.
                        + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          - apply Ha2.
                          - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                            apply Rlt_le. apply  Rinv_lt_contravar .
                            * apply Rmult_lt_0_compat.
                              ++ apply Rmult_lt_0_compat.
                                 -- apply lt_0_INR. lia.
                                 -- apply x_pow_gt_0. unfold u0; simpl; nra.
                              ++ apply Rmult_lt_0_compat.
                                 -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                 -- apply x_pow_gt_0. unfold u0; simpl; nra.
                            * apply Rmult_lt_compat.
                              ++ apply pos_INR.
                              ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                              ++ unfold nr. 
                                 assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                         apply H13. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                              ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                        + specialize (H1 a1 a2).
                          assert (In (a1, a2) (a :: L)).
                          { destruct a. rewrite Heqa1 Heqa2. simpl. auto. } specialize (H1 H13).
                          apply H1.
                        + apply Rabs_ineq.
                          fold u u0. unfold nr in Ha2.
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          - apply Ha1.
                          - apply sqrt_le_1_alt. apply Rplus_le_compat_r.
                            apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                            apply Rlt_le. apply  Rinv_lt_contravar .
                            * apply Rmult_lt_0_compat.
                              ++ apply Rmult_lt_0_compat.
                                 -- apply lt_0_INR. lia.
                                 -- apply x_pow_gt_0. unfold u0; simpl; nra.
                              ++ apply Rmult_lt_0_compat.
                                 -- unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra.
                                 -- apply x_pow_gt_0. unfold u0; simpl; nra.
                            * apply Rmult_lt_compat.
                              ++ apply pos_INR.
                              ++ apply Rlt_le, x_pow_gt_0. unfold u0; simpl; nra.
                              ++ unfold nr.
                                 assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                 apply H13. replace 1 with (INR 1) by (simpl;nra). apply lt_INR. lia.
                              ++ apply Rlt_pow. unfold u0; simpl; nra. lia.
                      } specialize (H12 H13). 
                      apply Rabs_triang_inv_impl in H12.  apply side_switch in H12.
                      fold u u0 in H12.
                      apply Rle_trans with 
                      (Rabs (FT2R a1 * FT2R a2) +
                              (Rabs (FT2R a1 * FT2R a2) * u0 + u)).
                      ++ nra.
                      ++ rewrite -/u0.
                         apply Rle_trans with 
                         ((sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) *
                                   sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)) * (1 + u0) + u).
                        -- rewrite Rabs_mult. 
                           assert (Rabs (FT2R a1) * Rabs (FT2R a2) +
                                    (Rabs (FT2R a1) * Rabs (FT2R a2) * u0 + u) = 
                                   (Rabs (FT2R a1) * Rabs (FT2R a2)) * (1 +u0) + u).
                           { nra. } rewrite H14. apply Rplus_le_compat_r.
                           apply Rmult_le_compat_r.
                           unfold u0; simpl; nra.
                           apply Rmult_le_compat; try apply Ha1; try apply Ha2.
                           apply Rabs_pos. apply Rabs_pos.
                        -- rewrite sqrt_def .
                           ** unfold nr.
                              assert ((F' / ((INR n+1) * (1 + u0) ^ (n + 1)) - u) * (1 + u0) + u = 
                                       (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * (1+u0)) - u * u0).
                              { nra. } rewrite H14. 
                              assert (F' / ((INR n +1)* (1 + u0) ^ (n + 1)) * (1 + u0) = F' / ((INR n+1) * (1 + u0) ^ n)).
                              { assert (F' / ((INR n+1) * (1 + u0) ^ (n + 1)) * (1 + u0) =
                                        F' * ( (1+u0) * / ((INR n+1) * (1 + u0) ^ (n + 1)))).
                                { nra. } rewrite H15.
                                assert (((1 + u0) * / ((INR n+1) * (1 + u0) ^ (n + 1))) = 
                                          / ((INR n+1) * (1 + u0) ^ n)).
                                { rewrite Rinv_mult_distr.
                                  + rewrite Rinv_mult_distr.
                                    - assert ((1 + u0) * (/ (INR n+1) * / (1 + u0) ^ (n + 1)) = 
                                              / (INR n+1) * ((1+u0) * / (1+u0)^(n+1))).
                                      { nra. } rewrite H16. 
                                      assert (((1 + u0) * / (1 + u0) ^ (n + 1)) = / (1 + u0) ^ n).
                                      { assert ((n+1)%nat = S n). { lia. } rewrite H17. 
                                        assert ((1 + u0) ^ S n = (1+u0) * (1+u0)^n).
                                        { simpl. nra. } rewrite H18. 
                                        rewrite Rinv_mult_distr.
                                        + assert ((1 + u0) * (/ (1 + u0) * / (1 + u0) ^ n) = 
                                                  ((1 + u0) / (1+u0)) * / (1 + u0) ^ n). { nra. }
                                          rewrite H19. 
                                          assert ((1 + u0) / (1+u0) = 1).
                                          { apply Rinv_r. unfold u0; simpl; nra. }
                                          rewrite H20. nra.
                                        + unfold u0; simpl; nra.
                                        + apply pow_nonzero. unfold u0; simpl; nra.
                                      } rewrite H17. nra.
                                    - assert (0 < INR n +1 -> INR n + 1 <> 0). { nra. } apply H16.
                                      apply Rplus_lt_0_compat. apply lt_0_INR;lia. nra.
                                    - apply  pow_nonzero. unfold u0; simpl; nra.
                                  + assert (0 < INR n +1 -> INR n + 1 <> 0). { nra. } apply H16.
                                      apply Rplus_lt_0_compat. apply lt_0_INR;lia. nra.

                                  + apply  pow_nonzero. unfold u0; simpl; nra.
                                } rewrite H16. nra.
                              } rewrite H15. 
                              apply Rle_trans with (F' / ((INR n + 1) * (1 + u0) ^ n)).
                              +++ unfold u, u0; simpl; nra.
                              +++ apply Rle_trans with (F' / (INR n * (1 + u0) ^ n)). 
                                  apply Rmult_le_compat_l. unfold F',F_max;simpl;nra.
                                  apply Rlt_le. apply Rinv_lt_contravar.
                                  --- apply Rmult_lt_0_compat.
                                      *** apply Rmult_lt_0_compat. apply lt_0_INR;lia.
                                          apply x_pow_gt_0. unfold u0;simpl;nra.
                                      *** apply Rmult_lt_0_compat. apply Rplus_lt_0_compat.
                                          apply lt_0_INR. lia. nra. apply x_pow_gt_0. unfold u0;simpl;nra.
                                  --- apply Rmult_lt_compat_r. apply x_pow_gt_0. unfold u0;simpl;nra. nra.
                                  --- unfold u0;simpl;nra.
                           **  apply Rge_le. apply Rge_minus. apply Rle_ge.
                               apply pow_invert.
                                * apply Rmult_lt_0_compat. apply Rplus_lt_0_compat. apply lt_0_INR. lia. nra. 
                                  apply x_pow_gt_0. unfold u0; simpl; nra.
                                * apply Rle_trans with 
                                  (u * ((INR n+1) * 3)).
                                  +++ repeat apply Rmult_le_compat_l.
                                     --- unfold u; simpl; nra.
                                     --- apply Rplus_le_le_0_compat. apply pos_INR. nra.
                                     --- apply Rlt_le. 
                                         pose proof  (delta_bound (n+1)%nat).
                                         assert ( (n + 1 < Z.to_nat (Z.pow_pos 2 23))%nat).
                                         { lia. } specialize (H14 H15).
                                        fold u0 in H14.
                                        nra.
                                  +++ replace (u * ((INR n+1) * 3)) with ((INR n+1) * (3 * u)) by nra.
                                     apply pow_invert_1.
                                     --- unfold u;simpl;nra.
                                     --- apply Rle_trans with 
                                          (IZR (Z.pow_pos 2 23) +1 ).
                                        *** apply Rlt_le. rewrite INR_IZR_INZ. apply Rplus_lt_compat_r. apply IZR_lt. lia.
                                        *** unfold u. simpl. unfold F', F_max; simpl; nra.
                 } specialize (H7 H9). fold u u0 in H7.
                 apply Rle_trans with 
                 ((Rabs (FT2R (prod Tsingle (fst a) (snd a)) +
                        FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) * u0 + u) +
                  (Rabs (FT2R (prod Tsingle (fst a) (snd a)) - FT2R (fst a) * FT2R (snd a)) +
                    Rabs (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                        sum_fixR (prod_fixR (Flist_to_Rlist_pair L))) )).
                 ** apply Rplus_le_compat.
                    +++ nra.
                    +++ assert ((FT2R (prod Tsingle (fst a) (snd a)) +
                                 FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                                 (FT2R (fst a) * FT2R (snd a) +
                                  sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))) = 
                                (FT2R (prod Tsingle (fst a) (snd a)) - FT2R (fst a) * FT2R (snd a)) + 
                                (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) - 
                                    sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))).
                       { nra. } rewrite H10. apply Rabs_triang.
                 **  pose proof (prove_rndoff_prod (fst a) (snd a) 2%nat).
                     assert ((1 < 2)%nat). { lia. } specialize (H10 H11).
                     assert ((2 < Z.to_nat (Z.pow_pos 2 23))%nat).
                     { lia. } specialize (H10 H12). 
                     remember (fst a) as a1.
                     remember (snd a) as a2.
                     assert (Rabs (FT2R a1) <=
                               sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u) /\
                               Rabs (FT2R a2) <=
                               sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                     { specialize (H1 a1 a2).
                        assert (In (a1, a2) (a :: L)).
                        { rewrite Heqa1 Heqa2. destruct a. simpl. auto.  }
                        specialize (H1 H13). nra.
                     } destruct H13 as [Ha1 Ha2].
                      pose proof (prove_rndoff_prod a1 a2 2%nat H11 H12).
                      assert (boundsmap_denote (@bmap_prod Tsingle 2) (vmap a1 a2)).
                      { apply boundsmap_denote_i.
                         2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
                         repeat apply list_forall_cons; try apply list_forall_nil;
                          (eexists; split; [|split;[|split]]; try reflexivity; auto;
                            try unfold List.nth; try nra; auto).
                        + specialize (H1 a1 a2).
                          assert (In (a1, a2) (a :: L)).
                          { rewrite Heqa1 Heqa2. destruct a. simpl; auto. }
                          apply H1. auto.
                        + apply Rabs_ineq. fold u u0. unfold nr in Ha2.
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          - apply Ha2.
                          - apply sqrt_le_1_alt. apply Rplus_le_compat_r. apply Rmult_le_compat_l.
                            unfold F', F_max; simpl; nra.
                            assert (n= 2%nat \/ (2 < n)%nat). { lia. } destruct H14.
                            * unfold nr. rewrite H14. rewrite Rinv_mult_distr. 
                              ++ rewrite Rinv_mult_distr. apply Rmult_le_compat. simpl; nra.
                                 apply Rlt_le. apply Rinv_0_lt_compat.  
                                 try (unfold u0;simpl;nra). simpl;nra. try (unfold u0;simpl;nra).
                                 simpl;nra. unfold u0; simpl; nra.
                              ++ simpl; nra.
                              ++ unfold u0; simpl; nra.
                            * apply Rlt_le. apply Rinv_lt_contravar.
                              ++ apply Rmult_lt_0_compat.
                                 -- unfold u0; simpl; nra.
                                 -- apply Rmult_lt_0_compat.
                                    ** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR; lia. nra.
                                    ** apply x_pow_gt_0. unfold u0; simpl; nra. 
                              ++ unfold nr. apply Rmult_lt_compat.
                                 -- simpl; nra.
                                 -- unfold u0; simpl; nra.
                                 -- assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                    apply H15. replace 1 with (INR 1) by (simpl;nra). apply lt_INR; lia.
                                 -- apply Rlt_pow. unfold u0; simpl; nra. lia.
                        + specialize (H1 a1 a2).
                          assert (In (a1, a2) (a :: L)).
                          { rewrite Heqa1 Heqa2. destruct a. simpl; auto. }
                          apply H1. auto.
                        + apply Rabs_ineq. fold u u0. unfold nr in Ha1.
                          apply Rle_trans with 
                          (sqrt (F' / ((nr+1) * (1 + u0) ^ (n + 1)) - u)).
                          - apply Ha1.
                          - apply sqrt_le_1_alt. apply Rplus_le_compat_r. apply Rmult_le_compat_l.
                            unfold F', F_max; simpl; nra.
                            assert (n= 2%nat \/ (2 < n)%nat). { lia. } destruct H14.
                            * unfold nr. rewrite H14. rewrite Rinv_mult_distr. 
                              ++ rewrite Rinv_mult_distr. unfold u0; simpl; nra.
                                 simpl; nra. unfold u0; simpl; nra.
                              ++ simpl; nra.
                              ++ unfold u0; simpl; nra.
                            * apply Rlt_le. apply Rinv_lt_contravar.
                              ++ apply Rmult_lt_0_compat.
                                 -- unfold u0; simpl; nra.
                                 -- apply Rmult_lt_0_compat.
                                    ** unfold nr. apply Rplus_lt_0_compat. apply lt_0_INR; lia. nra.
                                    ** apply x_pow_gt_0. unfold u0; simpl; nra. 
                              ++ unfold nr. apply Rmult_lt_compat.
                                 -- simpl; nra.
                                 -- unfold u0; simpl; nra.
                                 -- assert (1 < INR n -> INR 2 < INR n + 1). { simpl;nra. }
                                    apply H15. replace 1 with (INR 1) by (simpl;nra). apply lt_INR; lia.
                                 -- apply Rlt_pow. unfold u0; simpl; nra. lia.
                       } specialize (H13 H14). fold u u0 in H13.
                       unfold dot_prodF, dot_prodR in IHL.
                       apply Rle_trans with 
                       ((Rabs
                        (FT2R (prod Tsingle a1 a2) +
                         FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) * u0 + u) +
                        ((Rabs (FT2R a1 * FT2R a2) * u0 + u) + 
                        (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                          ((1 + u0) ^ S m - 1) +
                          INR (S m) * u * (1 + u0) ^ (S m - 1) +
                          u * ((1 + u0) ^ (S m - 1) - 1) / u0))).
                        +++ apply Rplus_le_compat_l. apply Rplus_le_compat; nra.
                        +++ apply Rabs_triang_inv_impl in H13. apply side_switch in H13.
                          apply Rle_trans with
                          ((((Rabs (FT2R a1 * FT2R a2)* (1+u0) + u) +
                             (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) * (1 + u0) ^ S m +
                              INR (S m) * u * (1 + u0) ^ (S m - 1) +
                              u * ((1 + u0) ^ (S m - 1) - 1) / u0))* u0 + u) +
                            (Rabs (FT2R a1 * FT2R a2) * u0 + u +
                               (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                ((1 + u0) ^ S m - 1) +
                                INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                u * ((1 + u0) ^ (S m - 1) - 1) / u0))).
                          --- apply Rplus_le_compat_r. 
                              apply Rle_trans with 
                              ((Rabs (FT2R (prod Tsingle a1 a2)) + 
                               Rabs (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)))) * u0 + u).
                              *** apply Rplus_le_compat_r. apply Rmult_le_compat_r. 
                                  unfold u0; simpl; nra. apply Rabs_triang.
                              *** apply Rplus_le_compat_r. apply Rmult_le_compat_r.
                                  unfold u0;simpl;nra. apply Rplus_le_compat.
                                  nra. destruct IHL as [ifHL IHL].
                                  apply Rabs_triang_inv_impl in IHL. apply side_switch in IHL. 
                                  apply Rle_trans with
                                  (Rabs (sum_fixR (prod_fixR (Flist_to_Rlist_pair L))) +
                                    (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                     ((1 + u0) ^ S m - 1) +
                                     INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                     u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                                  ++++ nra.
                                  ++++ apply Rle_trans with
                                      (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) +
                                          (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                           ((1 + u0) ^ S m - 1) + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                           u * ((1 + u0) ^ (S m - 1) - 1) / u0)).
                                      ---- apply Rplus_le_compat_r. apply sum_abs_pair_le.
                                      ---- nra.
                          --- rewrite Rabs_mult.
                              assert ((Rabs (FT2R a1) * Rabs (FT2R a2) * (1 + u0) + u +
                                       (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                        (1 + u0) ^ S m + INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                        u * ((1 + u0) ^ (S m - 1) - 1) / u0)) * u0 + u +
                                      (Rabs (FT2R a1) * Rabs (FT2R a2) * u0 + u +
                                       (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) *
                                        ((1 + u0) ^ S m - 1) +
                                        INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                        u * ((1 + u0) ^ (S m - 1) - 1) / u0)) = 
                                      ((Rabs (FT2R a1) * Rabs (FT2R a2)) * (u0 * (1+u0) + u0) +
                                      ((sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) * 
                                          (u0 * (1 + u0) ^ S m + ((1 + u0) ^ S m - 1))) +
                                      (u * u0 + u0 * INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                        u0 * u * ((1 + u0) ^ (S m - 1) - 1) / u0 + 2* u +
                                        INR (S m) * u * (1 + u0) ^ (S m - 1) + 
                                        u * ((1 + u0) ^ (S m - 1) - 1) / u0)))). { nra. }
                              rewrite H15. clear H15.
                              assert ((Rabs (FT2R a1) * Rabs (FT2R a2) +
                                         sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L))) *
                                        ((1 + u0) * (1 + u0) ^ S m - 1) +
                                        nr * u * (1 + u0) ^ (S m - 0) +
                                        u * ((1 + u0) ^ (S m - 0) - 1) / u0 = 
                                      ((Rabs (FT2R a1) * Rabs (FT2R a2)) * ((1 + u0) * (1 + u0) ^ S m - 1) +
                                      (sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)) * ((1 + u0) * (1 + u0) ^ S m - 1) +
                                      (nr * u * (1 + u0) ^ (S m - 0) +
                                        u * ((1 + u0) ^ (S m - 0) - 1) / u0)))). { nra. } rewrite H15.
                              apply Rplus_le_compat.
                              ++++ apply Rmult_le_compat_l.
                                  *** repeat apply Rmult_le_pos; apply Rabs_pos.
                                  *** assert (u0 * (1 + u0) + u0 = (1+u0)^2 - 1).
                                      { nra. } rewrite H16. apply Rplus_le_compat_r.
                                      assert ((1 + u0) * (1 + u0) ^ S m = (1+u0)^(S m +1)).
                                      { simpl. assert (S m = (m+1)%nat). { lia. } rewrite -H17. simpl. nra. }
                                      rewrite H17. apply Rle_pow. unfold u0; simpl; nra. lia.
                              ++++ apply Rplus_le_compat.
                                  *** apply Rmult_le_compat_l.
                                      ---- apply sum_abs_pair_rel.
                                      ---- nra.
                                  *** unfold nr. 
                                      assert ((S m - 0)%nat = S m). { lia. } rewrite H16.
                                      rewrite H2. rewrite plus_INR. change (INR 1) with 1. 
                                      assert (u * u0 + u0 * INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                                u0 * u * ((1 + u0) ^ (S m - 1) - 1) / u0 + 2 * u +
                                                INR (S m) * u * (1 + u0) ^ (S m - 1) +
                                                u * ((1 + u0) ^ (S m - 1) - 1) / u0 = 
                                              u * u0 + (INR (S m) * u * (1+u0)* (1+u0)^(S m -1)) +
                                              u0 * u * ((1 + u0) ^ (S m - 1) - 1) / u0 + 2 * u  +
                                              u * ((1 + u0) ^ (S m - 1) - 1) / u0).
                                      { nra. } rewrite H17. clear H17.
                                      assert (INR (S m) * u * (1 + u0) * (1 + u0) ^ (S m - 1) = 
                                              INR (S m) * u * (1+u0)^(S m)).
                                      { assert (S m = S (S m -1)). { lia. } 
                                        assert (INR (S m) * u * (1 + u0) ^ S m = INR (S m) * u * (1 + u0) ^ S (S m -1)).
                                        { by rewrite -H17. } rewrite H18. simpl. nra.
                                      } rewrite H17. 
                                      assert (u * u0 + INR (S m) * u * (1 + u0) ^ S m +
                                              u0 * u * ((1 + u0) ^ (S m - 1) - 1) / u0 + 
                                              2 * u + u * ((1 + u0) ^ (S m - 1) - 1) / u0  =
                                              u * u0 + INR (S m) * u * (1 + u0) ^ S m +
                                              u * (1+u0)* ((1 + u0) ^ (S m - 1) - 1) / u0 + 2 * u).
                                      { nra. } rewrite H18. clear H18.
                                      assert (u * (1 + u0) * ((1 + u0) ^ (S m - 1) - 1) / u0 =
                                              u * (1+u0) * (1 + u0) ^ (S m - 1) / u0  - u * (1+u0) / u0).
                                      { nra. } rewrite H18. clear H18.
                                      assert ( u * (1+u0) * (1 + u0) ^ (S m - 1) / u0 = 
                                                u * (1+u0)^(S m) / u0).
                                      { assert (S m = S (S m -1)). { lia. }
                                        assert (u * (1+u0)^(S m) / u0 = u * (1+u0)^(S (S m -1)) / u0).
                                        { by rewrite -H18. } rewrite H19. simpl. nra.
                                      } rewrite H18.
                                      assert (u * ((1 + u0) ^ S m - 1) / u0 = 
                                              (u * (1 + u0) ^ S m) / u0 - u / u0).
                                      { nra. } rewrite H19. 
                                      assert ((INR (S m) + 1) * u * (1 + u0) ^ S m  = 
                                              INR (S m) * u * (1 + u0) ^ S m + u * (1 + u0) ^ S m).
                                      { nra. } rewrite H20.
                                      assert (u * u0 + INR (S m) * u * (1 + u0) ^ S m +
                                              (u * (1 + u0) ^ S m / u0 - u * (1 + u0) / u0) + 
                                              2 * u = 
                                              (INR (S m) * u * (1 + u0) ^ S m + u * (1 + u0) ^ S m / u0) +
                                              (u * (1 + u0) - u / u0)).
                                      { unfold u, u0; simpl; nra. } rewrite H21.
                                      assert (INR (S m) * u * (1 + u0) ^ S m + u * (1 + u0) ^ S m +
                                                (u * (1 + u0) ^ S m / u0 - u / u0) =
                                              (INR (S m) * u * (1 + u0) ^ S m + u * (1 + u0) ^ S m / u0) +
                                              (u * (1 + u0) ^ S m - u / u0)).
                                      { nra. } rewrite H22.
                                      apply Rplus_le_compat_l. apply Rplus_le_compat_r.
                                      apply Rmult_le_compat_l. unfold u; simpl; nra.
                                      assert (1 + u0 = (1+u0)^1). { nra. } rewrite H23.
                                      assert (((1 + u0) ^ 1) ^ S m = (1+u0)^ S m).
                                      { simpl. rewrite Rmult_1_r. nra. } rewrite H24.
                                      apply Rle_pow. unfold u0; simpl; nra. lia.
Qed.


(** Using Coq's combine function to combibe two lists to get a 
    list of pairs
**)
Lemma forward_error_dot_precise:
  forall (L1 L2: list (ftype Tsingle)),
  let L := combine L1 L2 in
  let ty := Tsingle in 
  let n:= length L in 
  let nr := INR n in
  (1 < n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (n < Z.to_nat (Z.pow_pos 2 23) - 1)%nat ->
  (forall a b : ftype Tsingle,
              In (a,b) L ->
              Binary.is_finite (fprec Tsingle)
              (femax Tsingle) a = true /\
              Binary.is_finite (fprec Tsingle)
                (femax Tsingle) b = true /\
              Rabs (FT2R a) <=  sqrt( F' / ((nr+1) * (1+u0)^(n+1)) - u ) /\
              Rabs (FT2R b) <=  sqrt( F' / ((nr+1) * (1+u0)^(n+1)) - u )) ->
  is_finite (fprec Tsingle) (femax Tsingle)
  (dot_prodF _ L) = true /\
  Rabs (FT2R (dot_prodF _ L) - dot_prodR (Flist_to_Rlist_pair L)) <=
  (dot_prodR (Flist_to_Rlist_pair_abs L)) * ((1 + u0)^n -1) + 
  nr * u * (1+u0)^(n-1) + u * ((1+u0)^(n-1) -1) / u0.
Proof.
intros.
by apply forward_error_dot_aux.
Qed.


End WITHNANS.
(** Rough work. Might need it later **)

Lemma sqrt_full_le: 
  forall x:R,
  (1 <= x)%Re ->
  (sqrt x <= x)%Re.
Proof.
intros. 
assert ((sqrt x <= sqrt x * sqrt x)%Re -> 
        (sqrt x <= x)%Re).
{ rewrite sqrt_def. nra. nra. }
apply H0. 
assert ((sqrt x * 1<= sqrt x * sqrt x)%Re ->
        (sqrt x <= sqrt x * sqrt x)%Re).
{ nra. } apply H1.
apply Rmult_le_compat_l.
apply sqrt_pos.
replace 1%Re with (sqrt 1%Re); try by rewrite sqrt_1.
apply  sqrt_le_1_alt. nra.
Qed.


Print default_rel.
Print Z.pow_pos.

(*
Lemma C_ge_0 (m n:nat):
  (0 <= C m n)%Re.
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
  (n <= m)%coq_nat -> 
  (INR (fact m) / INR (fact (m - n)%coq_nat) <= INR (m ^ n))%Re.
Proof.
intros.
induction n.
+ simpl. 
  assert ((m - 0)%coq_nat = m). { lia. } rewrite H0.
  assert ((INR (fact m) / INR (fact m) )%Re= 1%Re).
  { apply Rinv_r. apply not_0_INR. apply fact_neq_0. }
  rewrite H1. nra.
+ simpl.
  assert ((n <= m)%coq_nat).
  { lia. } specialize (IHn H0).
  rewrite mult_INR. 
  assert (INR (fact (m - S n)%coq_nat) =  (INR (fact (m - n)%coq_nat) * / INR (m - n)%coq_nat )%Re).
  { assert ((m-n)%coq_nat = S (m - S n)%coq_nat).
    { lia.  } 
    assert (fact (m - n)%coq_nat = fact (S (m - S n)%coq_nat)).
    { by rewrite H1. } rewrite H2. simpl.
    assert ((fact (m - S n)%coq_nat + (m - S n)%coq_nat * fact (m - S n)%coq_nat)%coq_nat = 
            ((m - n)%coq_nat * fact (m - S n)%coq_nat)%coq_nat).
    { assert ((fact (m - n.+1)%coq_nat +
                (m - n.+1)%coq_nat * fact (m - n.+1)%coq_nat)%coq_nat = 
              (fact (m - n.+1)%coq_nat * 1%nat +
                (m - n.+1)%coq_nat * fact (m - n.+1)%coq_nat)%coq_nat).
      { lia.

lia. } rewrite H3. rewrite mult_INR.
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
*)

Require Import generalize.

Lemma pow_1: forall n:nat,
  (1^n)%Re = 1%Re.
Admitted.

Require Import Coq.ZArith.Znat.
Lemma fact_distr {n: nat}:
  (fact n + n * fact n)%nat =
  (fact n * (n + 1))%nat.
Admitted.

Lemma ratio_gt_0 {ty}:
  forall m:nat, 
  let u0 := default_rel ty in
  (m < 2 ^ (Z.to_nat (fprec ty)))%nat ->
  (0 < (1 - INR m * u0 / INR 2))%Re.
Admitted.
(*
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
  
*)

Lemma delta_bound {ty} :
  forall m:nat, 
  let u0 := default_rel ty in
  (m < 2 ^ (Z.to_nat (fprec ty)))%nat ->
  (((1 + u0) ^ m - 1) < 2)%Re.
Proof.
intros.
assert (((1 + u0) ^ m  < 3)%Re -> ((1 + u0) ^ m - 1 < 2)%Re).
{ nra. } apply H0.
assert ((1+u0)%Re = (u0 + 1)%Re). { nra. } rewrite H1. clear H1.
rewrite binomial.
apply Rle_lt_trans with
(sum_f_R0 (fun i : nat => ((INR (m ^ i) / INR (fact i)) * u0 ^ i * 1 ^ (m - i))%Re) m).
+ apply sum_Rle. intros.
  rewrite Rmult_assoc. 
  match goal with |-context[(_ <= ?a * ?b * ?c)%Re]=>
    replace (a * b * c)%Re with (a * (b * c))%Re by nra
  end. apply Rmult_le_compat.
  - apply C_ge_0 .
  - apply Rmult_le_pos. try apply Rlt_le,x_pow_gt_0;try nra.
    unfold u0. apply default_rel_gt_0. simpl.
    apply Rlt_le. apply pow_lt. nra.
  - unfold C. 
    assert ((INR (fact m) / (INR (fact n) * INR (fact (m - n))))%Re = 
              ((INR (fact m) / INR (fact (m-n))) * / INR (fact n))%Re).
    { assert ((INR (fact m) / (INR (fact n) * INR (fact (m - n))))%Re = 
              (INR (fact m) * / (INR (fact n) * INR (fact (m - n))))%Re).
      { nra. } rewrite H2. 
      rewrite Rinv_mult_distr; try nra; try apply not_0_INR, fact_neq_0.
    } rewrite H2. apply Rmult_le_compat_r.
    * apply Rlt_le, Rinv_0_lt_compat. apply lt_0_INR. apply lt_O_fact.
    * apply fact_bound;lia.
  - rewrite pow_1. nra.
+ assert (m = 0%nat \/ (0 < m)%nat). { admit. } destruct H1.
  - rewrite H1. simpl. nra.
  - apply Rle_lt_trans with 
    (1 + INR m *u0 * sum_f_R0 (fun i: nat => (INR (m^i) * u0^i / INR (2^i))%Re) (m-1)%nat)%Re.
    * rewrite decomp_sum.
      ++ simpl.
         assert ((1 / 1 * 1 * 1 ^ (m - 0)%nat)%Re = 1%Re). { rewrite pow1. nra. }
         rewrite H2. clear H2.
         apply Rplus_le_compat_l.
         rewrite scal_sum. 
         assert ((m - 1)%nat = (Init.Nat.pred m)). { by rewrite -subn1. } rewrite H2.
         apply sum_Rle. intros.
         rewrite !mult_INR. rewrite pow1.
         assert ((INR m * INR (m ^ n) / INR (fact n + n * fact n) *
                    (u0 * u0 ^ n) * 1)%Re = 
                 (( INR (m ^ n) / INR (fact n + n * fact n) * u0^n) * 
                 (INR m * u0) )%Re).
         { nra. } rewrite H4. apply Rmult_le_compat_r.
         -- apply Rmult_le_pos. apply pos_INR. unfold u0;simpl.
            apply default_rel_ge_0.
         -- rewrite Rmult_assoc. 
            assert ((INR (m ^ n) * u0 ^ n / INR (2 ^ n))%Re = 
                    (INR (m ^ n) * ( / INR (2 ^ n) * u0^n))%Re).
            { nra. } rewrite H5. apply Rmult_le_compat_l.
            ** apply pos_INR.
            ** apply Rmult_le_compat_r. 
               apply pow_le. unfold u0. apply default_rel_ge_0.
               assert (n = 0%nat \/ (0 < n)%nat).
               { admit. } destruct H6. 
               +++ rewrite H6. simpl. nra.
               +++ assert (n = 1%nat \/ (1 < n)%nat). { admit. } destruct H7.
                   --- rewrite H7. simpl. nra.
                   --- apply Rlt_le, Rinv_lt_contravar.
                       *** apply Rmult_lt_0_compat. apply lt_0_INR. 
                           apply pow_2_gt_0. apply lt_0_INR. apply /ssrnat.ltP.
                           rewrite addn_gt0. apply /orP. left. apply /ssrnat.ltP. apply lt_O_fact. 
                       *** assert ((fact n + n * fact n)%nat = (fact n * (n+1))%nat).
                           { by rewrite fact_distr. }
                           rewrite H8. apply fact_low_bound. by apply /ssrnat.ltP.
      ++ by apply /ssrnat.ltP.
   * assert (sum_f_R0 (fun i : nat =>
                          (INR (m ^ i) * u0 ^ i / INR (2 ^ i))%Re)  (m - 1) = 
             sum_f_R0 (fun i : nat => ((INR m * u0 / INR 2)^i)%Re) (m-1)).
     { apply sum_eq. intros.
       rewrite !pow_INR. rewrite [in RHS]Rpow_mult_distr.
       rewrite Rpow_mult_distr. rewrite -Rinv_pow. nra.
       simpl; nra.
     } rewrite H2. clear H2.
     assert ((m - 1)%nat = (Init.Nat.pred m)). { by rewrite -subn1. } rewrite H2.
     pose proof (GP_finite (INR m * u0 / INR 2) (Init.Nat.pred m) ).
     apply pow_invert_eq in H3.
     ++ rewrite H3.
        assert ((Init.Nat.pred m + 1)%coq_nat = m). { rewrite -subn1. admit. } rewrite H4.
        assert (((INR m * u0 * / ( INR m * u0 / INR 2 - 1)) *  
                  ((INR m * u0 / INR 2) ^ m - 1) < 2)%Re -> (1 +
                  INR m * u0 *
                  (((INR m * u0 / INR 2) ^ m - 1) /
                   (INR m * u0 / INR 2 - 1)) < 3)%Re).
        { intros. nra. } apply H5. clear H5.
        assert ((INR m * u0 * / (INR m * u0 / INR 2 - 1) *
                    ((INR m * u0 / INR 2) ^ m - 1))%Re = 
                 (INR m * u0 * / (1 - INR m * u0 / INR 2) *
                    (1 - (INR m * u0 / INR 2) ^ m ))%Re).
        { assert ((INR m * u0 / INR 2 - 1)%Re = (- ((1 - INR m * u0 / INR 2)))%Re).
          { nra. } rewrite H5.
          assert (((INR m * u0 / INR 2)^m - 1)%Re = (- ((1 - (INR m * u0 / INR 2)^m)))%Re).
          { nra. } rewrite H6. 
          rewrite -Ropp_inv_permute. 
          + nra.
          + pose proof (ratio_gt_0 H).
            assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    (1 - INR m * u0 / INR 2)%Re <> 0%Re).
            { nra. } apply H8. unfold u0. apply H7.
        } rewrite H5.
        replace 2%Re with (2 * 1)%Re by nra.
        apply Rmult_lt_compat.
        -- apply Rmult_le_pos.
           ** apply Rmult_le_pos; try apply pos_INR; try (unfold u0; simpl;nra). 
              unfold u0. apply default_rel_ge_0.
           ** apply Rlt_le, Rinv_0_lt_compat. replace (1* 1)%Re with 1%Re by nra.  by apply ratio_gt_0. 
        -- assert (((INR m * u0 / INR 2) ^ m <= 1)%Re -> 
                    (0 <= 1 - (INR m * u0 / INR 2) ^ m)%Re).
           { nra. }  apply H6.
           assert (1%Re = (1^m)%Re). { by rewrite pow1. } rewrite H7.
           apply pow_incr. split.
           ** apply Rmult_le_pos.
              +++ apply Rmult_le_pos; try apply pos_INR; try (unfold u0;simpl;nra).
                  unfold u0. apply default_rel_ge_0.
              +++ simpl;nra.
           ** assert ((0 < (1 - INR m * u0 / INR 2))%Re -> 
                        (INR m * u0 / INR 2 <= 1)%Re).
              { nra. } apply H8. by apply ratio_gt_0. 
        --  assert (2%Re = ((2 * (1 - INR m * u0 / INR 2)) * / (1 - INR m * u0 / INR 2))%Re ).
            { match goal with |-context[(_ = (?a * ?b) * ?c)%Re]=>
                replace ((a*b)*c)%Re with (a * (b * c))%Re by nra
              end. rewrite Rinv_r.
              nra.
              pose proof (ratio_gt_0 H).
              assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    (1 - INR m * u0 / INR 2)%Re <> 0%Re).
              { nra. } apply H7. unfold u0. apply H6. 
            } rewrite H6.
            apply Rmult_lt_compat_r.
            ** by apply Rinv_0_lt_compat,ratio_gt_0. 
            ** replace (INR 2) with 2%Re by (simpl;nra).
               assert ((2 * (1 - INR m * u0 / 2))%Re = (2 - INR m * u0)%Re).
               { nra. } rewrite H7.
               assert ((INR m * u0 < 1)%Re -> (INR m * u0 < 2 - INR m * u0)%Re).
               { nra. } apply H8. admit.
               (*apply Rlt_le_trans with
               (INR (Z.to_nat (Z.pow_pos 2 23)) * u0).
               +++ apply Rmult_lt_compat_r. unfold u0;simpl;nra.
                   apply lt_INR;lia.
               +++  rewrite INR_IZR_INZ. 
                    assert ((Z.of_nat (Z.to_nat (Z.pow_pos 2 23))) = Z.pow_pos 2 23).
                    { lia. } rewrite H9. unfold u0;simpl;nra. *)
         -- assert ( (0 < (INR m * u0 / INR 2) ^ m)%Re ->
                     (1 - (INR m * u0 / INR 2) ^ m < 1)%Re).
            { nra. } apply H6. apply x_pow_gt_0. 
            apply Rmult_lt_0_compat.
            ** apply Rmult_lt_0_compat.
               +++ apply lt_0_INR. lia.
               +++ unfold u0;simpl. apply default_rel_gt_0.
            ** simpl;nra.
     ++ pose proof (ratio_gt_0 H).
        assert ((0< (1 - INR m * u0 / INR 2))%Re -> 
                    0%Re <> (INR m * u0 / INR 2 - 1)%Re).
        { nra. } apply H5. unfold u0. apply H4.
Admitted.


Lemma n_bound {ty} {n:nat}:
  (n.+1 < 2 ^ Z.to_nat (fprec ty))%nat ->
  (sqrt
   (F' ty / 2 /
    (INR n.+1 * (1 + default_rel ty) ^ n.+1)) <=
 F' ty / 2 /
 (INR n.+1 * (1 + default_rel ty) ^ n.+1))%Re.
Proof.
intros.
apply sqrt_full_le.
assert ((F' ty / 2 /
           (INR n.+1 *
            (1 + default_rel ty) ^ n.+1))%Re = 
         ((F' ty) * / (2 * (INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re).
{ rewrite Rinv_mult_distr. nra. nra.
  apply Rmult_integral_contrapositive. split.
  + apply not_0_INR. lia.
  + apply pow_nonzero. 
    assert ((0 <  default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
    { nra. } apply H0, default_rel_gt_0.
} rewrite H0.
apply pow_invert.
+ apply Rmult_lt_0_compat. nra.
  apply Rmult_lt_0_compat. apply lt_0_INR. lia.
  apply pow_lt. apply Rplus_lt_0_compat. nra. apply default_rel_gt_0.
+ apply Rle_trans with 
  ((2 * INR n.+1) * 3)%Re.
  - assert ((1 * (2 *(INR n.+1 * (1 + default_rel ty) ^ n.+1)))%Re = 
            ((2 * INR n.+1) * (1 + default_rel ty) ^ n.+1)%Re).
    { nra. } rewrite H1.
    apply Rmult_le_compat_l.
    * apply Rmult_le_pos; try nra. apply Rlt_le, lt_0_INR. lia.
    * apply Rlt_le.
      assert ((((1 + default_rel ty) ^ n.+1 - 1) < 2)%Re -> 
              ((1 + default_rel ty) ^ n.+1 < 3)%Re).
      { nra. } apply H2. by apply delta_bound .
  - assert ((2 * INR n.+1 * 3)%Re = (6 * INR n.+1)%Re).
    { nra. } rewrite H1. 
    apply Rle_trans with 
    (6 * INR (2 ^ Z.to_nat (fprec ty)))%Re.
    * apply Rmult_le_compat_l. nra. apply Rlt_le.
      apply lt_INR. by apply /ssrnat.ltP. 
    * unfold F'. unfold fmax, default_rel.
      assert ((1 - 2 * (/ 2 * bpow Zaux.radix2 (- fprec ty + 1)))%Re = 
              (1 - bpow Zaux.radix2 (- fprec ty + 1))%Re).
      { nra. } rewrite H2. 
      rewrite Rmult_minus_distr_l. rewrite Rmult_1_r.
      assert ( ((6 * INR (2 ^ Z.to_nat (fprec ty)) + bpow Zaux.radix2 (femax ty) *
                     bpow Zaux.radix2 (- fprec ty + 1))%Re <= 
                bpow Zaux.radix2 (femax ty))%Re -> 
              (6 * INR (2 ^ Z.to_nat (fprec ty)) <=
               bpow Zaux.radix2 (femax ty) -
               bpow Zaux.radix2 (femax ty) * bpow Zaux.radix2 (- fprec ty + 1))%Re).
      { nra. } apply H3. admit.
Admitted.

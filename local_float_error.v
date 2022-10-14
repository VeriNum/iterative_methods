(** This file contains theorems for the componentwise floating-point error 
of each element of the solution vector **) 

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 

Require Import model_mat_lemmas real_model float_model inf_norm_properties lemmas vcfloat_lemmas.

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.


Import IntervalFlocq3.Tactic.

Open Scope R_scope.

(** LOCAL ROUND-OFF ERROR **)

Lemma prove_roundoff_bound_x1_aux:
  forall s: state,
  prove_roundoff_bound bmap (varmap s) x1' 
    (9.04e-06).
Proof.
intros. 
prove_roundoff_bound.
- prove_rndval; unfold list_nth in *; interval. 
- prove_roundoff_bound2; unfold list_nth in *.
simpl.
match goal with |- context[ Rabs ?a <= _] => 
field_simplify a 
end.
match goal with |- context[ Rabs ?a <= _] => 
interval_intro a upper 
end.
interval.
Qed.

Lemma prove_roundoff_bound_x2_aux:
  forall s: state,
  prove_roundoff_bound bmap (varmap s) x2' 
    (1.5e-05).
Proof.
intros. 
prove_roundoff_bound.
- prove_rndval; unfold list_nth in *; interval. 
- prove_roundoff_bound2; unfold list_nth in *.
simpl.
match goal with |- context[ Rabs ?a <= _] => 
field_simplify a 
end.
match goal with |- context[ Rabs ?a <= _] => 
interval_intro a upper 
end.
interval.
Qed.

Lemma prove_roundoff_bound_x3_aux:
  forall s: state,
  prove_roundoff_bound bmap (varmap s) x3' 
    (9.0004e-06).
Proof.
intros. 
prove_roundoff_bound.
- prove_rndval; unfold list_nth in *; interval. 
- prove_roundoff_bound2; unfold list_nth in *.
simpl.
match goal with |- context[ Rabs ?a <= _] => 
field_simplify a 
end.
match goal with |- context[ Rabs ?a <= _] => 
interval_intro a upper 
end.
interval.
Qed.


From mathcomp Require Import matrix bigop all_algebra all_ssreflect.
From mathcomp.analysis Require Import Rstruct.
From Coquelicot Require Import Lub Rbar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** We will open the real scope and the Ring scope 
  separately **)

Open Scope ring_scope.

(** We instantiate the ring scope with real scope using
  Delimit Scope ... **)
Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

(** We next import the ring theory so that we can use
  it for reals **)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.


(** define a vector of the elementwise floating point errors
derived using VCFloat in the lemmas prove_roundoff_bound_x3_aux,
prove_roundoff_bound_x2_aux, and prove_roundoff_bound_x1_aux *)
Definition round_off_error :=  
  vec_inf_norm (@listR_to_vecR 3%nat [9.04e-06; 1.5e-05; 9.0004e-06]).

Lemma Rabs_list_vecR (i : 'I_3):
  Rabs (listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0) = 
   listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0.
Proof.
rewrite !mxE.
case: (nat_of_ord i).
+ simpl. by rewrite Rabs_right; nra.
+ intros. simpl.
  destruct n.
  - by rewrite Rabs_right; nra.
  - destruct n.
    *  by rewrite Rabs_right; nra.
    * by destruct n; apply Rabs_R0. 
Qed.

Lemma Rabs_list_cons:
  [seq listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0
          | i <- enum 'I_3] = 
          mkseq (fun i => nth 0 [:: 9.04e-6; 1.5e-5; 9.0004e-6] i) 3.
Proof.
unfold mkseq. rewrite -val_enum_ord.
rewrite -[in RHS]map_comp.
apply eq_map. unfold eqfun.
intros. rewrite mxE //=.
case: (nat_of_ord x).
+ rewrite //=.
+ intros. case: n.
  - rewrite //=.
  - intros. case: n.
    * rewrite //=.
    * intros. by case: n.
Qed.

Lemma round_off_error_bound :
round_off_error = 1.5e-5.
Proof.
rewrite /round_off_error /vec_inf_norm.
assert ([seq Rabs
             (listR_to_vecR
                [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0)
             | i <- enum 'I_3] = 
          [seq (listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0) 
            | i <- enum 'I_3]).
{ apply eq_map. unfold eqfun. intros. apply Rabs_list_vecR. }
rewrite H. clear H.
assert ([seq listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6] i 0
          | i <- enum 'I_3] = 
          mkseq (fun i => nth 0 [:: 9.04e-6; 1.5e-5; 9.0004e-6] i) 3).
{ apply Rabs_list_cons. }
rewrite H.
apply bigmaxrP.
split.
- unfold mkseq.
  assert (1.5e-5 = (fun i => nth 0 [:: 9.04e-6; 1.5e-5; 9.0004e-6] i) 1%N).
  { by simpl. } rewrite H0. rewrite inE //=. apply /orP.
  right. rewrite inE //=. apply /orP. by left.
- intros. rewrite size_map in H0.
  rewrite -val_enum_ord size_map size_enum_ord in H0.
  assert (i = 0%N \/ i = 1%N \/ i = 2%N).
  { rewrite leq_eqVlt in H0. 
    assert ((i.+1 == 3%N) \/ (i.+1 < 3)%N).
    { by apply /orP. } destruct H1.
    + by right;right; apply /eqP.
    + rewrite leq_eqVlt in H1.
      assert ((i.+2 == 3%N) \/ (i.+2 < 3)%N).
      { by apply /orP. } destruct H2.
      - by right;left; apply /eqP.
      - left. rewrite !ltnS leqn0 in H2. by apply /eqP.
  }
  destruct H1.
  * rewrite H1. rewrite nth_mkseq //=. by apply /RleP; nra.
  * destruct H1; rewrite H1; rewrite nth_mkseq //=; apply /RleP; nra.
Qed.


Lemma prove_roundoff_bound_x1:
  forall s : state,
  boundsmap_denote bmap (varmap s)-> 
  (Rabs (FT2R (fval (env_ (varmap s)) x1')  
      - rval (env_ (varmap s)) x1') <= 9.04e-06)%Re.
Proof. intros. apply (prove_roundoff_bound_x1_aux s H). Qed.


Lemma prove_roundoff_bound_x2:
  forall s : state,
  boundsmap_denote bmap (varmap s)-> 
  (Rabs (FT2R (fval (env_ (varmap s)) x2')  
      - rval (env_ (varmap s)) x2') <= 1.5e-05)%Re.
Proof. intros. apply (prove_roundoff_bound_x2_aux s H). Qed.

Lemma prove_roundoff_bound_x3:
  forall s : state,
  boundsmap_denote bmap (varmap s)-> 
  (Rabs (FT2R (fval (env_ (varmap s)) x3')  
      - rval (env_ (varmap s)) x3') <= 9.0004e-06)%Re.
Proof. intros. apply (prove_roundoff_bound_x3_aux s H). Qed.



Theorem step_round_off_error':
  forall xb : state,
  boundsmap_denote bmap (varmap xb)-> 
  let env := env_ (varmap xb) in
  let x' := FT2R_list [fval env x1'; fval env x2'; fval env x3'] in 
  let x := [rval env x1'; rval env x2'; rval env x3'] in 
  vec_inf_norm( (@listR_to_vecR 3%nat x) - (@listR_to_vecR 3%nat x')) <= round_off_error.
Proof. 
intros.
cbv zeta.
rewrite round_off_error_bound.
unfold vec_inf_norm. apply /RleP.
apply bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros. rewrite size_map size_enum_ord in H0.
  assert ((@listR_to_vecR 3
            [:: rval (env_ (varmap xb)) x1';
                rval (env_ (varmap xb)) x2';
                rval (env_ (varmap xb)) x3'] -
          @listR_to_vecR 3
            (FT2R_list
               [:: fval (env_ (varmap xb)) x1';
                   fval (env_ (varmap xb)) x2';
                   fval (env_ (varmap xb)) x3'])) = 
          @listR_to_vecR 3 
          [:: (rval (env_ (varmap xb)) x1' - FT2R (fval (env_ (varmap xb)) x1'));
              (rval (env_ (varmap xb)) x2' - FT2R (fval (env_ (varmap xb)) x2'));
              (rval (env_ (varmap xb)) x3' - FT2R (fval (env_ (varmap xb)) x3'))]).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE.
    case: (nat_of_ord x).
    + rewrite /List.nth //=.
    + intros. case: n. 
      - rewrite /List.nth //=.
      - destruct n.
        * rewrite /List.nth //=.
        * rewrite /List.nth //=.
          destruct n ; by rewrite subr0.
  } rewrite H1. clear H1. 
  assert ([seq Rabs
                (listR_to_vecR
                   [:: rval (env_ (varmap xb)) x1' -
                       FT2R
                         (fval (env_ (varmap xb)) x1');
                       rval (env_ (varmap xb)) x2' -
                       FT2R
                         (fval (env_ (varmap xb)) x2');
                       rval (env_ (varmap xb)) x3' -
                       FT2R
                         (fval (env_ (varmap xb)) x3')]
                   i0 0)
            | i0 <- enum 'I_3] = 
          [seq (listR_to_vecR
                   [:: Rabs (rval (env_ (varmap xb)) x1' -
                       FT2R
                         (fval (env_ (varmap xb)) x1'));
                       Rabs (rval (env_ (varmap xb)) x2' -
                       FT2R
                         (fval (env_ (varmap xb)) x2'));
                       Rabs (rval (env_ (varmap xb)) x3' -
                       FT2R
                         (fval (env_ (varmap xb)) x3'))]
                   i0 0)
            | i0 <- enum 'I_3]).
  { apply eq_map. unfold eqfun. intros. rewrite !mxE.
    case: (nat_of_ord x).
    + rewrite /List.nth //=.
    + intros. case: n. 
      - rewrite /List.nth //=.
      - destruct n.
        * rewrite /List.nth //=.
        * rewrite /List.nth //=. destruct n; by apply Rabs_R0.
  } rewrite H1. clear H1.
  assert ([seq listR_to_vecR
                [:: Rabs
                      (rval (env_ (varmap xb)) x1' -
                       FT2R
                         (fval (env_ (varmap xb)) x1'));
                    Rabs
                      (rval (env_ (varmap xb)) x2' -
                       FT2R
                         (fval (env_ (varmap xb)) x2'));
                    Rabs
                      (rval (env_ (varmap xb)) x3' -
                       FT2R
                         (fval (env_ (varmap xb)) x3'))]
                i0 0
            | i0 <- enum 'I_3] = 
           mkseq (fun i => listR_to_vecR
                                [:: Rabs
                                      (rval (env_ (varmap xb)) x1' -
                                       FT2R
                                         (fval (env_ (varmap xb)) x1'));
                                    Rabs
                                      (rval (env_ (varmap xb)) x2' -
                                       FT2R
                                         (fval (env_ (varmap xb)) x2'));
                                    Rabs
                                      (rval (env_ (varmap xb)) x3' -
                                       FT2R
                                         (fval (env_ (varmap xb)) x3'))] (@inord 3 i) 0) 3).
  { unfold mkseq. rewrite -val_enum_ord.
    rewrite -[in RHS]map_comp.
    apply eq_map. unfold eqfun. intros.
    rewrite !mxE.
    assert (((fun i0 : nat =>
                listR_to_vecR
                  [:: Rabs
                        (rval (env_ (varmap xb)) x1' -
                         FT2R (fval (env_ (varmap xb)) x1'));
                      Rabs
                        (rval (env_ (varmap xb)) x2' -
                         FT2R (fval (env_ (varmap xb)) x2'));
                      Rabs
                        (rval (env_ (varmap xb)) x3' -
                         FT2R (fval (env_ (varmap xb)) x3'))]
                  (@inord 3 i0) 0) \o val) x = 
              listR_to_vecR
                  [:: Rabs
                        (rval (env_ (varmap xb)) x1' -
                         FT2R (fval (env_ (varmap xb)) x1'));
                      Rabs
                        (rval (env_ (varmap xb)) x2' -
                         FT2R (fval (env_ (varmap xb)) x2'));
                      Rabs
                        (rval (env_ (varmap xb)) x3' -
                         FT2R (fval (env_ (varmap xb)) x3'))]
                  (@inord 3 x) 0).
    { by simpl. }
    rewrite H1. clear H1. rewrite mxE.
    assert (nat_of_ord (@inord 3 x) = x :> nat).
    { rewrite inordK. 
      + by [].
      + apply ltn_trans with 3%N. 
        - apply ltn_ord.
        - by [].
    } by rewrite H1.
  } rewrite H1. clear H1.
  rewrite nth_mkseq.
  - assert (i = 0%N \/ i = 1%N \/ i = 2%N).
    { rewrite leq_eqVlt in H0. 
      assert ((i.+1 == 3%N) \/ (i.+1 < 3)%N).
      { by apply /orP. } destruct H1.
      + by right;right; apply /eqP.
      + rewrite leq_eqVlt in H1.
        assert ((i.+2 == 3%N) \/ (i.+2 < 3)%N).
        { by apply /orP. } destruct H2.
        - by right;left; apply /eqP.
        - left. rewrite !ltnS leqn0 in H2. by apply /eqP.
    } destruct H1.
    * rewrite H1. rewrite mxE. rewrite inordK.
      ++ rewrite /List.nth.
         assert ((rval (env_ (varmap xb)) x1' -
                    FT2R (fval (env_ (varmap xb)) x1'))%Re = 
                  (- (FT2R (fval (env_ (varmap xb)) x1')  
                          - rval (env_ (varmap xb)) x1'))%Re).
         { nra. } rewrite H2. clear H2. rewrite Rabs_Ropp.
         apply Rle_trans with 9.04e-06.
         -- by apply prove_roundoff_bound_x1.
         -- nra.
      ++ by [].
    * destruct H1.
      ++ rewrite H1. rewrite mxE. rewrite inordK.
         -- rewrite /List.nth.
            assert ((rval (env_ (varmap xb)) x2' -
                    FT2R (fval (env_ (varmap xb)) x2'))%Re = 
                      (- (FT2R (fval (env_ (varmap xb)) x2')  
                              - rval (env_ (varmap xb)) x2'))%Re).
             { nra. } rewrite H2. clear H2. rewrite Rabs_Ropp.
            by apply prove_roundoff_bound_x2.
         -- by [].
      ++ rewrite H1. rewrite mxE. rewrite inordK.
         -- rewrite /List.nth. 
            assert ((rval (env_ (varmap xb)) x3' -
                    FT2R (fval (env_ (varmap xb)) x3'))%Re = 
                  (- (FT2R (fval (env_ (varmap xb)) x3')  
                          - rval (env_ (varmap xb)) x3'))%Re).
             { nra. } rewrite H2. clear H2. rewrite Rabs_Ropp.
             apply Rle_trans with 9.0004e-06.
             ** by apply prove_roundoff_bound_x3.
             ** nra.
         -- by [].
  - by []. 
Qed. 


Theorem step_round_off_error:
  forall s : state,
  boundsmap_denote bmap (varmap s)-> 
  let env := env_ (varmap s) in
  let X_m_R := 
    (X_m_real 1 (@listR_to_vecR 3%nat (FT2R_list s)) (@listR_to_vecR 3%nat b_real) 1%Re) in
  let X_m_F := 
    listR_to_vecR ( FT2R_list (X_m 1 s b_float 1%F32)) in
  vec_inf_norm (X_m_R - X_m_F) <= round_off_error.
Proof.
intros.
pose proof step_round_off_error' H.
cbv zeta in H0.
cbv zeta.
rewrite reflect_reify_sR in H0.
rewrite reflect_reify_sF in H0.
apply H0.
Qed.



Theorem boundsmap_succ_step : 
  forall k x0,
  let xk := X_m k x0 b_float 1%F32 in
  boundsmap_denote bmap (varmap xk) -> 
  let len := 3%nat in
  let x0r := @listR_to_vecR len (FT2R_list x0) in
  let xkr := @listR_to_vecR len (FT2R_list xk) in
  let br := listR_to_vecR b_real in
  (exists c, vec_inf_norm (@X_m_real (k.+1) len x0r br 1) <= c
    /\ exists a, 
    vec_inf_norm (@X_m_real (k.+1) len x0r br 1 - listR_to_vecR (FT2R_list (X_m (k.+1) x0 b_float 1%F32))) <= a
    /\ a + c <= 100 ) ->   
  boundsmap_denote bmap (varmap (X_m (k.+1) x0 b_float 1%F32)).
Proof.
intros ? ? ? BMD ? ? ? ? H.
destruct H as (c & C & a & A & B).
apply boundsmap_denote_i.
2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
set (h := 1%F32).
assert
(@vec_inf_norm len (listR_to_vecR (FT2R_list (X_m (k.+1) x0 b_float h))) <= 100).
assert (Hyp1: forall n a b , @vec_inf_norm n (a - b) = @vec_inf_norm n (b- a)) .
{ intros. rewrite vec_inf_norm_opp. 
  assert (b - a0 = - (a0 - b)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE.
    by rewrite opprB.
  } by rewrite H.
}
rewrite Hyp1 in A.
assert (Hyp: forall n a b c, (0 < n)%N -> @vec_inf_norm n (a - b) <= c -> vec_inf_norm(a) - vec_inf_norm (b) <= c).
{ intros. 
  assert (n= n.-1.+1). { by rewrite prednK. }
  move: a0 b H0 H. rewrite H1. intros.
  by apply reverse_triang_ineq.
}
apply Hyp in A; clear Hyp.
+ 
rewrite ler_subl_addl in A.
apply /RleP. 
apply Rle_trans with 
(vec_inf_norm (X_m_real k.+1 x0r br 1) + a)%Re.
by apply /RleP.
apply Rle_trans with (c+a)%Re.
  - apply Rplus_le_compat.
    * by apply /RleP.
    * nra.
  - rewrite Rplus_comm. by apply /RleP.
+ by unfold len.
+
assert (H1: (0<len)%nat).
by unfold len. 
pose proof (vec_inf_norm_all_le H1 H).
assert (H2: (1<len)%nat).
by unfold len. 
assert (H3: (2<len)%nat).
by unfold len. 
pose proof (H0 0%nat H1).
pose proof (H0 1%nat H2).
pose proof (H0 2%nat H3).
replace (@List.nth R 0 (FT2R_list (X_m (k.+1) x0 b_float h)) 0)
  with (@FT2R Tsingle (list_nth 0 (X_m (k.+1) x0 b_float h))) in H4;
try apply FT2R_list_eq.
replace (@List.nth R 1 (FT2R_list (X_m (k.+1) x0 b_float h)) 0)
  with (@FT2R Tsingle (list_nth 1 (X_m (k.+1) x0 b_float h))) in H5;
try apply FT2R_list_eq.
replace (@List.nth R 2 (FT2R_list (X_m (k.+1) x0 b_float h)) 0)
  with (@FT2R Tsingle (list_nth 2 (X_m (k.+1) x0 b_float h))) in H6;
try apply FT2R_list_eq.
pose proof (Rabs_le_inv (@FT2R Tsingle (list_nth 0 (X_m (k.+1) x0 b_float h))) 100).
pose proof (Rabs_le_inv (@FT2R Tsingle (list_nth 1 (X_m (k.+1) x0 b_float h))) 100).
pose proof (Rabs_le_inv (@FT2R Tsingle (list_nth 2 (X_m (k.+1) x0 b_float h))) 100).
repeat apply list_forall_cons; try apply list_forall_nil;
(eexists; split; [|split;[|split]]; try reflexivity; auto;
  try unfold List.nth; try nra; auto).
-
destruct (prove_roundoff_bound_x2_aux _ BMD) as [? _].
rewrite <- H10; clear H10.
simple apply f_equal.
unfold_all_fval.
reflexivity.
- 
apply H8; apply /RleP; apply H5.
-
destruct (prove_roundoff_bound_x1_aux _ BMD) as [? _]; clear H.
rewrite <- H10; clear H10.
simple apply f_equal.
unfold_all_fval.
reflexivity.
- 
apply H7; apply /RleP; apply H4.
- 
destruct (prove_roundoff_bound_x3_aux _ BMD) as [? _]; clear H.
rewrite <- H10; clear H10.
simple apply f_equal.
unfold_all_fval.
reflexivity.
- 
apply H9; apply /RleP; apply H6.
Qed.



Lemma roundoff_pos :
  (0<= round_off_error)%Re.
Proof.
unfold round_off_error.
rewrite_scope.
apply vec_norm_pd.
Qed.


Lemma concrete_roundoff_k : 
  forall k: nat,
  (k <= 100)%nat -> 
  round_off_error * error_sum k.+2 (@matrix_inf_norm 3 (S_mat _ 1)) <= 0.0016.
Proof.
intros; rewrite_scope; eapply Rle_trans.
apply Rmult_le_compat_l. try apply roundoff_pos.
rewrite_scope.
apply error_sum_le.
apply matrix_norm_pd.
apply S_mat_norm_lt_1; try nra.
rewrite error_sum_1.
unfold round_off_error.
assert (@vec_inf_norm 3 (listR_to_vecR [:: 9.04e-6; 1.5e-5; 9.0004e-6]) =  1.5e-5).
{ assert (round_off_error = 1.5e-5).
  { apply round_off_error_bound. } by unfold round_off_error in H0.
}
rewrite H0.
eapply Rle_trans.
apply Rmult_le_compat_l. try nra. 
assert ((INR k.+2 <= 102)%Re).
{ rewrite -addn2. rewrite plus_INR. 
  assert (INR 2 = 2%Re). { reflexivity. } rewrite H1.
  assert (102%Re  = (100 + 2)%Re). { nra. } rewrite H2. 
  apply Rplus_le_compat_r. 
  rewrite -real_cast.
  assert (100%Re = 100%:R). 
  { rewrite real_cast. simpl. nra. }
  rewrite H3. by apply m_ge_n.
}
apply H1.
interval.
Qed.



Theorem iterative_round_off_error:
  forall (x_l: list (ftype Tsingle)),
  boundsmap_denote bmap (varmap x_l) -> 
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b := listR_to_vecR b_real in
  @vec_inf_norm 3 x0 <= 48 -> @vec_inf_norm 3 b <= 1 -> 
  let h := 1 in
  let h_f := 1%F32 in  
  let len := 3%nat in
  forall k: nat,
  (k <= 100)%nat -> 
  let varmap_k := (varmap (X_m k x_l b_float h_f)) in
  vec_inf_norm (@X_m_real k len x0 b h - listR_to_vecR (FT2R_list (X_m k x_l b_float h_f))) <=
  round_off_error *
  error_sum k.+1 (@matrix_inf_norm len (S_mat _ h)) /\ boundsmap_denote bmap varmap_k.
Proof.
intros ? ? ? ? ? Hx0 ? ? ?  ? Hk. intros.
induction k.
(* base case*)
-
split. 
+
rewrite /error_sum big_ord_recr //= expr0 big_ord0 add0r mulr1.
  rewrite /x0 x_minus_x_is_0.
  assert ( @vec_inf_norm (len.-1.+1) 0 = 0%Re).
  { apply vec_inf_norm_0_is_0. }
  assert (@vec_inf_norm (len.-1.+1) 0 = @vec_inf_norm len 0).
  { assert ((len.-1.+1) = len). 
    { by rewrite prednK. } auto.  
  } rewrite H1. apply /RleP.  apply roundoff_pos.
+
simpl in varmap_k; subst varmap_k; auto.
-
match goal with |-context [?A /\ ?B] => 
assert A;
try split; auto
end.
simpl in IHk; destruct IHk as (IHk & BMDk); try apply ltnW; auto.
Search (?a < ?b -> ?a <= ?b). try interval.
set (xkr := (X_m_real k x0 (listR_to_vecR b_real) h)) in *.
assert (X_m_real k.+1 x0 b h = X_m_real 1 xkr b h) by (apply X_m_real_iter).
set (xkf :=  @listR_to_vecR len (FT2R_list (X_m k x_l b_float h_f))) in *.
set (xkpf := @listR_to_vecR len (FT2R_list (X_m k.+1 x_l b_float h_f))).
assert ((X_m_real k.+1 x0 b h - listR_to_vecR (FT2R_list (X_m k.+1 x_l b_float h_f)))
= 
X_m_real 1 xkr b h - X_m_real 1 xkf b h + X_m_real 1 xkf b h - xkpf
).
rewrite H1.
subst xkpf.
apply vec_sum_simpl.
rewrite H2. 
apply /RleP.
eapply Rle_trans. 

apply /RleP.
apply cs_ineq_vec_inf_norm; auto.


eapply Rle_trans; auto.
apply /RleP.
eapply ler_add.

assert (Hlen: len = len.-1.+1) by (rewrite prednK; auto).
assert (Hlen2 : (0 < len)%nat). by unfold len. 
pose proof ( @matrix_norm_submult len Hlen2 xkr xkf b 1) as submult.
apply submult.  

pose proof step_round_off_error as Hstep.
set (sk:= (X_m k x_l b_float h_f)).
specialize (Hstep sk BMDk).
cbv zeta in Hstep.
unfold xkf.
assert (
H_Flist: listR_to_vecR (FT2R_list (X_m 1 (X_m k x_l b_float h_f) b_float 1%F32)) =
xkpf
).
+
unfold xkpf. 
rewrite /h_f.
by rewrite /X_m.
+
rewrite <- H_Flist .
unfold h in H1.
unfold len.
apply Hstep.
+
(* invoke lemma relating VCFloat bound (LHS) and analytic bound (RHS) *)
eapply Rle_trans. 
eapply Rplus_le_compat.
eapply Rmult_le_compat.
(* matrix norm positive definite *) 
apply /RleP. apply matrix_norm_pd.
(* vector norm positive definite *)
apply /RleP. apply vec_norm_pd.
apply Rle_refl.
unfold xkr.
unfold len in *.
apply /RleP.
apply IHk.
apply Rle_refl.
unfold h; subst len.
rewrite -!RmultE.
assert (Hsums : error_sum k.+2 (matrix_inf_norm (S_mat 3 1)) =
                 error_sum_ind (matrix_inf_norm (S_mat 3 1)) k.+2).
{ by rewrite error_sum_equiv. }
rewrite Hsums.
rewrite <- error_sum_aux2.
rewrite_scope.


rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
rewrite_scope.
eapply Rplus_le_compat.
rewrite <- error_sum_equiv.
rewrite_scope.
rewrite_scope.
rewrite Rmult_comm.
rewrite !Rmult_assoc.
apply Rmult_le_compat_l.
apply roundoff_pos.
rewrite Rmult_comm.
apply Rmult_le_compat_l.
rewrite_scope.
apply matrix_norm_pd.
all : (apply Req_le; auto).
+
simpl in IHk; destruct IHk as (IHk & BMDk); try apply ltnW; auto.
apply boundsmap_succ_step; auto.
unfold h in *; repeat fold x0 f_list b.
set (xkp:=
    (X_m_real k.+1 x0 b 1)).
set (xk :=
    (@X_m_real k len x0 b 1)).
exists 99; split; unfold xkp.
apply sol_up_bound_exists; auto.
exists (round_off_error * error_sum k.+2 (@matrix_inf_norm len (S_mat len 1))).
split.
apply H1. 
rewrite_scope. 
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite_scope.
apply concrete_roundoff_k; try apply ltnW; auto.
nra. 
Qed.


End WITHNANS.


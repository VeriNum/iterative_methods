(*** Error bounds for matrix matrix multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix classical_sets.
From mathcomp.analysis Require Import Rstruct reals.
Require Import dot_prod_defn generalize float_model_generic 
     inf_norm_properties lemmas matrix_vec_mult_bound matrix_matrix_mult_bound
     real_func_model_generic.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


(*** ||A \otimes v - A v|| <= max_i {e_i}
     |A_i \otimes v - A_i v_2| <= e_i
***)
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.



Section WITHNANS.
Context {NANS: Nans}.

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).


Definition FT2R_list (l : list (ftype Tsingle)) : list R :=  map FT2R l. 


(** Define theta_x **)

(*
Definition theta_x  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1):=
 let s:= [seq (INR (nat_of_ord i)) | i <- enum 'I_k] in
 sup [set x | x \in s].
*)

(** Since, we have a finite set, I can just use bigmaxr instead of
    sup
**)
Definition theta_x  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1) :=
 let s := [seq (vec_inf_norm (@FT2R_mat n 0%nat (x_hat (nat_of_ord i))) 
                / vec_inf_norm x)%Re | i <- enum 'I_k.+1] in
 bigmaxr 0%Re s.



(** Revising the bound E_3 **)
Fixpoint vec_to_list_real {n:nat} (m:nat) (v :'cV[R]_n.+1)
   : list R := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_real p v
   end.

Definition Rlist_pair_abs (L : list (R * R)) :=
  map (fun a => (Rabs (fst a), Rabs (snd a))) L.


Lemma sum_Rabs_pair_rel:
  forall (L: list (R * R)),
  0 <= sum_fixR (prod_fixR (Rlist_pair_abs L)).
Proof.
intros.
induction L.
+ simpl. apply /RleP. apply Rle_refl.
+ simpl. apply /RleP. 
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  apply /RleP. apply IHL.
Qed.


Definition e_i_real {n:nat}  (i : 'I_n.+1) (k:nat)
  (A : 'M[ftype Tsingle]_n.+1) (b : 'cV[ftype Tsingle]_n.+1) 
  (x_hat : nat -> 'cV[ftype Tsingle]_n.+1)
  (x : 'cV[R]_n.+1) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in 
  let l1 := vec_to_list_real n.+1 (\row_(j < n.+1) A_real i j)^T in
  let l2 := vec_to_list_real n.+1 x in
  let L := combine l1 l2 in
  let rs := (theta_x k x_hat x) * dot_prodR (Rlist_pair_abs L) in
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in
  (rs * ((1 + d)^n.+1 -1) + nr * e * (1+d)^(n.+1 -1)%coq_nat + 
  e * ((1+d)^(n.+1-1)%coq_nat -1) / d)%Re.


Definition E_3 {n:nat} (k:nat) 
  (A : 'M[ftype Tsingle]_n.+1) (b : 'cV[ftype Tsingle]_n.+1) 
  (x_hat : nat -> 'cV[ftype Tsingle]_n.+1) (x : 'cV[R]_n.+1) :=
  bigmaxr 0%Re [seq (e_i_real i k A b x_hat x) | i <- enum 'I_n.+1].


Definition tau {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in 
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3_def := E_3 k S_hat b x_hat x in 
  ((matrix_inf_norm S * d + E_2 * d + E_2) * ((theta_x k x_hat x) * vec_inf_norm x) + 
  (E_3_def * d + (vec_inf_norm f) * d + E_1* d + E_3_def + E_1 + e))%Re.

(*
Definition tau {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3 := mat_vec_mult_err_bnd S_hat (x_hat k) in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * ((theta_x k x_hat x) * vec_inf_norm x) + 
  (E_3 * d + (vec_inf_norm f) * d + E_1* d + E_3 + E_1 + e))%Re.
*)


Definition tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3_def := E_3 k S_hat b x_hat x in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * vec_inf_norm (FT2R_mat (x_hat k)) + 
  (E_3_def * d + (vec_inf_norm f) * d + E_1* d + E_3_def + E_1 + e))%Re.


(*
Definition tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):=
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let S := - (FT2R_mat inv_A1) * (FT2R_mat A2) in 
  let f := FT2R_mat (inv_A1) *m (FT2R_mat b) in
  let E_1 := mat_vec_mult_err_bnd inv_A1 b in 
  let E_2 := mat_mat_mult_err_bnd inv_A1 A2 in
  let S_hat := (-f (inv_A1 *f A2)) in
  let E_3 := mat_vec_mult_err_bnd S_hat (x_hat k) in
  ((matrix_inf_norm S * d + E_2 * d + E_2) * vec_inf_norm (FT2R_mat (x_hat k)) + 
  (E_3 * d + (vec_inf_norm f) * d + E_1* d + E_3 + E_1 + e))%Re.

*)


Lemma pow_invert_2: forall x y z :R,
  (0 < z)%Re ->  (x / z <= y)%Re -> (x <= y * z)%Re.
Proof.
intros.
replace x with (x * 1)%Re by nra.
assert (1%Re = (/z * z)%Re).
{ symmetry. apply Rinv_l. nra. } rewrite H1.
replace (x * (/z * z))%Re with ((x / z) * z)%Re by nra.
apply Rmult_le_compat_r.
+ nra.
+ nra.
Qed.


Lemma vec_norm_definite {n:nat} (v : 'cV[R]_n.+1):
  v != 0 ->
  (0 < vec_inf_norm v)%Re.
Proof.
intros.
unfold vec_inf_norm.
assert (exists i, v i 0 != 0).
{ by apply /cV0Pn. } destruct H0 as [i H0].
apply Rlt_le_trans with 
[seq Rabs (v i0 0) | i0 <- enum 'I_n.+1]`_i.
+ rewrite seq_equiv. rewrite nth_mkseq; last by []. 
  apply Rabs_pos_lt. apply /eqP. 
  by rewrite inord_val.
+ apply /RleP. apply (@bigmaxr_ler _ 0%Re [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1] i).
  by rewrite size_map size_enum_ord.
Qed.

Lemma mat_err_bnd_pd {n:nat}
  (A1 A2 : 'M[ftype Tsingle]_n.+1) :
  0%Re <= mat_mat_mult_err_bnd A1 A2.
Proof.
unfold mat_mat_mult_err_bnd.
apply bigmax_le_0.
+ apply /RleP; apply Rle_refl.
+ intros. 
  rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  unfold row_e_j.
  apply big_ge_0_ex_abstract.
  intros. apply /RleP. unfold e_i.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.  unfold dot_prodR.
      apply sum_abs_pair_rel. apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. rewrite -!RmultE. simpl; nra.
    * repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed.


Lemma tau_bounds_tau_m {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1) :
  x != 0 ->
  (tau_m  k x x_hat inv_A1 A1 A2 b <= tau k x x_hat inv_A1 A1 A2 b)%Re.
Proof.
intros.
unfold tau_m, tau.
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
+ repeat apply Rplus_le_le_0_compat. 
  - apply Rmult_le_pos.
    * apply /RleP. apply matrix_norm_pd.
    * rewrite -RmultE. simpl;nra.
  - apply Rmult_le_pos.
    * apply /RleP. apply mat_err_bnd_pd.
    * rewrite -RmultE. simpl;nra.
  - apply /RleP. apply mat_err_bnd_pd.
+ unfold theta_x. apply pow_invert_2. 
  - by apply vec_norm_definite.
  - apply Rle_trans with
    ([seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
        vec_inf_norm x)%Re
      | i <- enum 'I_k.+1]`_k).
    * rewrite seq_equiv. rewrite nth_mkseq; last by [].
      rewrite inordK; last by []. nra.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re 
              [seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
                  vec_inf_norm x)%Re| i <- enum 'I_k.+1] k).
      by rewrite size_map size_enum_ord.
Qed.


Lemma theta_x_ge_0  {n:nat} (k:nat)
 (x_hat : nat ->'cV[ftype Tsingle]_n.+1) (x: 'cV[R]_n.+1):
  x != 0 ->
 (0 <= theta_x k x_hat x)%Re.
Proof.
intros.
unfold theta_x.
apply Rle_trans with (vec_inf_norm (FT2R_mat (x_hat k)) / vec_inf_norm x)%Re.
+ apply Rmult_le_pos.
  - apply /RleP. apply vec_norm_pd.
  - apply Rlt_le, Rinv_0_lt_compat. by apply vec_norm_definite.
+ apply Rle_trans with
    ([seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
        vec_inf_norm x)%Re
      | i <- enum 'I_k.+1]`_k).
    * rewrite seq_equiv. rewrite nth_mkseq; last by [].
      rewrite inordK; last by []. nra.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re 
              [seq (vec_inf_norm (FT2R_mat (x_hat (nat_of_ord i))) /
                  vec_inf_norm x)%Re| i <- enum 'I_k.+1] k).
      by rewrite size_map size_enum_ord.
Qed. 

Lemma mat_vec_mult_err_bnd_pd {n:nat} 
 (A: 'M[ftype Tsingle]_n.+1) (v: 'cV[ftype Tsingle]_n.+1):
 (0 <= mat_vec_mult_err_bnd A v)%Re.
Proof.
unfold mat_vec_mult_err_bnd.
apply /RleP.
apply bigmax_le_0.
+ apply /RleP. apply Rle_refl.
+ intros. rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  unfold e_i. apply /RleP.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.  unfold dot_prodR.
      apply sum_abs_pair_rel. apply Rge_le. apply Rge_minus. apply Rle_ge.
      apply pow_R1_Rle. rewrite -!RmultE. simpl; nra.
    * repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed. 

Lemma X_m_real_iter {n:nat} (k: nat) (x0 b: 'cV[R]_n.+1) 
  (A2 inv_A1: 'M[ftype Tsingle]_n.+1) :
   let xkr := X_m_real_generic k x0 b (FT2R_mat inv_A1) (FT2R_mat A2) in
    X_m_real_generic k.+1 x0 b (FT2R_mat inv_A1) (FT2R_mat A2) = 
    X_m_real_generic 1 xkr b (FT2R_mat inv_A1) (FT2R_mat A2).
Proof. simpl; auto. Qed.


Lemma add_vec_distr {n:nat}:
  forall a b c: 'cV[R]_n,
  a - b + b - c = (a-b) + (b-c).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. by rewrite -addrA.
Qed.


Lemma add_vec_distr_1 {n:nat}:
  forall a b c: 'cV[R]_n,
  (a+b) - (b+c) = a - c.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite -!RplusE -!RoppE. nra.
Qed.

Lemma theta_eq {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1):
  theta_x k x_hat x = theta_x k.+1 x_hat x.
Admitted.


Lemma tau_rel {n:nat} (k:nat) (x: 'cV[R]_n.+1) 
  (x_hat : nat ->'cV[ftype Tsingle]_n.+1)
  (inv_A1 A1 A2 : 'M[ftype Tsingle]_n.+1)
  (b : 'cV[ftype Tsingle]_n.+1):
  (tau k x x_hat inv_A1 A1 A2 b <= tau k.+1 x x_hat inv_A1 A1 A2 b)%Re.
Proof.
unfold tau. 
remember (/ 2 *
   bpow Zaux.radix2 (- fprec Tsingle + 1)) as d.
remember (/ 2 *
  bpow Zaux.radix2
    (3 - femax Tsingle - fprec Tsingle)) as e.
apply Rplus_le_compat.
+ apply Rmult_le_compat_l.
  - repeat apply Rplus_le_le_0_compat. 
    * apply Rmult_le_pos.
      ++ apply /RleP. apply matrix_norm_pd.
      ++ rewrite Heqd. rewrite -RmultE. simpl;nra.
    * apply Rmult_le_pos.
      ++ apply /RleP. apply mat_err_bnd_pd.
      ++ rewrite Heqd. rewrite -RmultE. simpl;nra.
    * apply /RleP. apply mat_err_bnd_pd.
  - apply Rmult_le_compat_r.
    ++ apply /RleP. apply vec_norm_pd.
    ++ rewrite theta_eq;nra.
+ repeat apply Rplus_le_compat.
  unfold E_3. 
  apply Rmult_le_compat_r; try nra.
  - rewrite Heqd. rewrite -RmultE. simpl;nra.
  - assert ([seq e_i_real i k (-f (inv_A1 *f A2)) b
                    x_hat x
                | i <- enum 'I_n.+1] = 
            [seq e_i_real i k.+1
                    (-f (inv_A1 *f A2)) b x_hat x
                | i <- enum 'I_n.+1]).
    { rewrite !seq_equiv. 
      assert ((fun i : nat =>
                  e_i_real (inord i) k (-f (inv_A1 *f A2)) b x_hat x) = 
               (fun i : nat =>
                  e_i_real (inord i) k.+1 (-f (inv_A1 *f A2)) b x_hat x)).
      { apply Logic.FunctionalExtensionality.functional_extensionality.
        move=>i. unfold e_i_real.
        repeat apply Rplus_eq_compat_r. 
        repeat apply Rmult_eq_compat_r.
        apply theta_eq.
      } by rewrite H.
    } rewrite H. nra.
  - nra.
  - nra.
  - unfold E_3. 
    assert ([seq e_i_real i k (-f (inv_A1 *f A2)) b
                      x_hat x
                  | i <- enum 'I_n.+1] = 
              [seq e_i_real i k.+1
                      (-f (inv_A1 *f A2)) b x_hat x
                  | i <- enum 'I_n.+1]).
      { rewrite !seq_equiv. 
        assert ((fun i : nat =>
                    e_i_real (inord i) k (-f (inv_A1 *f A2)) b x_hat x) = 
                 (fun i : nat =>
                    e_i_real (inord i) k.+1 (-f (inv_A1 *f A2)) b x_hat x)).
        { apply Logic.FunctionalExtensionality.functional_extensionality.
          move=>i. unfold e_i_real.
          repeat apply Rplus_eq_compat_r. 
          repeat apply Rmult_eq_compat_r.
          apply theta_eq.
        } by rewrite H.
      } rewrite H. nra.
  - nra.
  - nra.
Qed.

Lemma E_3_err_bnd_pd {n:nat} (k:nat) 
  (A : 'M[ftype Tsingle]_n.+1) (b : 'cV[ftype Tsingle]_n.+1) 
  (x_hat : nat -> 'cV[ftype Tsingle]_n.+1) (x : 'cV[R]_n.+1):
   x != 0 ->
  (0 <= E_3 k A b x_hat x)%Re.
Proof.
intros.
unfold E_3. apply /RleP.
apply bigmax_le_0.
+ apply /RleP. apply Rle_refl.
+ intros. rewrite seq_equiv. rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H0.
  unfold e_i_real. apply /RleP.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.  unfold dot_prodR.
      apply Rmult_le_pos.
      ++ by apply theta_x_ge_0.
      ++ apply /RleP. apply sum_Rabs_pair_rel.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. rewrite -!RmultE. simpl; nra.
    * repeat apply Rmult_le_pos.
      ++ apply pos_INR.
      ++ nra.
      ++ simpl; nra.
      ++ apply pow_le . rewrite -!RmultE. simpl;nra.
  - rewrite -!RmultE. apply Rmult_le_pos.
    * apply Rmult_le_pos.
      ++ simpl;nra.
      ++ apply Rge_le. apply Rge_minus. apply Rle_ge.
         apply pow_R1_Rle. simpl; nra.
    * simpl;nra.
Qed.


(** not entirely in correct form. need to connect A, A1^{-1}. A2 **)
Theorem iterative_round_off_error {n:nat} :
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in 
  (forall i k:nat, (i < n.+1)%nat /\ (k < n.+1)%nat -> 
    (forall (a b : ftype Tsingle) (A1 A2: 'M[ftype Tsingle]_n.+1),
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
           (vec_to_list_float n.+1 (\col_j (A2 j (inord k))))) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt (F' / (nr * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt (F' / (nr * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re))->

  forall (A A1 A2 inv_A1: 'M[ftype Tsingle]_n.+1),
  (** ||A_1^{-1}A_2|| < 1 **)
  matrix_inf_norm (S_mat (FT2R_mat inv_A1) (FT2R_mat A2)) < 1 ->
  (** Relation between A, A_1, A_2 **)
  matrix_inf_norm (FT2R_mat (A +f (-f (A1 +f A2)))) <=
  matrix_inf_norm (FT2R_mat A) * d + e ->
  (** Relation between A_1, inv_A1 **)
  matrix_inf_norm (FT2R_mat (A1 *f inv_A1 ) - (FT2R_mat A1) *m (FT2R_mat inv_A1)) <=
  mat_mat_mult_err_bnd A1 inv_A1 ->
  forall (x_l b: list (ftype Tsingle)),
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b_real := listR_to_vecR (FT2R_list b) in
  let x0_f := list_to_vec_float x_l in
  let b_f := list_to_vec_float b in
  let x := invmx (FT2R_mat A) *m b_real in
  x != 0 ->
  forall k:nat, 
  let f:= tau k x (fun m:nat => @X_m_generic _ _ m n x0_f b_f inv_A1 A2) inv_A1 A1 A2 b_f in
  vec_inf_norm (FT2R_mat (@X_m_generic _ _ k n x0_f b_f inv_A1 A2) - 
                @X_m_real_generic n k x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2)) <=
  f *  error_sum k.+1 (@matrix_inf_norm n.+1 (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))).
Proof.
intros.
induction k.
+ assert (FT2R_mat (X_m_generic 0 x0_f b_f inv_A1 A2) -
           X_m_real_generic 0 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 0).
  { unfold X_m_real_generic, X_m_generic. apply matrixP. unfold eqrel.
    intros. rewrite !mxE. 
    destruct (nat_of_ord x1);
    ( unfold FT2R_list; simpl;
    rewrite -map_nth; simpl; apply /eqP; by rewrite subr_eq0).
  } rewrite H5. simpl. 
  rewrite /tau /error_sum //=. simpl in d, e. fold d e.
  rewrite big_ord_recr //= big_ord0 add0r expr0 mulr1.
  rewrite vec_inf_norm_0_is_0. apply /RleP.
  repeat apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos.
    * repeat apply Rplus_le_le_0_compat.
      ++ apply Rmult_le_pos.
         -- apply /RleP. apply matrix_norm_pd.
         -- unfold d;simpl. rewrite -RmultE. nra.
      ++ apply Rmult_le_pos.
         -- apply /RleP. apply mat_err_bnd_pd.
         -- unfold d;simpl. rewrite -RmultE. nra.
      ++ apply /RleP. apply mat_err_bnd_pd.
    * apply Rmult_le_pos. 
      ++ by apply theta_x_ge_0.
      ++ apply /RleP. apply vec_norm_pd.
  - apply Rmult_le_pos.
    ++ unfold E_3. simpl. by apply E_3_err_bnd_pd .
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - apply Rmult_le_pos.
    ++ apply /RleP. apply vec_norm_pd.
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - apply Rmult_le_pos.
    ++ apply mat_vec_mult_err_bnd_pd .
    ++ unfold d;simpl. rewrite -RmultE. nra.
  - by apply E_3_err_bnd_pd .
  - apply mat_vec_mult_err_bnd_pd .
  - unfold e;simpl. rewrite -RmultE. nra.
+ (** Induction step **)
  set (xkr := (X_m_real_generic k x0 b_real (FT2R_mat inv_A1)(FT2R_mat A2))) in *.
  assert (X_m_real_generic k.+1 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 
          X_m_real_generic 1 xkr b_real (FT2R_mat inv_A1) (FT2R_mat A2)) by 
  apply X_m_real_iter.
  set (xkf := FT2R_mat (X_m_generic k x0_f b_f inv_A1 A2)) in *.
  set (xkpf := FT2R_mat (X_m_generic k.+1 x0_f b_f inv_A1 A2)).
  assert (xkpf - X_m_real_generic k.+1 x0 b_real (FT2R_mat inv_A1) (FT2R_mat A2) = 
          xkpf - X_m_real_generic 1 xkf b_real (FT2R_mat inv_A1) (FT2R_mat A2) + 
          X_m_real_generic 1 xkf b_real (FT2R_mat inv_A1) (FT2R_mat A2) - 
          X_m_real_generic 1 xkr b_real (FT2R_mat inv_A1) (FT2R_mat A2)).
  { rewrite H5. apply vec_sum_simpl. } rewrite H6.
  apply /RleP. eapply Rle_trans.
  - apply /RleP. by apply cs_ineq_vec_inf_norm. 
  - rewrite -RmultE. 
    assert (error_sum k.+2
         (matrix_inf_norm
            (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))) = 
      (1 + (matrix_inf_norm
            (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))) * 
          error_sum k.+1
             (matrix_inf_norm
                (S_mat (FT2R_mat inv_A1) (FT2R_mat A2))))%Re).
    { rewrite !error_sum_equiv. rewrite -error_sum_aux2.
      by rewrite addrC.
    } rewrite H7.
    rewrite Rmult_plus_distr_l. 
    apply Rplus_le_compat.
    * admit.
    * simpl. 
      assert (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkf +
                FT2R_mat inv_A1 *m b_real -
                (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr +
                 FT2R_mat inv_A1 *m b_real) = 
               (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkf) -
               (S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr)).
      { assert ((S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr +
                 FT2R_mat inv_A1 *m b_real) = 
                FT2R_mat inv_A1 *m b_real + 
                S_mat (FT2R_mat inv_A1) (FT2R_mat A2) *m xkr).
        { by rewrite addrC. } rewrite H8. clear H8.
        by rewrite add_vec_distr_1.
      } rewrite H8. clear H8.
      rewrite -mulmxBr.
      eapply Rle_trans.
      ++ apply /RleP. apply submult_prop.
      ++ rewrite -RmultE.
         match goal with |-context[( _ <= ?a * (?b * ?c))%Re]=>
          replace (a * (b * c))%Re with (b * (a * c))%Re by nra
         end. apply Rmult_le_compat_l.
         -- apply /RleP. apply matrix_norm_pd.
         -- eapply Rle_trans.
            ** apply /RleP. apply IHk.
            ** rewrite -RmultE. apply Rmult_le_compat_r.
               +++ apply /RleP. apply error_sum_ge_0.
                   apply matrix_norm_pd.
               +++ apply tau_rel.       
Admitted.




End WITHNANS.
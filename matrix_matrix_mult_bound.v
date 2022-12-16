(*** Error bounds for matrix matrix multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
From Iterative Require Import dot_prod_defn generalize float_model_generic 
               inf_norm_properties lemmas matrix_vec_mult_bound.

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

(** Define the maximum error for matrix-matrix multiplication **)
Definition row_e_j {n:nat} (i: 'I_n.+1) (A1 A2: 'M[ftype Tsingle]_n.+1) :=
  \sum_(k < n.+1) (e_i i A1 (\col_j (A2 j k))).

Definition mat_mat_mult_err_bnd {n:nat} (A1 A2: 'M[ftype Tsingle]_n.+1):=
 bigmaxr 0%Re [seq (row_e_j i A1 A2) | i <- enum 'I_n.+1].

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).



(***  
      Bound for matrix matrix multiplication from the bound for
      dot product of vectors
***)

Lemma mat_mat_err_bnd_holds {n:nat}:
  forall (A1 A2: 'M[ftype Tsingle]_n.+1),
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in 
  (forall i k:nat, (i < n.+1)%nat /\ (k < n.+1)%nat -> 
    (forall a b : ftype Tsingle,
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
           (vec_to_list_float n.+1 (\col_j (A2 j (inord k))))) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt (F' / (nr * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt (F' / (nr * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re))->
  matrix_inf_norm (FT2R_mat (A1 *f A2 ) - (FT2R_mat A1) *m (FT2R_mat A2)) <=
  mat_mat_mult_err_bnd A1 A2.
Proof.
intros. unfold matrix_inf_norm, mat_mat_mult_err_bnd.
apply /RleP. apply bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.
apply Rle_trans with
([seq row_e_j i0 A1 A2 | i0 <- enum 'I_n.+1]`_i).
+ rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.
  unfold row_e_j. unfold row_sum. apply /RleP.
  apply big_sum_ge_ex_abstract. move => k _.
  unfold e_i. fold d e.
  remember (combine
              (vec_to_list_float n.+1 (\row_j A1 (inord i) j)^T)
              (vec_to_list_float n.+1 (\col_j A2 j k))) as L.
  unfold FT2R_mat. rewrite !mxE.
  assert (\sum_j
           (\matrix_(i0, j0) FT2R (A1 i0 j0))  (inord i) j *
           (\matrix_(i0, j0) FT2R (A2 i0 j0)) j k = 
          dot_prodR (Flist_to_Rlist_pair L)).
  { assert (\sum_j
               (\matrix_(i0, j0) FT2R (A1 i0 j0))  (inord i) j *
               (\matrix_(i0, j0) FT2R (A2 i0 j0)) j k  = 
            \sum_j (FT2R (A1 (@inord n i) j) * FT2R (A2 j k))).
    { apply eq_big. by []. intros. by rewrite !mxE. } rewrite H2.
    pose proof (@sum_dot n n.+1 Tsingle (leqnn n.+1)) .
    specialize (H3 (\row_j A1 (inord i) j)^T (\col_j A2 j k)).
    rewrite HeqL. rewrite -H3.
    apply eq_big. by []. intros. rewrite !mxE.
    assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
    { unfold widen_ord. apply val_inj. by simpl. } by rewrite H5. 
  } rewrite H2. 
  pose proof (forward_error_dot_aux L).
  specialize (H0 i k).
  assert ((i < n.+1)%nat /\ (k < n.+1)%nat).
  { split. 
    + by rewrite size_map size_enum_ord in H1.
    + by apply ltn_ord.
  } specialize (H0 H4).
  assert (length L = n.+1).
  { rewrite HeqL. rewrite combine_length. rewrite !length_veclist. lia. }
  rewrite H5 in H3.
  assert ((1 < n.+1)%coq_nat). { destruct H. apply H. }
  assert ((n.+1 < (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat).
  { destruct H. apply H7. } specialize (H3 H6 H7).
  assert (forall a b : ftype Tsingle,
              In (a, b) L ->
              is_finite (fprec Tsingle) (femax Tsingle) a = true /\
              is_finite (fprec Tsingle) (femax Tsingle) b = true /\
              (Rabs (FT2R a) <=
                sqrt (F' / (INR n.+1 *
                   (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))^ (n.+1 + 1)%coq_nat) -
                  / 2 * bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)))%Re /\
              (Rabs (FT2R b) <=
               sqrt (F' /  (INR n.+1 *
                    (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1))^ (n.+1 + 1)%coq_nat) -
                     / 2 * bpow Zaux.radix2(3 - femax Tsingle - fprec Tsingle)))%Re).
    { intros. apply H0. rewrite HeqL in H8; auto. 
      assert (inord k = k). { by rewrite inord_val. } by rewrite H9.
    } specialize (H3 H8). clear H6 H7 H8.
    destruct H3 as [ifH3 H3].
    rewrite -RminusE. unfold d, e. rewrite HeqL in H3. 
    rewrite HeqL. apply H3.
+ apply /RleP.
  apply (@bigmaxr_ler _  _ [seq row_e_j i0 A1 A2 | i0 <- enum 'I_n.+1] i).
  rewrite size_map size_enum_ord.
  by rewrite size_map size_enum_ord in H1.
Qed.


End WITHNANS.
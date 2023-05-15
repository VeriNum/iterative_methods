From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.
Require Import floatlib jacob_list_fun_model.
Require Import fma_floating_point_model.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section WITHNANS.
Context {NANS: Nans}. 

Import jacob_list_fun_model.Experiment.


Lemma A1_invert_equiv {ty} (A : matrix ty) i: 
  (i < length A)%coq_nat ->
  nth i 
     (invert_diagmatrix (diag_of_matrix A))
     (Zconst ty 1) =
  BDIV (Zconst ty 1)
     (nth i (nth i A []) (Zconst ty 0)).
Proof.
intros.
assert (nth i (invert_diagmatrix (diag_of_matrix A))
            (Zconst ty 1) = 
        BDIV (Zconst ty 1) (nth i (diag_of_matrix A) (Zconst ty 1))).
{ rewrite (nth_map_inrange (Zconst ty 1)); try by [].
  by rewrite /diag_of_matrix map_length seq_length /matrix_rows_nat .
} rewrite H0.
unfold diag_of_matrix.  rewrite nth_map_seq.
by unfold matrix_index.
by unfold matrix_rows_nat.
Qed.


Lemma v_equiv {ty} (v: vector ty) size:
  length v = size.+1 -> 
  v = rev (vec_to_list_float size.+1
          (\col_j0 vector_inj v size.+1 j0 ord0)).
Proof.
intros. 
apply nth_ext with (Zconst ty 0) (Zconst ty 0).
+ rewrite rev_length length_veclist. by []. 
+ intros. rewrite rev_nth length_veclist.
  assert ((size.+1 - n.+1)%coq_nat = (size.+1.-1 - n)%coq_nat).
  { by []. } rewrite H1.
  rewrite nth_vec_to_list_float.
  - rewrite !mxE /=. rewrite inordK. 
    * by [].
    * rewrite -H. by apply /ssrnat.ltP.
  - rewrite -H. by apply /ssrnat.ltP.
  - by rewrite -H. 
Qed.


Lemma A2_equiv {ty} (A: matrix ty) size i :
  length A = size.+1 ->
  (i < size.+1)%coq_nat ->
  let A_v := matrix_inj A size.+1 size.+1 in
  nth i
     (matrix_by_index (matrix_rows_nat A)
        (matrix_rows_nat A)
        (fun i0 j : nat =>
         if is_left (Nat.eq_dec i0 j)
         then Zconst ty 0
         else matrix_index A i0 j)) [] =
  rev (vec_to_list_float size.+1
     (\row_j0 A2_J A_v (inord i) j0)^T).
Proof.
intros.
apply nth_ext with (Zconst ty 0) (Zconst ty 0).
+ rewrite rev_length length_veclist. 
  unfold matrix_by_index. rewrite nth_map_seq.
  - rewrite map_length. rewrite seq_length. by unfold matrix_rows_nat.
  - unfold matrix_rows_nat. by rewrite H. 
+ intros.
  rewrite rev_nth length_veclist.
  assert ((size.+1 - n.+1)%coq_nat = (size.+1.-1 - n)%coq_nat).
  { by []. } rewrite H2.
  rewrite nth_vec_to_list_float.
  - rewrite !mxE. unfold matrix_by_index.
    rewrite nth_map_seq.
    * rewrite nth_map_seq.
      ++ rewrite !inordK.
         -- unfold is_left.
            case: (Nat.eq_dec i n). 
            ** intros. rewrite a //=. 
               assert (n == n :>nat = true). 
               { by apply /eqP. }
               by rewrite H3.
            ** intros.
               assert ( i == n :> nat = false). { by apply /eqP. }
               rewrite H3. by unfold matrix_index. 
         -- rewrite /matrix_by_index nth_map_seq in H1.
            ** rewrite map_length seq_length /matrix_rows_nat H in H1.
               by apply /ssrnat.ltP.
            ** unfold matrix_rows_nat. by rewrite H. 
         -- by apply /ssrnat.ltP.
      ++ rewrite /matrix_by_index nth_map_seq in H1.
         -- rewrite map_length seq_length /matrix_rows_nat H in H1.
            by rewrite /matrix_rows_nat H.
         -- unfold matrix_rows_nat. by rewrite H.
    * unfold matrix_rows_nat. by rewrite H.
  - rewrite /matrix_by_index nth_map_seq in H1.
    -- rewrite map_length seq_length /matrix_rows_nat H in H1.
       by apply /ssrnat.ltP.
    -- unfold matrix_rows_nat. by rewrite H.
  - rewrite /matrix_by_index nth_map_seq in H1.
    -- by rewrite map_length seq_length /matrix_rows_nat H in H1.
    -- unfold matrix_rows_nat. by rewrite H.
Qed.

Lemma residual_equiv {ty} (v: vector ty) (A: matrix ty) i:
  (0 < length A)%nat ->
  let size := (length A).-1 in   
  let A_v := matrix_inj A size.+1 size.+1 in
  length A = length v ->
  (i < length A)%nat ->
  nth i (matrix_vector_mult (remove_diag A) v) (Zconst ty 0) = 
  dotprod_r (vec_to_list_float size.+1
              (\row_j0 A2_J A_v (inord i) j0)^T)
           (vec_to_list_float size.+1
              (\col_j0 vector_inj v size.+1 j0 ord0)).
Proof.
intros.
assert (nth i (matrix_vector_mult (remove_diag A) v)
          (Zconst ty 0) = 
        dotprod 
        (nth i (matrix_by_index (matrix_rows_nat A)
                  (matrix_rows_nat A)
                  (fun i0 j : nat =>
                   if Nat.eq_dec i0 j
                   then Zconst ty 0
                   else matrix_index A i0 j)) [])
        v).
{ unfold matrix_by_index. rewrite nth_map_seq.
  unfold matrix_vector_mult.
  rewrite (@map_nth _ _ _ _ [] _ ).
  unfold remove_diag.
  unfold matrix_by_index. rewrite nth_map_seq.
  + rewrite (@map_ext _ _ _ (fun j : nat =>
      if is_left (Nat.eq_dec i j)
      then Zconst ty 0
      else matrix_index A i j)); try by [].
    intros. unfold is_left.
    by case: (Nat.eq_dec i a).
  + unfold matrix_rows_nat. by apply /ssrnat.ltP.
  + unfold matrix_rows_nat. by apply /ssrnat.ltP.
} rewrite H2. clear H2. 
assert (v = rev (vec_to_list_float size.+1
          (\col_j0 vector_inj v size.+1 j0 ord0))).
{ apply v_equiv. rewrite -H0. rewrite /size.
  by rewrite prednK.
}
rewrite [in LHS]H2.
rewrite (@A2_equiv _ _ size _).
rewrite dotprod_rev_equiv; try by [].
by rewrite !length_veclist.
by rewrite /size prednK /=.
rewrite /size prednK /=.
by apply /ssrnat.ltP.
apply H.
Qed.


Lemma iter_length {ty} n (A: matrix ty) (b: vector ty) (x: vector ty):
  length b = length A ->
  length x = length A ->
  length
  (Nat.iter n
     (fun x0 : vector ty =>
      diagmatrix_vector_mult
        (invert_diagmatrix (diag_of_matrix A))
        (vector_sub b
           (matrix_vector_mult (remove_diag A) x0)))
     x) = length A.
Proof.
induction n.
+ by simpl.
+ simpl. repeat rewrite !map_length combine_length.
  unfold matrix_vector_mult. rewrite map_length.
  rewrite !map_length !seq_length /matrix_rows_nat /=.
  intros. rewrite H. by rewrite !Nat.min_id.
Qed.
  

Lemma func_model_equiv {ty} (A: matrix ty) (b: vector ty) (x: vector ty) (n: nat) :
  let size := (length A).-1 in  
  let x_v := vector_inj x size.+1 in 
  let b_v := vector_inj b size.+1 in 
  let A_v := matrix_inj A size.+1 size.+1 in
  (0 < length A)%nat ->
  length b = length A -> 
  length x = length A ->
  vector_inj (jacobi_n A b x n) size.+1 = @X_m_jacobi _ ty size n x_v b_v A_v.
Proof.
intros.
induction n.
+ apply /matrixP. unfold eqrel.
  intros. by rewrite !mxE /=.  
+ simpl. rewrite -IHn.
  apply /matrixP. unfold eqrel.
  move=> i j.
  rewrite !mxE. 
  remember (jacobi_n A b x n) as x_n.
  unfold jacob_list_fun_model.jacobi_iter.
  unfold diagmatrix_vector_mult, map2, uncurry.
  rewrite (nth_map_inrange (Zconst ty 1, Zconst ty 0)).
  - rewrite combine_nth.
    rewrite A1_invert_equiv.
    * rewrite nth_vec_to_list_float; last by apply ltn_ord.
      rewrite !mxE. rewrite inordK; last by apply ltn_ord.
      assert (nth i
                   (vector_sub b
                      (matrix_vector_mult (remove_diag A) x_n))
                   (Zconst ty 0) = 
               BMINUS (nth i b (Zconst ty 0))
                    (nth i  (matrix_vector_mult (remove_diag A)
                            x_n) (Zconst ty 0))).
           { unfold vector_sub, map2, uncurry. 
             rewrite (nth_map_inrange (Zconst ty 0, Zconst ty 0)).
             + rewrite combine_nth. 
               - reflexivity.
               - unfold matrix_vector_mult. rewrite map_length. 
                 unfold remove_diag. rewrite map_length seq_length.
                 by unfold matrix_rows_nat.
             + rewrite combine_length. rewrite !map_length seq_length /matrix_rows_nat H0 Nat.min_id /=.
                assert (length A = size.+1).
                { rewrite /size. by rewrite prednK. } rewrite H2. 
                apply /ssrnat.ltP. apply ltn_ord. 
           } rewrite H2. rewrite nth_vec_to_list_float; last by apply ltn_ord.
           rewrite !mxE. rewrite residual_equiv. rewrite inordK.
           rewrite -/size . by rewrite /A_v. 
           apply ltn_ord. by [].
           rewrite Heqx_n. unfold jacobi_n.
           unfold jacob_list_fun_model.jacobi_iter.
           by rewrite iter_length.
           assert (length A = size.+1).
           { rewrite /size. by rewrite prednK. } rewrite H3. apply ltn_ord.
     * assert (length A = size.+1).
       { rewrite /size. by rewrite prednK. } rewrite H2. 
       apply /ssrnat.ltP. apply ltn_ord.
     * rewrite  !map_length !seq_length combine_length !map_length !seq_length.
       by rewrite /matrix_rows_nat H0 Nat.min_id.
  - rewrite  combine_length !map_length !seq_length combine_length !map_length !seq_length.
     rewrite /matrix_rows_nat H0 !Nat.min_id.
     assert (length A = size.+1).
     { rewrite /size. by rewrite prednK. } rewrite H2. 
     apply /ssrnat.ltP. apply ltn_ord. 
Qed.


End WITHNANS.

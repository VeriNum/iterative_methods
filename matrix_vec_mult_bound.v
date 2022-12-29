(*** Error bounds for matrix vector multiplication
     from the error bounds for dot product
***)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Require Import dot_prod_defn generalize float_model_generic 
               inf_norm_properties lemmas.

Import Coq.Lists.List Coq.Lists.List.ListNotations.


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

Definition e_i {n:nat} (i : 'I_n.+1) 
  (A: 'M[ftype Tsingle]_n.+1) (v: 'cV[ftype Tsingle]_n.+1) := 
  let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
  let l2 := vec_to_list_float n.+1 v in
  let L := combine l1 l2 in
  let rs := dot_prodR (Flist_to_Rlist_pair_abs L) in
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in
  (rs * ((1 + d)^n.+1 -1) + nr * e * (1+d)^(n.+1 -1)%coq_nat + 
  e * ((1+d)^(n.+1-1)%coq_nat -1) / d)%Re.


Definition mat_vec_mult_err_bnd {n:nat} 
 (A: 'M[ftype Tsingle]_n.+1) (v: 'cV[ftype Tsingle]_n.+1):=
 bigmaxr 0%Re [seq (e_i i A v) | i <- enum 'I_n.+1].

Definition FT2R_mat {m n: nat} (A : 'M[ftype Tsingle]_(m.+1, n.+1)) :
   'M[R]_(m.+1, n.+1):=
  \matrix_(i, j) FT2R (A i j).


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).


(** an equivalence between real dot product defined using the mathcomp
    sum and our dot product definition using the lists
**)

Lemma sum_dot {n:nat} (m:nat) {ty} (le_n_m : (m <= n.+1)%nat) :
  forall (v1 v2: 'cV[ftype ty]_n.+1),
  let l1 := @vec_to_list_float _ n m v1 in 
  let l2 := @vec_to_list_float _ n m v2 in 
  let L := combine l1 l2 in
  \sum_(j < m) (FT2R (v1 (@widen_ord m n.+1 le_n_m j) 0) * 
                FT2R (v2 (@widen_ord m n.+1 le_n_m j) 0)) = 
  dot_prodR (Flist_to_Rlist_pair L).
Proof.
intros.
induction m.
+  rewrite big_ord0 //=. 
+ simpl. rewrite big_ord_recr //=.
  assert (dot_prodR
            ((FT2R (v1 (inord m) ord0),
              FT2R (v2 (inord m) ord0))
             :: Flist_to_Rlist_pair
                  (combine (vec_to_list_float m v1)
                     (vec_to_list_float m v2))) = 
          (FT2R (v1 (inord m) ord0) * 
              FT2R (v2 (inord m) ord0)) +
          dot_prodR (Flist_to_Rlist_pair
                      (combine (vec_to_list_float m v1)
                       (vec_to_list_float m v2)))).
  { by unfold dot_prodR. } rewrite H. clear H.
  assert (\sum_(i < m)
             FT2R (v1
                  (widen_ord (m:=n.+1) le_n_m
                     (widen_ord (m:=m.+1) (leqnSn m) i)) 0) *
               FT2R
                 (v2
                    (widen_ord (m:=n.+1) le_n_m
                       (widen_ord (m:=m.+1) (leqnSn m) i)) 0) = 
           dot_prodR
            (Flist_to_Rlist_pair
               (combine (vec_to_list_float m v1)
                  (vec_to_list_float m v2)))).
  { unfold L in IHm.  
    assert ((m <= n.+1)%nat). { by apply ltnW. }
    specialize (IHm H). rewrite -IHm.
    apply eq_big. by [].
    intros. 
    assert ((widen_ord (m:=n.+1) le_n_m
                  (widen_ord (m:=m.+1) (leqnSn m) i))= 
             (widen_ord (m:=n.+1) H i)).
    { unfold widen_ord. 
      apply val_inj. by simpl.
    } by rewrite H1.
  } rewrite H. rewrite addrC. 
  assert ((widen_ord (m:=n.+1) le_n_m ord_max) = (inord m)).
  { unfold widen_ord. 
    apply val_inj. simpl. by rewrite inordK.
  } by rewrite H0.
Qed.


Lemma length_veclist {ty} {n m:nat} (v: 'cV[ftype ty]_n.+1):
  length (@vec_to_list_float _ n m v) = m.
Proof.
induction m.
+ simpl. auto.
+ simpl. by rewrite IHm.
Qed.


(***  Bound for matrix vector multiplication from the bound for
      dot product of vectors
***)


Lemma mat_vec_err_bnd_holds {n:nat}:
  forall (A: 'M[ftype Tsingle]_n.+1) (v: 'cV[ftype Tsingle]_n.+1),
  (1 < n.+1 /\ n.+1< (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat ->
  let e := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let nr := INR n.+1 in 
  (forall i:nat, (i < n.+1)%nat -> 
    (forall a b : ftype Tsingle,
      In (a, b)
        (combine (vec_to_list_float n.+1 (\row_j A (inord i) j)^T)
           (vec_to_list_float n.+1 v)) ->
      is_finite (fprec Tsingle) (femax Tsingle) a = true /\
      is_finite (fprec Tsingle) (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt (F' / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re /\
      (Rabs (FT2R b) <=
       sqrt (F' / ((nr+1) * (1 + d) ^ (n.+1 + 1)%coq_nat) - e))%Re))->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  mat_vec_mult_err_bnd A v.
Proof.
intros. unfold vec_inf_norm, mat_vec_mult_err_bnd.
apply /RleP. apply bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.
pose proof (forward_error_dot_aux ((combine
          (vec_to_list_float n.+1
             (\row_j A (inord i) j)^T)
          (vec_to_list_float n.+1 v)))).
assert (length (combine
            (vec_to_list_float n.+1 (\row_j A (inord i) j)^T)
            (vec_to_list_float n.+1 v)) = n.+1).
{ rewrite combine_length. rewrite !length_veclist. lia. }
rewrite H3 in H2.
assert ((1 < n.+1)%coq_nat). { destruct H. apply H. }
assert ((n.+1 < (Z.to_nat (Z.pow_pos 2 23) - 1)%coq_nat)%coq_nat).
{ destruct H. apply H5. } specialize (H2 H4 H5). 
assert (forall a b : ftype Tsingle,
      In (a, b)
        (combine
           (vec_to_list_float n.+1
              (\row_j A (inord i) j)^T)
           (vec_to_list_float n.+1 v)) ->
      is_finite (fprec Tsingle)  (femax Tsingle) a = true /\
      is_finite (fprec Tsingle)  (femax Tsingle) b = true /\
      (Rabs (FT2R a) <=
       sqrt
         (F' /
          ((INR n.+1 + 1) *
           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ (n.+1 + 1)%coq_nat) -
          / 2 * bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)))%Re /\
      (Rabs (FT2R b) <=
       sqrt
         (F' /
          ((INR n.+1 + 1)*
           (1 + / 2 * bpow Zaux.radix2 (- fprec Tsingle + 1)) ^ (n.+1 + 1)%coq_nat) -
            / 2 * bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)))%Re).
{ specialize (H0 i).
  assert ((i < n.+1)%nat).
  { by rewrite size_map size_enum_ord in H1. } specialize (H0 H6).
  apply H0.
} specialize (H2 H6). clear H4 H5 H6.
destruct H2 as [ifH2 H2]. fold d e in H2. 
apply Rle_trans with (e_i (@inord n i) A v).
+ unfold e_i. fold d e.
  remember (combine
                (vec_to_list_float n.+1  (\row_j A (inord i) j)^T)
                (vec_to_list_float n.+1 v)) as L.
  unfold FT2R_mat. rewrite !mxE. 
  assert (\sum_j
             (\matrix_(i0, j0) FT2R (A i0 j0)) (inord i) j *
             (\matrix_(i0, j0) FT2R (v i0 j0)) j 0 = 
          dot_prodR (Flist_to_Rlist_pair L)).
  { assert (\sum_j
               (\matrix_(i0, j0) FT2R (A i0 j0)) (inord i) j *
               (\matrix_(i0, j0) FT2R (v i0 j0)) j 0  = 
            \sum_j (FT2R (A (@inord n i) j) * FT2R (v j 0))).
    { apply eq_big. by []. intros. by rewrite !mxE. } rewrite H4.
    assert (\sum_j FT2R (A (inord i) j) * FT2R (v j 0) = 
             \sum_j FT2R ((\row_j A (inord i) j)^T j 0) * FT2R (v j 0)).
    { apply eq_big. by []. intros. by rewrite !mxE. } rewrite H5.
    pose proof (@sum_dot n n.+1 Tsingle (leqnn n.+1)) .
    specialize (H6 (\row_j0 A (inord i) j0)^T v).
    rewrite HeqL.  rewrite -H6.
    apply eq_big. by []. intros. rewrite !mxE.
    assert (widen_ord (m:=n.+1) (leqnn n.+1) i0 = i0).
    { unfold widen_ord. apply val_inj. by simpl. }
    by rewrite H8. 
  } rewrite H4. rewrite -RminusE. unfold d, e. rewrite HeqL in H2.
  rewrite HeqL. 
  assert (vec_to_list_float n.+1 (\col_j v j 0) = vec_to_list_float n.+1 v).
  { assert (v = \col_j v j 0). 
    { apply matrixP. unfold eqrel. intros. rewrite !mxE.
      assert (y=0). { by apply ord1. } by rewrite H5.
    } by rewrite -H5.
  } rewrite H5. apply H2.
+ assert (e_i (inord i) A v = 
         [seq e_i i0 A v | i0 <- enum 'I_n.+1]`_i).
  { rewrite seq_equiv nth_mkseq. nra. by rewrite size_map size_enum_ord in H1. } 
  rewrite H4. apply /RleP.
  apply (@bigmaxr_ler _  _ [seq e_i i0 A v | i0 <- enum 'I_n.+1] i).
  rewrite size_map size_enum_ord.
  by rewrite size_map size_enum_ord in H1.
Qed.


End WITHNANS.
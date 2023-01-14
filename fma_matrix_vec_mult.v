From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib jacob_list_fun_model fma_dot_mat_model inf_norm_properties.

Require Import common fma_dot_acc float_acc_lems dotprod_model.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: Nans}. 

Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).



Definition e_i {n:nat} {ty} (i : 'I_n.+1) 
  (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1) := 
  let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
  let l2 := vec_to_list_float n.+1 v in
  let L := combine l1 l2 in
  let prods := map (uncurry Rmult) (map Rabsp (map FR2 L)) in
  let rs:= sum_fold prods in
  (g ty (length l1) * Rabs rs  + g1 ty (length l1) (length l1 - 1))%Re.


Definition mat_vec_mult_err_bnd {n:nat} {ty}
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):=
 bigmaxr 0%Re [seq (e_i i A v) | i <- enum 'I_n.+1].


Definition FT2R_mat {m n: nat} {ty} (A : 'M[ftype ty]_(m.+1, n.+1)) :
   'M[R]_(m.+1, n.+1):=
  \matrix_(i, j) FT2R (A i j).



Print vec_to_list_float.

Lemma zero_eq {ty}:
  neg_zero = Zconst ty 0.
Admitted.

Lemma dotprod_cons {t: type} (v1 v2: list (ftype t)) (x y : ftype t): 
  length v1 = length v2 ->
  dotprod_r (x :: v1) (y :: v2) = 
  BFMA x y (dotprod_r v1 v2).
Proof.
intros. by unfold dotprod_r. 
Qed.

Lemma fma_dot_prod_rel_holds {n:nat} {ty} m i
  (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1):
  fma_dot_prod_rel
  (combine
     (@vec_to_list_float _ n m (\row_j A (inord i) j)^T)
     (@vec_to_list_float _  n m v))
  (let l1 :=
     @vec_to_list_float _ n m (\row_j A (inord i) j)^T
     in
   let l2 := @vec_to_list_float _ n m v in
   dotprod_r l1 l2).
Proof.
induction m.
+ simpl. unfold dotprod_r. simpl. rewrite -zero_eq. apply fma_dot_prod_rel_nil.
+ simpl. rewrite !mxE. 
  assert ( (dotprod_r
             (A (inord i) (inord m)
              :: vec_to_list_float m (\row_j A (inord i) j)^T)
             (v (inord m) ord0 :: vec_to_list_float m v)) = 
            BFMA (A (inord i) (inord m)) (v (inord m) ord0) 
            (dotprod_r (vec_to_list_float m (\row_j A (inord i) j)^T)
                      (vec_to_list_float m v))).
  { apply dotprod_cons. by rewrite !length_veclist. } 
  rewrite H. by apply fma_dot_prod_rel_cons.
Qed.


Lemma R_dot_prod_rel_holds {n:nat} {ty} m i (le_n_m : (m <= n.+1)%nat)
  (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1):
  R_dot_prod_rel
  (combine
     (map FT2R
        (@vec_to_list_float _ n m 
           (\row_j A (inord i) j)^T))
     (map FT2R (@vec_to_list_float _ n m v)))
  (\sum_(j < m)
      FT2R_mat A (inord i) (@widen_ord m n.+1 le_n_m j) * 
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) 0).
Proof.
induction m.
+ simpl. rewrite big_ord0 //=. apply R_dot_prod_rel_nil.
+ simpl. rewrite !mxE. rewrite big_ord_recr //=.
  rewrite -RplusE -RmultE.
  assert ((widen_ord le_n_m ord_max) = (inord m)).
  { unfold widen_ord. 
    apply val_inj. simpl. by rewrite inordK.
  } rewrite H. rewrite Rplus_comm. rewrite !mxE.
  apply R_dot_prod_rel_cons.
  assert ((m <= n.+1)%nat). { by apply ltnW. }
  specialize (IHm H0). 
  assert (\sum_(j < m)
            FT2R_mat A (inord i)
              (widen_ord H0 j) *
            FT2R_mat v (widen_ord H0 j) 0 = 
          \sum_(i0 < m)
                FT2R_mat A (inord i)
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) *
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) 0).
  { apply eq_big. by []. intros.
    assert ((widen_ord le_n_m
                  (widen_ord (leqnSn m) i0))= 
             (widen_ord  H0 i0)).
    { unfold widen_ord. 
      apply val_inj. by simpl.
    } by rewrite H2.
  } rewrite -H1. apply IHm.
Qed.

Lemma R_dot_prod_rel_abs_holds {n:nat} {ty} m i
  (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1):
  R_dot_prod_rel
  (combine
     (map Rabs
        (map FT2R
           (@vec_to_list_float _ n m
              (\row_j A (inord i) j)^T)))
     (map Rabs
        (map FT2R (@vec_to_list_float _ n m v))))
  (sum_fold
     (map (uncurry Rmult)
        (map Rabsp
           (map FR2
              (combine
                 (@vec_to_list_float _ n m
                    (\row_j A (inord i) j)^T)
                 (@vec_to_list_float _ n m v)))))).
Proof.
induction m.
+ simpl. apply R_dot_prod_rel_nil.
+ simpl. rewrite !mxE. by apply R_dot_prod_rel_cons.
Qed.

(** Write a lemma for matrix-vector multiplication **)
Lemma matrix_vec_mult_bound {n:nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1),
  (forall (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
      Rabs (FT2R (fst (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty) /\
      Rabs (FT2R (snd (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty)) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  mat_vec_mult_err_bnd A v.
Proof.
intros. unfold vec_inf_norm, mat_vec_mult_err_bnd.
apply /RleP. apply bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H0.
pose proof (fma_dotprod_forward_error _ ty 
             (vec_to_list_float n.+1 (\row_j A (inord i) j)^T)
             (vec_to_list_float n.+1 v)).
rewrite !length_veclist in H1.
assert ((1 <= n.+1)%coq_nat). { lia. } 
assert (n.+1 = n.+1). { lia. } 
specialize (H1 H2 H3).
apply Rle_trans with (e_i (@inord n i) A v).
+ unfold e_i. rewrite !mxE -RminusE.
  rewrite !length_veclist.
  apply H1.
  assert (v = \col_j v j ord0).
  {  apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
      assert ( y = ord0). { apply ord1. } by rewrite H4.
  } rewrite -H4.
  - apply fma_dot_prod_rel_holds .
  - pose proof (@R_dot_prod_rel_holds n ty n.+1 i (leqnn n.+1)).
    specialize (H4 A v).
    assert (\sum_(j < n.+1)
               FT2R_mat A (inord i)
                 (widen_ord (leqnn n.+1) j) *
               FT2R_mat v
                 (widen_ord (leqnn n.+1) j) 0 = 
            \sum_j
               FT2R_mat A (inord i) j * FT2R_mat v j 0).
    { apply eq_big. by []. intros.
      assert (widen_ord (leqnn n.+1) i0 = i0).
      { unfold widen_ord. apply val_inj. by simpl. }
      by rewrite H6.
    } by rewrite -H5. 
  - apply R_dot_prod_rel_abs_holds.
  - intros. specialize (H xy (@inord n i)).
    rewrite inord_val in H. specialize (H H4).
    split; apply H.
  - apply (fma_is_finite _ ty (vec_to_list_float n.+1
       (\row_j A (inord i) j)^T) (vec_to_list_float n.+1 v)).
    * by rewrite !length_veclist.
    * assert (v = \col_j v j ord0).
      {  apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
        assert ( y = ord0). { apply ord1. } by rewrite H4.
      } rewrite -H4.
      apply fma_dot_prod_rel_holds.
    * intros.  rewrite length_veclist. specialize (H xy (@inord n i)).
    rewrite inord_val in H. specialize (H H4).
    destruct H as [Hf1 [Hf2 [Ha1 Ha2]]].
    repeat split; try by []; try by apply /RleP.
+ assert (e_i (inord i) A v = 
         [seq e_i i0 A v | i0 <- enum 'I_n.+1]`_i).
  { rewrite seq_equiv nth_mkseq. nra. by rewrite size_map size_enum_ord in H0. } 
  rewrite H4. apply /RleP.
  apply (@bigmaxr_ler _  _ [seq e_i i0 A v | i0 <- enum 'I_n.+1] i).
  rewrite size_map size_enum_ord.
  by rewrite size_map size_enum_ord in H0.
Qed.

End WITHNANS.
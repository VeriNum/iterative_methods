From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib fma_floating_point_model inf_norm_properties.

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

(* replace (length l1) by r *)

(* e_i_sparse *)
(* A is sparse as a hypothesis *)
(*  *)

(* Ask Mohit if there is definition for sparsity *)


Definition extract_non_zero_elmt {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) :=
  filter (fun x => negb (Req_bool (FT2R x) 0)) (vec_to_list_float n.+1 v).

Definition extract_non_zero_idx {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) :=
  let idx_seq := iota 0 n.+1 in
  let l := combine idx_seq (vec_to_list_float n.+1 v) in
  map fst (filter (fun x => negb (Req_bool (FT2R (snd x)) 0)) l).

Definition sparsity_fac {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) :=
  length (extract_non_zero_elmt v).

Definition is_r_sparse {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) (r : nat) :=
  le (sparsity_fac v) r.

Lemma non_zero_length {n : nat} {ty} (v : 'cV[ftype ty]_n.+1):
  length (extract_non_zero_elmt v) = length (extract_non_zero_idx v).
Proof.
  unfold extract_non_zero_elmt, extract_non_zero_idx.
  rewrite map_length.
  remember (vec_to_list_float n.+1 v) as l.
  assert (length l = n.+1).
  { rewrite Heql. by rewrite length_veclist. }
  clear Heql v.
  revert n H.
  induction l as [|h l']; intros.
  + simpl. reflexivity.
  + simpl. assert (length l' = n).
    { simpl in H. lia. }
    destruct (Req_bool (FT2R h) 0) eqn:Heq.
Admitted.


(* Variable ty : type.
Variable n : nat.
Variable A : 'M[ftype ty]_n.+1.

Variable i : 'I_n.+1.
Definition Ai := (\row_(j < n.+1) A i j)^T. *)

(* Check maxn. *)

Definition sparsity_fac_mat_row {n : nat} {ty} (A : 'M[ftype ty]_n.+1) (i : 'I_n.+1) :=
  sparsity_fac (\row_(j < n.+1) A i j)^T.

Definition is_r_sparse_mat {n : nat} {ty} (A : 'M[ftype ty]_n.+1) (r : nat) :=
  foldr and True [seq (is_r_sparse (row i A)^T r) | i <- enum 'I_n.+1].

Definition sparsity_fac_mat {n : nat} {ty} (A: 'M[ftype ty]_n.+1) :=
  foldr maxn 0%nat [seq (sparsity_fac_mat_row A i) | i <- enum 'I_n.+1].

(* Definition is_r_sparse_mat {n : nat} {ty} (A: 'M[ftype ty]_n.+1) (r : nat) :=
  le (sparsity_fac_mat A) r. *)

(* alternative: BIG-AND of "is_r_sparse row" *)

Definition e_i_sparse {n : nat} {ty} (i : 'I_n.+1)
  (A : 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1) 
  (r : nat) (HA : is_r_sparse_mat A r) :=
  let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
  let l2 := vec_to_list_float n.+1 v in
  let L := combine l1 l2 in
  let prods := map (uncurry Rmult) (map Rabsp (map FR2 L)) in
  let rs:= sum_fold prods in
  (g ty r * Rabs rs  + g1 ty r (r - 1))%Re.




(* Search (?A -> (seq.seq ?A) -> bool). *)
(* Definition extract_non_zero {n : nat} {ty} (r : nat) (v : 'cV[ftype ty]_n.+1) :=
  filter (fun x => x != 0) (vec_to_list_float n.+1 v). *)



(* leverage the old theorem *)
(* another vector to each new theorem *)
(* modify the definition *)
(* add arg r, extract non-zero elements *)
(* pre-condition: dim of new vector = dim of v *)

(* only assume that the first vector is sparse *)


Definition mat_vec_mult_err_bnd {n:nat} {ty}
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):=
 bigmaxr 0%Re [seq (e_i i A v) | i <- enum 'I_n.+1].


(* Variable n : nat.
Variable i : 'I_n.+1.
Variable ty : type.
Variable A : 'M[ftype ty]_n.+1. *)

Definition mat_vec_mult_err_bnd_sparse {n : nat} {ty}
  (A : 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1) 
  (r : nat) (HA : is_r_sparse_mat A r) :=
  bigmaxr 0%Re [seq (@e_i_sparse n ty i A v r HA) | i <- enum 'I_n.+1].


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
+ simpl. unfold dotprod_r. simpl. apply fma_dot_prod_rel_nil.
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
(* Locate "*f". *)

(* try proving a lemma that reduces sparse vectors to normal vectors first *)

(** Write a lemma for matrix-vector multiplication **)
Lemma matrix_vec_mult_bound {n:nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1),
  (forall (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    finite xy.1 /\finite xy.2) ->
  (forall (i : 'I_n.+1),
    finite  (let l1 := vec_to_list_float n.+1 (\row_j A (inord i) j)^T in
         let l2 := vec_to_list_float n.+1 (\col_j v j 0) in
         dotprod_r l1 l2)) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  mat_vec_mult_err_bnd A v.
Proof.
intros. unfold vec_inf_norm, mat_vec_mult_err_bnd.
apply /RleP. apply bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.
pose proof (fma_dotprod_forward_error _ ty 
            (vec_to_list_float n.+1 (\row_j A (inord i) j)^T)
             (vec_to_list_float n.+1 v)).
rewrite !length_veclist in H2.
assert (n.+1 = n.+1). { lia. } 
specialize (H2 H3).
apply Rle_trans with (e_i (@inord n i) A v).
+ unfold e_i. rewrite !mxE -RminusE.
  rewrite !length_veclist.
  apply H2.
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
  - intros. specialize (H0 (@inord n i)). 
    rewrite inord_val in H0. apply H0. 
+ assert (e_i (inord i) A v = 
         [seq e_i i0 A v | i0 <- enum 'I_n.+1]`_i).
  { rewrite seq_equiv nth_mkseq. nra. by rewrite size_map size_enum_ord in H1. } 
  rewrite H4. apply /RleP.
  apply (@bigmaxr_ler _  _ [seq e_i i0 A v | i0 <- enum 'I_n.+1] i).
  rewrite size_map size_enum_ord.
  by rewrite size_map size_enum_ord in H1.
Qed.

(* Locate "*v".
Print mulmx_float.
Variable n : nat.
Variable ty : type.
Variable v1 : 'cV[ftype ty]_n.+1.
Variable v2 : 'cV[ftype ty]_n.+1.
Definition v1_nonzero := extract_non_zero_elmt v1.
Definition r1 := sparsity_fac v1.

Check (ftype ty).
Search "zero".

Check (let l1 := vec_to_list_float n.+1 v1 in
         let l2 := vec_to_list_float n.+1 v2 in
         dotprod ty l1 l2). *)

Definition extract_elements {T} (idx : seq.seq nat) (l : list T) (default : T) :=
  map (fun i => nth i l default) idx.

Lemma extract_elements_length {T} (idx : seq.seq nat) (l : list T) (default : T):
  length (extract_elements idx l default) = length idx.
Proof.
  induction idx as [|h idx'].
  + simpl. auto.
  + simpl. rewrite IHidx'. auto.
Qed.

Lemma reduce_sparse_vec_vec_mult {n : nat} {ty}:
  forall (v1 v2 : 'cV[ftype ty]_n.+1) (r : nat) (Hv : is_r_sparse v1 r),
  let l1 := vec_to_list_float n.+1 v1 in
  let l2 := vec_to_list_float n.+1 v2 in
  let l1_nonzero := extract_non_zero_elmt v1 in
  let l2_nonzero := extract_elements (extract_non_zero_idx v1) l2 (Zconst ty 0) in
  dotprod_r l1 l2 = dotprod_r l1_nonzero l2_nonzero.
Proof.
  intros. unfold dotprod_r.
  assert (length l1 = length l2).
  { rewrite !length_veclist. auto. }
  assert (length l1_nonzero = length l2_nonzero).
  { unfold l1_nonzero, l2_nonzero. rewrite extract_elements_length.




  

Lemma matrix_vec_mult_bound_sparse {n : nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1)
  {r : nat} {HA : is_r_sparse_mat A r},
  (forall (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    finite xy.1 /\finite xy.2) ->
  (forall (i : 'I_n.+1),
    finite  (let l1 := vec_to_list_float n.+1 (\row_j A (inord i) j)^T in
         let l2 := vec_to_list_float n.+1 (\col_j v j 0) in
         dotprod_r l1 l2)) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  @mat_vec_mult_err_bnd_sparse n ty A v r HA.

Admitted.
  
Definition FT2R_abs {m n: nat} (A : 'M[R]_(m.+1, n.+1)) :=
  \matrix_(i,j) Rabs (A i j).

Lemma sum_abs_eq {n:nat} (f: 'I_n.+1 -> R):
  (forall i, (0 <= f i)%Re) ->
  Rabs (\sum_j (f j)) = \sum_j (f j).
Proof.
intros.
induction n.
+ simpl. rewrite big_ord_recr /= big_ord0 /=.
  rewrite add0r. rewrite Rabs_right. by []. apply Rle_ge. by apply H.
+ simpl. rewrite big_ord_recr /=. rewrite Rabs_right.
  by []. rewrite -RplusE. apply Rle_ge.
  apply Rplus_le_le_0_compat.
  - rewrite -IHn. apply Rabs_pos. 
    intros. apply H.
  - apply H.
Qed.


Lemma sum_fold_mathcomp_equiv {n:nat} {ty} m i (le_n_m : (m <= n.+1)%nat)
  (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1) :
  \sum_(j < m) FT2R_abs (FT2R_mat A) (inord i) (@widen_ord m n.+1 le_n_m j)
               * FT2R_abs (FT2R_mat v) (@widen_ord m n.+1 le_n_m j) 0 = 
   sum_fold
      (map (uncurry Rmult)
         (map Rabsp
            (map FR2
               (combine
                  (@vec_to_list_float _ n m
                     (\row_j A (inord i) j)^T)
                  (@vec_to_list_float _ n m v))))).
Proof.
induction m.
+ simpl. by rewrite big_ord0 /=. 
+ rewrite big_ord_recr /= !mxE.
   assert ((widen_ord le_n_m ord_max) = (inord m)).
  { unfold widen_ord. 
    apply val_inj. simpl. by rewrite inordK.
  } rewrite H. rewrite Rplus_comm. 
  assert ((m <= n.+1)%nat). { by apply ltnW. }
  specialize (IHm H0). 
  assert (\sum_(j < m)
               FT2R_abs (FT2R_mat A) (inord i)
                 (widen_ord H0 j) *
               FT2R_abs (FT2R_mat v) (widen_ord H0 j) 0 = 
           \sum_(i0 < m)
               FT2R_abs (FT2R_mat A) (inord i)
                 (widen_ord le_n_m (widen_ord (leqnSn m) i0)) *
               FT2R_abs (FT2R_mat v)
                 (widen_ord le_n_m (widen_ord (leqnSn m) i0)) 0).
  { apply eq_big. by []. intros.
    assert ((widen_ord le_n_m
                  (widen_ord (leqnSn m) i0))= 
             (widen_ord  H0 i0)).
    { unfold widen_ord. 
      apply val_inj. by simpl.
    } by rewrite H2.
  } rewrite -H1. by rewrite IHm.
Qed.




Lemma matrix_err_bound_equiv {n:nat} {ty}
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):
 mat_vec_mult_err_bnd A v = 
 vec_inf_norm (FT2R_abs (FT2R_mat A) *m FT2R_abs (FT2R_mat v)) * g ty n.+1 +
   g1 ty n.+1 (n.+1 - 1).
Proof.
unfold mat_vec_mult_err_bnd.
unfold vec_inf_norm. rewrite mulrC.
rewrite -bigmaxr_mulr.
+ apply bigmaxrP . split.
  - rewrite -bigmaxr_addr.
    assert ([seq y + g1 ty n.+1 (n.+1 - 1)
               | y <- [seq g ty n.+1 *
                           Rabs
                             ((FT2R_abs (FT2R_mat A) *m 
                               FT2R_abs (FT2R_mat v)) i 0)
                         | i <- enum 'I_n.+1]] = 
            [seq e_i i A v | i <- enum 'I_n.+1]).
    { rewrite seq_equiv. rewrite -map_comp.
      rewrite seq_equiv. apply eq_mkseq.
      unfold eqfun. intros.
      rewrite !mxE. unfold e_i.
      rewrite !length_veclist.
      pose proof (@sum_fold_mathcomp_equiv n ty n.+1 x (leqnn n.+1) A v).
      rewrite -H.
      assert (\sum_j
                  FT2R_abs (FT2R_mat A) (inord x) j *
                  FT2R_abs (FT2R_mat v) j 0 = 
              \sum_(j < n.+1)
                 FT2R_abs (FT2R_mat A) (inord x)
                   (widen_ord (leqnn n.+1) j) *
                 FT2R_abs (FT2R_mat v)
                   (widen_ord (leqnn n.+1) j) 0).
      { apply eq_big. by []. intros.
        assert (widen_ord (leqnn n.+1) i = i).
        { unfold widen_ord. apply val_inj. by simpl. }
        by rewrite H1.
      } by rewrite -H0.
    } rewrite H. apply bigmaxr_mem.
    by rewrite size_map size_enum_ord.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    unfold e_i. rewrite !length_veclist.
    apply /RleP. rewrite -RplusE.
    apply Rplus_le_compat_r.
    apply Rle_trans with 
    ([seq (g ty n.+1 *
         Rabs
           ((FT2R_abs (FT2R_mat A) *m 
             FT2R_abs (FT2R_mat v)) i0 0))%Ri
      | i0 <- enum 'I_n.+1]`_i).
    * rewrite seq_equiv. rewrite nth_mkseq;
      last by rewrite size_map size_enum_ord in H.
      rewrite -RmultE. rewrite !mxE.
      pose proof (@sum_fold_mathcomp_equiv n ty n.+1 i (leqnn n.+1) A v).
      rewrite -H0.
      assert (\sum_j
                  FT2R_abs (FT2R_mat A) (inord i) j *
                  FT2R_abs (FT2R_mat v) j 0 = 
              \sum_(j < n.+1)
                 FT2R_abs (FT2R_mat A) (inord i)
                   (widen_ord (leqnn n.+1) j) *
                 FT2R_abs (FT2R_mat v)
                   (widen_ord (leqnn n.+1) j) 0).
      { apply eq_big. by []. intros.
        assert (widen_ord (leqnn n.+1) i0 = i0).
        { unfold widen_ord. apply val_inj. by simpl. }
        by rewrite H2.
      } rewrite -H1. apply Rle_refl.
   * apply /RleP.
     apply (@bigmaxr_ler _ 0%Re [seq (g ty n.+1 *
                 Rabs
                   ((FT2R_abs (FT2R_mat A) *m 
                     FT2R_abs (FT2R_mat v)) i0 0))%Ri
              | i0 <- enum 'I_n.+1] i).
     rewrite size_map size_enum_ord.
     by rewrite size_map size_enum_ord in H.
+ apply /RleP. apply g_pos.
Qed.


Lemma matrix_err_bound_le_rel {n:nat} {ty}
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):
 mat_vec_mult_err_bnd A v <=
 (matrix_inf_norm (FT2R_mat A) * vec_inf_norm (FT2R_mat v)) * g ty n.+1 +
   g1 ty n.+1 (n.+1 - 1).
Proof.
unfold mat_vec_mult_err_bnd.
unfold vec_inf_norm, matrix_inf_norm.
rewrite mulrC. rewrite [in X in (_ * X + _)]mulrC.
rewrite -bigmaxr_mulr.
+ apply /RleP. rewrite -RplusE -RmultE.
  apply bigmax_le.
  - by rewrite size_map size_enum_ord.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    unfold e_i. rewrite !length_veclist.
    apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * apply g_pos.
    * apply Rle_trans with
      [seq (bigmaxr 0%Re
           [seq Rabs (FT2R_mat v i1 0)
              | i1 <- enum 'I_n.+1] *
         row_sum (FT2R_mat A) i0)%Ri
      | i0 <- enum 'I_n.+1]`_i.
      ++ assert ([seq bigmaxr 0%Re
                    [seq Rabs (FT2R_mat v i1 0)
                       | i1 <- enum 'I_n.+1] *
                    row_sum (FT2R_mat A) i0
                  | i0 <- enum 'I_n.+1] = 
                 mkseq (fun i: nat => (bigmaxr 0%Re
                                        [seq Rabs (FT2R_mat v i1 ord0)
                                           | i1 <- enum 'I_n.+1] *
                                      row_sum (FT2R_mat A) (@inord n i))%Re) n.+1).
          { rewrite !seq_equiv. by []. } rewrite H0. clear H0.
         rewrite nth_mkseq;
         last by rewrite size_map size_enum_ord in H.
         rewrite RmultE.
         unfold row_sum. rewrite big_distrr.
         rewrite -sum_fold_mathcomp_equiv.
         rewrite sum_abs_eq /=.
         -- apply /RleP. apply big_sum_ge_ex_abstract.
            intros. rewrite -RmultE.
            assert ((widen_ord (leqnn n.+1) i0) = i0).
            { unfold widen_ord. apply val_inj. by simpl. }
            rewrite H1. rewrite !mxE. rewrite mulrC.
            rewrite -RmultE. apply Rmult_le_compat_l.
            ** apply Rabs_pos.
            ** apply Rle_trans with
               [seq Rabs (FT2R_mat v i1 ord0)
                   | i1 <- enum 'I_n.+1]`_i0.
               +++ rewrite seq_equiv. rewrite nth_mkseq; 
                   last by apply ltn_ord.
                   rewrite !mxE /=. rewrite inord_val. apply Rle_refl.
               +++ apply /RleP. 
                   apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v i1 ord0)
                                                | i1 <- enum 'I_n.+1] i0).
                   rewrite size_map size_enum_ord. apply ltn_ord.
         -- intros. rewrite !mxE. rewrite -RmultE. 
            apply Rmult_le_pos; apply Rabs_pos.
     ++ apply /RleP.
        apply (@bigmaxr_ler _ 0%Re [seq bigmaxr 0%Re
                                           [seq Rabs (FT2R_mat v i1 0)
                                              | i1 <- enum 'I_n.+1] *
                                         row_sum (FT2R_mat A) i0
                                       | i0 <- enum 'I_n.+1] i).
        rewrite size_map size_enum_ord.
        by rewrite size_map size_enum_ord in H.
+ apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Qed.


Lemma matrix_vec_mult_bound_corollary {n:nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1),
  (forall (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    finite xy.1 /\  finite xy.2) ->
  (forall (i : 'I_n.+1),
    finite
        (let l1 := vec_to_list_float n.+1 (\row_j A (inord i) j)^T in
         let l2 := vec_to_list_float n.+1 (\col_j v j 0) in
         dotprod_r l1 l2) ) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  (matrix_inf_norm (FT2R_mat A) * vec_inf_norm (FT2R_mat v)) * g ty n.+1 +
   g1 ty n.+1 (n.+1 - 1).
Proof.
intros.
apply /RleP.
apply Rle_trans with (mat_vec_mult_err_bnd A v).
+ apply /RleP. by apply matrix_vec_mult_bound.
+ apply /RleP. apply matrix_err_bound_le_rel.
Qed.

End WITHNANS.

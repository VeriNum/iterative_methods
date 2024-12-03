From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

From mathcomp Require Import all_ssreflect ssralg ssrnat (*all_algebra*) seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPStdLib.

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

Import Order.TTheory GRing.Theory (*Num.Def Num.Theory*).


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

Definition extract_elements {T} (idx : seq.seq nat) (l : list T) (default : T) :=
  map (fun i => nth i l default) idx.

Lemma extract_elements_length {T} (idx : seq.seq nat) (l : list T) (default : T):
  length (extract_elements idx l default) = length idx.
Proof.
  induction idx as [|h idx'].
  + simpl. auto.
  + simpl. rewrite IHidx'. auto.
Qed.

Lemma extract_elements_succ {T} (idx : seq.seq nat) (x : T) (l : list T) (default : T) :
  extract_elements (map S idx) (x :: l) default = extract_elements idx l default.
Proof.
  induction idx as [|i0 idx'].
  + simpl. auto.
  + simpl. f_equal. auto.
Qed.

Fixpoint extract_nonzero_idx_aux {ty} (l : list (ftype ty)) (k : nat) : list nat :=
  match l with 
  | [] => []
  | h :: t => if (BCMP Eq false h (Zconst ty 0)) 
      then k :: extract_nonzero_idx_aux t (S k) 
      else extract_nonzero_idx_aux t (S k) 
  end.

Definition extract_nonzero_idx {ty} (l : list (ftype ty)) :=
  extract_nonzero_idx_aux l 0.

Definition a := map (Zconst Tsingle) ([0; 3; 0; 5; 7; 0; 9])%Z.
Definition b := extract_nonzero_idx a.
Compute b.

Fixpoint nat_extract_nonzero_idx_aux (l : list nat) (k : nat) : list nat :=
  match l with 
  | [] => []
  | h :: t => if (negb (Nat.eqb h 0)) 
      then k :: nat_extract_nonzero_idx_aux t (S k) 
      else nat_extract_nonzero_idx_aux t (S k) 
  end.

Definition nat_extract_nonzero_idx (l : list nat) :=
  nat_extract_nonzero_idx_aux l 0.

Definition extract_nonzero_elmt {ty} (l : list (ftype ty)) :=
  extract_elements (extract_nonzero_idx l) l (Zconst ty 0).

Lemma extract_nonzero_idx_nil {ty} : @extract_nonzero_idx ty [] = [].
Proof.
  unfold extract_nonzero_idx. simpl. auto.
Qed.

Lemma extract_nonzero_elmt_nil {ty} : @extract_nonzero_elmt ty [] = [].
Proof.
  unfold extract_nonzero_elmt. rewrite extract_nonzero_idx_nil. simpl. auto.
Qed.

Lemma extract_nonzero_idx_aux_cons {ty} : forall x l k,
  @extract_nonzero_idx_aux ty (x :: l) k = 
  if (BCMP Eq false x (Zconst ty 0)) then k%nat :: (extract_nonzero_idx_aux l k.+1) else (extract_nonzero_idx_aux l k.+1).
Proof.
  intros. simpl. destruct (BCMP Eq false x (Zconst ty 0)) eqn:E; auto.
Qed.

Lemma extract_nonzero_idx_aux_succ {ty} : forall l k,
  @extract_nonzero_idx_aux ty l (k.+1) = map S (extract_nonzero_idx_aux l k).
Proof.
  intros. revert k. induction l as [|h l'].
  + simpl. reflexivity.
  + intros. repeat rewrite extract_nonzero_idx_aux_cons.
    destruct (BCMP Eq false h (Zconst ty 0)) eqn:E.
    - simpl. rewrite IHl'. reflexivity.
    - simpl. rewrite IHl'. reflexivity.
Qed.  

Lemma extract_nonzero_idx_cons {ty} : forall x l,
  @extract_nonzero_idx ty (x :: l) = 
  if (BCMP Eq false x (Zconst ty 0)) then 0%nat :: map S (extract_nonzero_idx l) else map S (extract_nonzero_idx l).
Proof.
  intros. destruct (BCMP Eq false x (Zconst ty 0)) eqn:E.
  + unfold extract_nonzero_idx in *. rewrite <- extract_nonzero_idx_aux_succ.
    rewrite extract_nonzero_idx_aux_cons. rewrite E. auto.
  + unfold extract_nonzero_idx in *. rewrite <- extract_nonzero_idx_aux_succ.
    rewrite extract_nonzero_idx_aux_cons. rewrite E. auto.
Qed. 

Lemma extract_nonzero_elmt_cons {ty} : forall x l,
  @extract_nonzero_elmt ty (x :: l) = 
  if (BCMP Eq false x (Zconst ty 0)) then x :: extract_nonzero_elmt l else extract_nonzero_elmt l.
Proof.
  intros. unfold extract_nonzero_elmt.
  destruct (BCMP Eq false x (Zconst ty 0)) eqn:E.
  + rewrite extract_nonzero_idx_cons. rewrite E. simpl.
    f_equal. rewrite extract_elements_succ. auto.
  + rewrite extract_nonzero_idx_cons. rewrite E. simpl.
    rewrite extract_elements_succ. auto.
Qed.

Definition sparsity_fac_aux {ty} (l : list (ftype ty)) :=
  length (extract_nonzero_idx l).

Definition sparsity_fac {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) :=
  sparsity_fac_aux (vec_to_list_float n.+1 v).

Definition is_r_sparse_aux {ty} (l : list (ftype ty)) (r : nat) :=
  le (sparsity_fac_aux l) r.

Definition is_r_sparse {n : nat} {ty} (v : 'cV[ftype ty]_n.+1) (r : nat) :=
  is_r_sparse_aux (vec_to_list_float n.+1 v) r.

Lemma extract_nonzero_length {ty} (l : list (ftype ty)):
  length (@extract_nonzero_elmt ty l) = length (@extract_nonzero_idx ty l).
Proof.
  unfold extract_nonzero_elmt. 
  rewrite extract_elements_length.
  reflexivity.
Qed.

Definition sparsity_fac_mat_row {n : nat} {ty} (A : 'M[ftype ty]_n.+1) (i : 'I_n.+1) :=
  sparsity_fac (\row_(j < n.+1) A i j)^T.

Definition is_r_sparse_mat {n : nat} {ty} (A : 'M[ftype ty]_n.+1) (r : nat) :=
  forall (i : 'I_n.+1), is_r_sparse (\row_j A (i) j)^T r.

Definition sparsity_fac_mat {n : nat} {ty} (A: 'M[ftype ty]_n.+1) :=
  foldr maxn 0%nat [seq (sparsity_fac_mat_row A i) | i <- enum 'I_n.+1].

Definition e_i_sparse {n : nat} {ty} (i : 'I_n.+1)
  (A : 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1) 
  (r : nat) (HA : is_r_sparse_mat A r) :=
  let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
  let l2 := vec_to_list_float n.+1 v in
  let L := combine l1 l2 in
  let prods := map (uncurry Rmult) (map Rabsp (map FR2 L)) in
  let rs:= sum_fold prods in
  (g ty r * Rabs rs  + g1 ty r (r - 1))%Re.

Definition mat_vec_mult_err_bnd {n:nat} {ty}
 (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1):=
 bigmaxr 0%Re [seq (e_i i A v) | i <- enum 'I_n.+1].

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
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) ord0).
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
            FT2R_mat v (widen_ord H0 j) ord0 = 
          \sum_(i0 < m)
                FT2R_mat A (inord i)
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) *
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) ord0).
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
    finite xy.1 /\finite xy.2) ->
  (forall (i : 'I_n.+1),
    finite  (let l1 := vec_to_list_float n.+1 (\row_j A (inord i) j)^T in
         let l2 := vec_to_list_float n.+1 (\col_j v j ord0) in
         dotprod_r l1 l2)) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  mat_vec_mult_err_bnd A v.
Proof.
intros. unfold vec_inf_norm, mat_vec_mult_err_bnd.
apply lemmas.bigmax_le; first by rewrite size_map size_enum_ord.
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
                 (widen_ord (leqnn n.+1) j) ord0 = 
            \sum_j
               FT2R_mat A (inord i) j * FT2R_mat v j ord0).
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

Lemma bcmp_zero {ty} (x : ftype ty) :
  BCMP Eq false x (Zconst ty 0) = false ->
  finite x ->
  feq x (Zconst ty 0).
Proof.
  intros. destruct x; auto; inversion H0.
  unfold BCMP in H. unfold extend_comp in H. unfold Bcompare in H.
  unfold BinarySingleNaN.Bcompare in H. simpl in H. destruct s; inversion H.
Qed.

Lemma bcmp_nonzero {ty} (x : ftype ty) : 
  BCMP Eq false x (Zconst ty 0) = true ->
  finite x ->
  ~ feq x (Zconst ty 0).
Proof.
  intros. destruct x; auto; inversion H0.
Qed.

Lemma bfma_bcmp_zero {ty} (x y z : ftype ty):
  BCMP Eq false x (Zconst ty 0) = false ->
  finite x ->
  finite y ->
  feq (BFMA x y z) z.
Proof.
  intros. rewrite (bcmp_zero H); auto.
  rewrite BFMA_zero1; auto.
Qed.

Definition list_finite {ty} (l : list (ftype ty)) :=
  forall x, In x l -> finite x.

Lemma list_finite_nil {ty} : list_finite (@nil (ftype ty)).
Proof.
  unfold list_finite. intros. inversion H.
Qed.

Lemma list_finite_cons {ty} : forall x l,
  finite x ->
  @list_finite ty l ->
  list_finite (x :: l).
Proof.
  unfold list_finite. intros. simpl in H1. destruct H1.
  + subst x0. auto.
  + apply H0. auto.
Qed.

Lemma list_finite_cons_inv {ty} : forall x l,
  @list_finite ty (x :: l) ->
  finite x /\ list_finite l.
Proof.
  unfold list_finite. intros. split.
  + apply H. simpl. auto.
  + intros. apply H. simpl. auto.
Qed.

Lemma extract_elements_inclusion {ty} : forall (l : list (ftype ty)) idx d x,
  In x (extract_elements idx l d) ->
  In x l \/ x = d.
Proof.
  intros. induction idx as [|i' idx'].
  + simpl in H. destruct H.
  + simpl in H. destruct H.
    - pose proof (nth_in_or_default i' l d). subst x. 
      destruct H0; [left | right]; auto.
    - apply (IHidx' H).
Qed.

Lemma list_finite_extract {ty} : forall (l : list (ftype ty)) idx d,
  list_finite l ->
  finite d ->
  list_finite (extract_elements idx l d).
Proof.
  unfold list_finite. intros.
  pose proof (extract_elements_inclusion H1). destruct H2.
  + apply (H x H2).
  + subst x. apply H0.
Qed.

Definition list_list_finite {ty} (l : list (list (ftype ty))) :=
  forall x, In x l -> list_finite x.

Lemma list_list_finite_nil {ty} : list_list_finite (@nil (list (ftype ty))).
Proof.
  unfold list_list_finite. intros. inversion H.
Qed.

Lemma list_list_finite_cons {ty} : forall x l,
  list_finite x ->
  @list_list_finite ty l ->
  list_list_finite (x :: l).
Proof.
  unfold list_list_finite. intros. simpl in H1. destruct H1.
  + subst x0. auto.
  + apply H0. auto.
Qed.

Lemma reduce_sparse_vec_vec_mult {ty}:
  forall (l1 l2 : seq.seq (ftype ty)),
  let l1_nonzero := @extract_nonzero_elmt ty l1 in
  let l2_nonzero := extract_elements (@extract_nonzero_idx ty l1) l2 (Zconst ty 0) in
  length l1 = length l2 ->
  list_finite l1 ->
  list_finite l2 ->
  feq (dotprod_r l1 l2) (dotprod_r l1_nonzero l2_nonzero).
Proof.
  intros.
  revert l2 H H1 l2_nonzero.
  induction l1 as [| x1 l1']; intros.
  + simpl in H. destruct l2; auto.
  + destruct l2 as [| x2 l2']; [inversion H|].
    simpl in *. inversion H. clear H.
    pose proof (proj2 (list_finite_cons_inv H0)).
    pose proof (proj2 (list_finite_cons_inv H1)).
    specialize (IHl1' H l2' H3 H2).
    rewrite dotprod_cons; auto.
    destruct (BCMP Eq false x1 (Zconst ty 0)) eqn:E.
    - subst l1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst l2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ. rewrite dotprod_cons.
      2:{ rewrite extract_elements_length. rewrite extract_nonzero_length. auto. }
      rewrite IHl1'. auto.
    - pose proof (proj1 (list_finite_cons_inv H0)).
      pose proof (proj1 (list_finite_cons_inv H1)).
      rewrite bfma_bcmp_zero; auto.
      subst l1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst l2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ. rewrite IHl1'. auto.
Qed.

Lemma op_defs_BFMA_zero1 {ty} y s:
  strict_feq y y ->
  feq (op_defs.BFMA (Zconst ty 0) y s) s.
Proof.
  intros.
  intros.
  change (Zconst ty 0) with 
    (Binary.B754_zero (fprec ty)  (femax ty) false).
  unfold BFMA, BPLUS, BINOP in *.
  destruct y, s; try discriminate; simpl; auto.
Qed.

Lemma fma_dot_prod_rel_holds_vec {ty} (l1 l2 : seq.seq (ftype ty)) :
  length l1 = length l2 ->
  fma_dot_prod_rel (combine l1 l2) (dotprod_r l1 l2).
Proof.
  intros. revert l2 H. induction l1 as [|x1 l1']; intros.
  + destruct l2. 2:{ inversion H. }
    unfold dotprod_r. simpl. apply fma_dot_prod_rel_nil.
  + destruct l2 as [|x2 l2']; inversion H.
    specialize (IHl1' l2' H1).
    apply fma_dot_prod_rel_cons. apply IHl1'.
Qed.

Lemma fma_dot_prod_rel_hold_vec_inv {ty} (l1 l2 : seq.seq (ftype ty)) :
  length l1 = length l2 ->
  forall p, fma_dot_prod_rel (combine l1 l2) p -> feq p (dotprod_r l1 l2).
Proof.
  revert l2. induction l1 as [|x1 l1']; intros.
  + destruct l2; try inversion H.
    inversion H0. auto.
  + destruct l2 as [|x2 l2']; inversion H. inversion H0.
    specialize (IHl1' l2' H2 s H5).
    rewrite dotprod_cons; auto. simpl. rewrite <- IHl1'. auto.
Qed.

Lemma feq_zero {ty} (x : ftype ty) :
  feq x (Zconst ty 0) ->
  x = B754_zero (fprec ty) (femax ty) true \/ x = B754_zero _ _ false.
Proof.
  intros. destruct x; try inversion H.
  destruct s; auto.
Qed.

Lemma bfma_zero_eq {ty} (x y z : ftype ty) :
  feq x (Zconst ty 0) ->
  finite y ->
  BFMA x y z = z.
Proof.
  intros. pose proof (feq_zero H). destruct H1 eqn:Ex; subst.
  + unfold BFMA. unfold Bfma. unfold BSN2B. unfold BinarySingleNaN.Bfma. simpl.
    destruct y; try inversion H0; simpl.
    - destruct z. 
      * simpl. unfold BinarySingleNaN.Bfma_szero. simpl. 
        destruct s eqn:E; destruct s0 eqn:E0; simpl; auto.
Abort.

Lemma fma_dot_prod_rel_holds_sparse {ty} :
  forall (l1 l2 : seq.seq (ftype ty)),
  let l1_nonzero := @extract_nonzero_elmt ty l1 in
  let l2_nonzero := extract_elements (@extract_nonzero_idx ty l1) l2 (Zconst ty 0) in
  length l1 = length l2 ->
  list_finite l1 ->
  list_finite l2 ->
  forall fp,
  fma_dot_prod_rel (combine l1 l2) fp ->
  fma_dot_prod_rel (combine l1_nonzero l2_nonzero) fp.
Abort.

Lemma fma_dot_prod_rel_holds_sparse {ty} : 
  forall (l1 l2 : seq.seq (ftype ty)),
  let l1_nonzero := @extract_nonzero_elmt ty l1 in
  let l2_nonzero := extract_elements (@extract_nonzero_idx ty l1) l2 (Zconst ty 0) in
  length l1 = length l2 ->
  list_finite l1 ->
  list_finite l2 ->
  forall fp,
  fma_dot_prod_rel (combine l1 l2) fp ->
  exists fp', feq fp fp' /\ fma_dot_prod_rel (combine l1_nonzero l2_nonzero) fp'.
Proof.
  intros. generalize dependent l2. revert fp.
  induction l1 as [| x1 l1']; intros.
  + destruct l2; try inversion H. inversion H2.
    exists fp. subst fp. split; auto.
  + destruct l2 as [| x2 l2']; inversion H.
    simpl in *. clear H.
    pose proof (proj2 (list_finite_cons_inv H0)).
    pose proof (proj2 (list_finite_cons_inv H1)).
    inversion H2. simpl in H6. rename s into fps. subst xy l. simpl in *.
    specialize (IHl1' H fps l2' H4 H3 H8).
    destruct IHl1' as [fps' [? ?]].
    pose proof (proj1 (list_finite_cons_inv H0)).
    destruct (BCMP Eq false x1 (Zconst ty 0)) eqn:E.
    - subst l1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst l2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ. exists (op_defs.BFMA x1 x2 fps'). split.
      2:{ constructor. auto. }
      rewrite H5. auto.
    - subst l1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst l2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ.
      pose proof (bcmp_zero E (proj1 (list_finite_cons_inv H0))).
      assert (feq (op_defs.BFMA x1 x2 fps) fps).
      { rewrite H10. rewrite op_defs_BFMA_zero1. auto.  
        pose proof (proj1 (list_finite_cons_inv H1)). auto. }
      exists fps'. split; auto.
      rewrite H11. auto.
Qed. 

Lemma bcmp_zero_b754zero {ty} (x : ftype ty) :
  BCMP Eq false x (Zconst ty 0) = false ->
  finite x ->
  exists b, x = B754_zero _ _ b.
Proof.
  intros. pose proof (bcmp_zero H H0).
  destruct x; inversion H1.
  exists s; auto.
Qed.

Lemma R_dot_prod_rel_holds_sparse {ty} (v1 v2 : list (ftype ty)) (rp : R):
  let v1_nonzero := @extract_nonzero_elmt ty v1 in
  let v2_nonzero := extract_elements (@extract_nonzero_idx ty v1) v2 (Zconst ty 0) in
  length v1 = length v2 ->
  list_finite v1 ->
  list_finite v2 ->
  R_dot_prod_rel (combine (map FT2R v1) (map FT2R v2)) rp ->
  R_dot_prod_rel (combine (map FT2R v1_nonzero) (map FT2R v2_nonzero)) rp.
Proof.
  intros. generalize dependent v2. revert rp. induction v1 as [| x1 v1']; intros.
  + destruct v2; inversion H. simpl.
    inversion H2. subst. constructor.
  + destruct v2 as [| x2 v2']; inversion H.
    simpl in *. clear H.
    pose proof (proj2 (list_finite_cons_inv H0)).
    pose proof (proj2 (list_finite_cons_inv H1)).
    inversion H2; subst. rename s into rp'; simpl in *.
    specialize (IHv1' H rp' v2' H4 H3 H8).
    destruct (BCMP Eq false x1 (Zconst ty 0)) eqn:E.
    - subst v1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst v2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      constructor. rewrite extract_elements_succ. auto.
    - subst v1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst v2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ.
      pose proof (bcmp_zero_b754zero E (proj1 (list_finite_cons_inv H0))).
      destruct H5 as [b ?]. subst x1. simpl.
      rewrite Rmult_0_l. rewrite Rplus_0_l. auto.
Qed.

Lemma R_dot_prod_rel_abs_holds_sparse {ty} (v1 v2 : list (ftype ty)) (rp_abs : R):
  let v1_nonzero := @extract_nonzero_elmt ty v1 in
  let v2_nonzero := extract_elements (@extract_nonzero_idx ty v1) v2 (Zconst ty 0) in
  length v1 = length v2 ->
  list_finite v1 ->
  list_finite v2 ->
  R_dot_prod_rel (combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) rp_abs ->
  R_dot_prod_rel (combine (map Rabs (map FT2R v1_nonzero)) (map Rabs (map FT2R v2_nonzero))) rp_abs.
Proof.
  intros. generalize dependent v2. revert rp_abs. induction v1 as [| x1 v1']; intros.
  + destruct v2; inversion H. simpl.
    inversion H2. subst. constructor.
  + destruct v2 as [| x2 v2']; inversion H.
    simpl in *. clear H.
    pose proof (proj2 (list_finite_cons_inv H0)).
    pose proof (proj2 (list_finite_cons_inv H1)).
    inversion H2; subst. rename s into rp'; simpl in *.
    specialize (IHv1' H rp' v2' H4 H3 H8).
    destruct (BCMP Eq false x1 (Zconst ty 0)) eqn:E.
    - subst v1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst v2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      constructor. rewrite extract_elements_succ. auto.
    - subst v1_nonzero. rewrite extract_nonzero_elmt_cons. rewrite E.
      subst v2_nonzero. rewrite extract_nonzero_idx_cons. rewrite E. simpl.
      rewrite extract_elements_succ.
      pose proof (bcmp_zero_b754zero E (proj1 (list_finite_cons_inv H0))).
      destruct H5 as [b ?]. subst x1. simpl.
      rewrite Rabs_R0. rewrite Rmult_0_l. rewrite Rplus_0_l. auto.
Qed.

Lemma feq_finite {ty} (x y : ftype ty) :
  feq x y ->
  finite x -> 
  finite y.
Proof.
  intros. destruct x; destruct y; inversion H; inversion H0; simpl; auto.
Qed.

Lemma feq_to_r {ty} (x y : ftype ty) :
  feq x y ->
  FT2R x = FT2R y.
Proof.
  intros.
  destruct x; destruct y; inversion H; simpl; auto.
  destruct H1; subst s0 m0 e1. auto.
Qed. 

Lemma g_increasing {ty} (n n' : nat) :
  le n n' ->
  Rle (g ty n) (g ty n').
Proof.
  intros. unfold g. 
  pose proof (default_rel_ge_0 ty).
  remember (default_rel ty) as p.
  clear Heqp. induction H.
  + right. auto.
  + eapply Rle_trans; [apply IHle |].
    unfold pow; fold pow. 
    apply Rplus_le_compat_r.
    rewrite Rmult_comm.
    rewrite <- (Rmult_1_r ((1+p)^m)) at 1.
    apply Rmult_le_compat_l; try lra.
    apply Rlt_le. apply pow_lt. lra.
Qed.

Lemma g1_increasing {ty} (n n' m m': nat) :
  le n n' ->
  le m m' ->
  Rle (g1 ty n m) (g1 ty n' m').
Proof.
  intros. unfold g1.
  pose proof (default_abs_ge_0 ty).
  eapply Rmult_le_compat.
  + apply Rmult_le_pos.
    - apply pos_INR.
    - apply H1.
  + pose proof (g_pos ty m). lra. 
  + pose proof (le_INR n n' H). 
    pose proof (pos_INR n). 
    apply Rmult_le_compat_r; auto.
  + pose proof (@g_increasing ty m m' H0). lra.
Qed.

Lemma le_minus_1 {a b : nat} :
  (a <= b)%coq_nat -> (a - 1 <= b - 1)%coq_nat.
Proof.
  intros H.
  destruct a; destruct b; try lia.
  + unfold subn. simpl. lia.
  + unfold subn. simpl. unfold subn_rec. simpl. lia.
Qed.

Lemma fma_dotprod_forward_error_sparse {ty}:
  forall (v1 v2 : seq.seq (ftype ty)) (r : nat) (HA : is_r_sparse_aux v1 r),
  length v1 = length v2 ->
  list_finite v1 ->
  list_finite v2 ->
  forall (fp : ftype ty) (rp rp_abs : R),
  fma_dot_prod_rel (combine v1 v2) fp ->
  R_dot_prod_rel (combine (map FT2R v1) (map FT2R v2)) rp ->
  R_dot_prod_rel (combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) rp_abs ->
  finite fp ->
  (Rabs (FT2R fp - rp) <= g ty r * Rabs rp_abs + g1 ty r (r-1)%nat)%Re.
 Proof.
  intros.
  remember (@extract_nonzero_elmt ty v1) as v1_nonzero.
  remember (extract_elements (@extract_nonzero_idx ty v1) v2 (Zconst ty 0)) as v2_nonzero.
  assert (length v1_nonzero = length v2_nonzero) as Hl.
  { unfold extract_nonzero_elmt in Heqv1_nonzero.
    subst. repeat rewrite extract_elements_length. auto. }
  pose proof (fma_dotprod_forward_error _ _ v1_nonzero v2_nonzero Hl).
  pose proof (fma_dot_prod_rel_holds_sparse H H0 H1 H2).
  destruct H7 as [fp' [? ?]].
  rewrite <- Heqv1_nonzero, <- Heqv2_nonzero in H8.
  pose proof (R_dot_prod_rel_holds_sparse H H0 H1 H3).
  pose proof (R_dot_prod_rel_abs_holds_sparse H H0 H1 H4).
  pose proof (feq_finite H7 H5).
  rewrite <- Heqv1_nonzero, <- Heqv2_nonzero in H9.
  rewrite <- Heqv1_nonzero, <- Heqv2_nonzero in H10.
  specialize (H6 fp' rp rp_abs H8 H9 H10 H11).
  clear H8 H9 H10 H11.
  rewrite (feq_to_r H7).
  eapply Rle_trans; [apply H6 |].
  assert (length v1_nonzero <= r)%coq_nat.
  { rewrite Heqv1_nonzero. unfold is_r_sparse_aux, sparsity_fac_aux in HA.
    unfold extract_nonzero_elmt. rewrite extract_elements_length. auto. }
  assert (length v1_nonzero - 1 <= r - 1)%coq_nat. 
  { apply le_minus_1. auto. } 
  pose proof (@g_increasing ty (length v1_nonzero) r H8).
  pose proof (@g1_increasing ty (length v1_nonzero) r (length v1_nonzero - 1) (r - 1) H8 H9).
  apply Rplus_le_compat.
  + apply Rmult_le_compat_r; auto. apply Rabs_pos.
  + apply H11.
Qed.

Lemma in_combine_inv_l {A} (l1 l2 : list A) (x : A) :
  In x l1 ->
  length l1 = length l2 ->
  exists y, In (x, y) (combine l1 l2).
Proof.
  intros. generalize dependent l2.
  induction l1 as [| x1 l1']; intros.
  + inversion H.
  + destruct l2 as [| x2 l2']; inversion H0.
    simpl in *. destruct H.
    - subst x1. exists x2. auto.
    - destruct (IHl1' H l2' H2) as [y ?].
      exists y. auto.
Qed.

Lemma in_combine_inv_r {A} (l1 l2 : list A) (y : A) :
  In y l2 ->
  length l1 = length l2 ->
  exists x, In (x, y) (combine l1 l2).
Proof.
  intros. generalize dependent l1.
  induction l2 as [| x2 l2']; intros.
  + inversion H.
  + destruct l1 as [| x1 l1']; inversion H0.
    simpl in *. destruct H.
    - subst. exists x1. auto.
    - destruct (IHl2' H l1' H2) as [x ?].
      exists x. auto.
Qed.

Lemma combine_finite {ty} (l1 l2 : seq.seq (ftype ty)) :
  length l1 = length l2 ->
  (forall xy , In xy (combine l1 l2) -> finite xy.1 /\ finite xy.2) ->
  list_finite l1 /\ list_finite l2.
Proof.
  intros. split.
  + unfold list_finite. intros.
    destruct (in_combine_inv_l H1 H) as [y ?].
    specialize (H0 (x, y) H2). auto. destruct H0. auto.
  + unfold list_finite. intros.
    destruct (in_combine_inv_r H1 H) as [y ?].
    specialize (H0 (y, x) H2). auto. destruct H0. auto.
Qed.

Lemma matrix_vec_mult_bound_sparse {n : nat} {ty}:
  forall (A: 'M[ftype ty]_n.+1) (v : 'cV[ftype ty]_n.+1)
  {r : nat} {HA : is_r_sparse_mat A r},
  (forall (xy : ftype ty * ftype ty) (i : nat),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    finite xy.1 /\finite xy.2) ->
  (forall (i : 'I_n.+1),
    finite  (let l1 := vec_to_list_float n.+1 (\row_j A (inord i) j)^T in
         let l2 := vec_to_list_float n.+1 (\col_j v j ord0) in
         dotprod_r l1 l2)) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  @mat_vec_mult_err_bnd_sparse n ty A v r HA.
Proof.
  intros. unfold vec_inf_norm, mat_vec_mult_err_bnd_sparse.
  (*apply /RleP.*) apply lemmas.bigmax_le; first by rewrite size_map size_enum_ord.

  intros. rewrite seq_equiv. 
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H1.

  remember (vec_to_list_float n.+1 (\row_j A (inord i) j)^T) as l1.
  remember (vec_to_list_float n.+1 (\col_j v j ord0)) as l2.
  pose proof (@fma_dotprod_forward_error_sparse ty l1 l2 r).

  assert (is_r_sparse_aux l1 r).
  { unfold is_r_sparse_mat in HA. unfold is_r_sparse in HA.
    rewrite Heql1. specialize (HA (inord i)). apply HA. }

  assert (length l1 = length l2).
  { rewrite Heql1. rewrite Heql2. rewrite !length_veclist. auto. }

  assert (list_finite l1).
  { pose proof (@combine_finite ty l1 l2 H4). apply H5.
    intros. rewrite Heql1 Heql2 in H6. 
    assert (v = \col_j v j ord0).
    { apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
      assert ( y = ord0). { apply ord1. } by rewrite H7. }
    rewrite -H7 in H6. clear H7.
    apply (H xy (i)). apply H6.
  }

  assert (list_finite l2).
  { pose proof (@combine_finite ty l1 l2 H4). apply H6.
    intros. rewrite Heql1 Heql2 in H7. 
    assert (v = \col_j v j ord0).
    { apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
      assert ( y = ord0). { apply ord1. } by rewrite H8. }
    rewrite -H8 in H7. clear H8.
    apply (H xy (i)). apply H7.
  }
  specialize (H2 H3 H4 H5 H6).

  apply Rle_trans with (@e_i_sparse n ty (@inord n i) A v r HA).
  + unfold e_i_sparse. rewrite !mxE -RminusE.
    apply H2.
    - rewrite <- Heql1. 
      change GRing.zero with (@ord0 O).
      rewrite <- Heql2. simpl. subst.
      apply fma_dot_prod_rel_holds.
    - pose proof (@R_dot_prod_rel_holds n ty n.+1 i (leqnn n.+1) A v).
      subst.
      assert (\sum_(j < n.+1)
                FT2R_mat A (inord i) (widen_ord (leqnn n.+1) j) *
                FT2R_mat v (widen_ord (leqnn n.+1) j) ord0 = 
              \sum_j
                FT2R_mat A (inord i) j * FT2R_mat v j ord0).
      { apply eq_big. by []. intros.
        assert (widen_ord (leqnn n.+1) i0 = i0).
        { unfold widen_ord. apply val_inj. by simpl. }
        by rewrite H9. }
      rewrite -H8.
      assert (v = \col_j v j ord0).
      { apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
        assert ( y = ord0). { apply ord1. } by rewrite H9.
      } rewrite -H9. auto.
    - pose proof (@R_dot_prod_rel_abs_holds n ty n.+1 i A v).
      rewrite Heql1 Heql2.
      assert (v = \col_j v j ord0).
      { apply matrixP.  unfold eqrel. intros. rewrite !mxE /=.
        assert ( y = ord0). { apply ord1. } rewrite H8. auto. }
      rewrite -H8. auto.
    - intros. specialize (H0 (@inord n i)).
      rewrite inord_val in H0.
      rewrite -Heql1 -Heql2. simpl. subst l1 l2. apply H0.
  + assert (@e_i_sparse n ty (inord i) A v r HA = [seq @e_i_sparse n ty i0 A v r HA | i0 <- enum 'I_n.+1]`_i).
    { rewrite seq_equiv nth_mkseq. nra. by rewrite size_map size_enum_ord in H1. }
    rewrite H7. apply /RleP.
    apply (@bigmaxr_ler _  _ [seq e_i_sparse i0 v HA | i0 <- enum 'I_n.+1] i).
    rewrite size_map size_enum_ord.
    rewrite size_map in H1.
    rewrite size_enum_ord in H1. auto.
Qed.

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
               * FT2R_abs (FT2R_mat v) (@widen_ord m n.+1 le_n_m j) ord0 = 
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
               FT2R_abs (FT2R_mat v) (widen_ord H0 j) ord0 = 
           \sum_(i0 < m)
               FT2R_abs (FT2R_mat A) (inord i)
                 (widen_ord le_n_m (widen_ord (leqnSn m) i0)) *
               FT2R_abs (FT2R_mat v)
                 (widen_ord le_n_m (widen_ord (leqnSn m) i0)) ord0).
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
                               FT2R_abs (FT2R_mat v)) i ord0)
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
                  FT2R_abs (FT2R_mat v) j ord0 = 
              \sum_(j < n.+1)
                 FT2R_abs (FT2R_mat A) (inord x)
                   (widen_ord (leqnn n.+1) j) *
                 FT2R_abs (FT2R_mat v)
                   (widen_ord (leqnn n.+1) j) ord0).
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
             FT2R_abs (FT2R_mat v)) i0 ord0))%Ri
      | i0 <- enum 'I_n.+1]`_i).
    * rewrite seq_equiv. rewrite nth_mkseq;
      last by rewrite size_map size_enum_ord in H.
      rewrite -RmultE. rewrite !mxE.
      pose proof (@sum_fold_mathcomp_equiv n ty n.+1 i (leqnn n.+1) A v).
      rewrite -H0.
      assert (\sum_j
                  FT2R_abs (FT2R_mat A) (inord i) j *
                  FT2R_abs (FT2R_mat v) j ord0 = 
              \sum_(j < n.+1)
                 FT2R_abs (FT2R_mat A) (inord i)
                   (widen_ord (leqnn n.+1) j) *
                 FT2R_abs (FT2R_mat v)
                   (widen_ord (leqnn n.+1) j) ord0).
      { apply eq_big. by []. intros.
        assert (widen_ord (leqnn n.+1) i0 = i0).
        { unfold widen_ord. apply val_inj. by simpl. }
        by rewrite H2.
      } rewrite -H1. apply Rle_refl.
   * apply /RleP.
     apply (@bigmaxr_ler _ 0%Re [seq (g ty n.+1 *
                 Rabs
                   ((FT2R_abs (FT2R_mat A) *m 
                     FT2R_abs (FT2R_mat v)) i0 ord0))%Ri
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
change
(mat_vec_mult_err_bnd A v <=
(matrix_inf_norm (FT2R_mat A) * vec_inf_norm (FT2R_mat v) * g ty n.+1 +
g1 ty n.+1 (n.+1 - 1))%R).


unfold mat_vec_mult_err_bnd.
unfold vec_inf_norm, matrix_inf_norm.
rewrite mulrC. rewrite [in X in (_ * X + _)]mulrC.
rewrite -bigmaxr_mulr.
+(* apply /RleP.*) rewrite -RplusE -RmultE.
  apply lemmas.bigmax_le.
  - by rewrite size_map size_enum_ord.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    unfold e_i. rewrite !length_veclist.
    apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * apply g_pos.
    * apply Rle_trans with
      [seq (bigmaxr 0%Re
           [seq Rabs (FT2R_mat v i1 ord0)
              | i1 <- enum 'I_n.+1] *
         row_sum (FT2R_mat A) i0)%Ri
      | i0 <- enum 'I_n.+1]`_i.
      ++ assert ([seq bigmaxr 0%Re
                    [seq Rabs (FT2R_mat v i1 ord0)
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
                                           [seq Rabs (FT2R_mat v i1 ord0)
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
         let l2 := vec_to_list_float n.+1 (\col_j v j ord0) in
         dotprod_r l1 l2) ) ->
  vec_inf_norm (FT2R_mat (A *f v) - (FT2R_mat A) *m (FT2R_mat v)) <=
  (matrix_inf_norm (FT2R_mat A) * vec_inf_norm (FT2R_mat v)) * g ty n.+1 +
   g1 ty n.+1 (n.+1 - 1).
Proof.
intros.
(*apply /RleP.*)
apply Rle_trans with (mat_vec_mult_err_bnd A v).
+ (*apply /RleP.*) by apply matrix_vec_mult_bound.
+ (*apply /RleP.*) apply matrix_err_bound_le_rel.
Qed.

End WITHNANS.

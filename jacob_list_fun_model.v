Require Import vcfloat.VCFloat.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct.

Require Import floatlib.
Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Require Import fma_floating_point_model.

Section WITH_NANS.

Context {NANS: Nans}.

Definition diagmatrix t := list (ftype t).

Definition invert_diagmatrix {t} (v: diagmatrix t) : diagmatrix t :=
   map (BDIV t (Zconst t 1)) v.

Definition diagmatrix_vector_mult {t}: diagmatrix t -> vector t -> vector t :=
  map2 (BMULT t).

Definition diagmatrix_matrix_mult {t} (v: diagmatrix t) (m: matrix t) : matrix t :=
  map2 (fun d => map (BMULT t d)) v m.
  
Definition diag_of_matrix {t: type} (m: matrix t) : diagmatrix t :=
  map (fun i => matrix_index m i i) (seq 0 (matrix_rows_nat m)).

Definition remove_diag {t} (m: matrix t) : matrix t :=
 matrix_by_index (matrix_rows_nat m) (matrix_rows_nat m)
  (fun i j => if Nat.eq_dec i j then Zconst t 0 else matrix_index m i j).

Definition matrix_of_diag {t} (d: diagmatrix t) : matrix t :=
 matrix_by_index (length d) (length d)
  (fun i j => if Nat.eq_dec i j then nth i d (Zconst t 0) else Zconst t 0).

Definition jacobi_iter {t: type} (A1: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult (invert_diagmatrix A1) (vector_sub b (matrix_vector_mult A2 x)).

Definition jacobi_residual {t: type} (A1: diagmatrix t) (A2: matrix t) (b: vector t) (x: vector t) : vector t :=
   diagmatrix_vector_mult A1 (vector_sub (jacobi_iter A1 A2 b x) x).


Definition going {t} (s acc: ftype t) := 
   andb (Binary.is_finite (fprec t) (femax t) s) (BCMP _ Lt false s acc).


Fixpoint iter_stop {t} {A} (norm2: A -> ftype t) (residual: A -> A) (f : A -> A) (n:nat) (acc: ftype t) (x:A) :=
 let y := f x in 
 let s := norm2 (residual x) in 
 match n with
 | O => (s, x)
 | S n' => if going s acc
                then iter_stop norm2 residual f n' acc y
                else (s,x)
  end.

Definition jacobi_n {t: type} (A: matrix t) (b: vector t) (x: vector t) (n: nat) : vector t :=
   let A1 := diag_of_matrix  A in 
   let A2 := remove_diag A in 
   Nat.iter n (jacobi_iter A1 A2 b) x.

Definition dist2 {t: type} (x y: vector t) := norm2 (vector_sub x y).

Definition jacobi {t: type} (A: matrix t) (b: vector t) (x: vector t) (acc: ftype t) (n: nat) :
         ftype t * vector t :=
   let A1 := diag_of_matrix  A in 
   let A2 := remove_diag A in 
   iter_stop norm2 (jacobi_residual A1 A2 b) (jacobi_iter A1 A2 b) (Nat.pred n) acc x.

Definition old_jacobi_iter {t: type} x0 b (A1: diagmatrix t) (A2: matrix t) : vector t :=
  let S_J :=  opp_matrix (diagmatrix_matrix_mult A1 A2) in
  let f_J := diagmatrix_vector_mult A1 b in
  vector_add (matrix_vector_mult S_J x0) f_J.

Require Import fma_real_func_model fma_floating_point_model.

Require Import inf_norm_properties common.

Search "ceil".


Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  vec_inf_norm (FT2R_mat x_k - x).



Definition jacobi_preconditions {t: type}
  (A: matrix t) (b: vector t) (accuracy: ftype t) (k: nat) : Prop :=
  (* some property of A,b,accuracy holds such that 
    jacobi_n will indeed converge within k iterations to this accuracy, 
   without ever overflowing *)
  let n := (length A).-1 in
  let A' := @matrix_inj _ A n.+1 n.+1 in
  let b' := @vector_inj _ b n.+1 in
  let A_real := FT2R_mat A' in
  let b_real := FT2R_mat b' in
  
  let x:= mulmx (A_real^-1) b_real in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real)) in
  let delta := default_rel t in
  let rho := ((((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * (1 + delta) + delta) * R +
                (((1 + g t n.+1) * (1 + delta) *
                  g t n.+1 + delta * (1 + g t n.+1) +
                  g t n.+1) * default_abs t +
                 default_abs t) *
                matrix_inf_norm (A2_J_real A_real) + R) in
   let d_mag := ((g t n.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs t) *
                     vec_inf_norm b_real) +
                    (1 + g t n.+1) * g1 t n.+1 (n.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs t) +
                    g1 t n.+1 (n.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs t) * vec_inf_norm b_real +
                    ((((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * (1 + delta) + delta) * R +
                     (((1 + g t n.+1) * (1 + delta) *
                       g t n.+1 + delta * (1 + g t n.+1) +
                       g t n.+1) * default_abs t +
                      default_abs t) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real)) in
  let x0 := (repeat  (Zconst t 0) (length b)) in
  let x0' := @vector_inj _ x0 n.+1 in
  
  (** dimension of A is positive **)
  (0 < length A)%coq_nat /\
  (** Finiteness of A **)
  (forall i j, Binary.is_finite _ _ (A' i j) = true) /\
  (** x <> 0 **)
  x != 0 /\
  (** constant for the contraction mapping **)
  (rho < 1)%Re /\
  (** Invertibility of A **)
  A_real \in unitmx /\
  (** Finiteness of the inverse of diagonal elements of A **)
  (forall i : 'I_n.+1,
    Binary.is_finite (fprec t) (femax t)
      (BDIV t (Zconst t 1) (A' i i)) = true) /\
  (** Finiteness of solution vector at each iteration **)
  (forall k:nat, 
      forall i, Binary.is_finite _ _ ((X_m_jacobi k x0' b' A') i ord0) = true) /\
  (** Constraint on Gamma **)
  (Rsqr (g1 t n.+1 (n.+1 - 1)) < FT2R (accuracy))%Re /\
  (** Gamma is finite **)
  Binary.is_finite _ _ accuracy = true /\
  (** constraint on k **)
  (k > Z.to_N (Zceil (ln (((1- rho) * sqrt (INR n.+1) * (1 + g t n.+1) * (f_error 0 b' x0' x A' - d_mag / (1-rho))) /
                          (sqrt (FT2R (accuracy)  - g1 t n.+1 (n.+1 - 1)))) /
                      ln (1 / rho))))%coq_nat.
       


Lemma jacobi_iteration_bound_monotone:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k k': nat),
   (k <= k')%nat ->
   jacobi_preconditions A b acc k ->
   jacobi_preconditions A b acc k'.
Proof. 
Admitted.

From Flocq Require Import Binary.

(** remove this later. Also in the fma_jacobi_forward_error file **)
Lemma bfma_overflow_implies {t : type}: 
  forall x y z, 
  Binary.is_finite _ _ (@BFMA _ t x y z) = true ->
  Binary.is_finite _ _ x = true /\
  Binary.is_finite _ _ y = true /\
  Binary.is_finite _ _ z = true.
Proof.
intros.
destruct x, y, z; (unfold BFMA, BINOP, Bfma, is_finite in *; simpl in *; auto;
  try destruct (eqb s (~~ s0)); simpl in * ;auto; try by []; 
  try unfold is_finite in H1; simpl in *; auto);
  by destruct s,s0,s1;simpl in *; auto.
Qed.


Lemma jacobi_iteration_bound_corollaries:
  forall {t: type}  (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
   matrix_cols A (matrix_rows A) /\
   Forall (Forall finite) A /\
   Forall finite (invert_diagmatrix (diag_of_matrix A)) /\
   Forall finite b /\ finite acc.
Proof. 
intros. unfold jacobi_preconditions in H.
destruct H as [Hla [HfA [Hxneq0 [Hrho [HAinv [Hinvf [Hsolf [HcG1 [HcG2 Hk]]]]]]]]].
repeat split.
+ unfold matrix_cols, matrix_rows. simpl.
  admit.
+ apply Forall_nth. intros.
  apply Forall_nth. intros.
  specialize (HfA (@inord (length A).-1 i) (@inord (length A).-1 i0)).
  apply finite_is_finite. rewrite !mxE in HfA.
  rewrite !inordK in HfA.
  - admit.
  - rewrite prednK. by apply /ssrnat.ltP. by apply /ssrnat.ltP.
  - rewrite prednK.
    assert (length (nth i A d) = length A).
    { admit . } admit.
   by apply /ssrnat.ltP.
+ apply Forall_nth. intros.
  unfold invert_diagmatrix. 
  rewrite (nth_map_inrange (Zconst t 0)).
  - specialize (Hinvf (@inord (length A).-1 i)).
    rewrite !mxE in Hinvf. unfold diag_of_matrix.
    rewrite nth_map_seq.
    * unfold matrix_index. rewrite inordK in Hinvf.
      ++ apply finite_is_finite. apply Hinvf.
      ++ rewrite prednK. rewrite !map_length seq_length /matrix_rows_nat in H.
         by apply /ssrnat.ltP. by apply /ssrnat.ltP.
    * unfold matrix_rows_nat. 
      by rewrite !map_length seq_length /matrix_rows_nat in H.
  - rewrite !map_length seq_length.
    by rewrite !map_length seq_length in H.
+ specialize (Hsolf k.+1).
  apply Forall_nth. intros.
  specialize (Hsolf (@inord (length A).-1 i)).
  apply finite_is_finite.  
  remember (length A).-1 as m. clear Hk HcG2 HcG1.
  rewrite mxE in Hsolf.
  rewrite !nth_vec_to_list_float in Hsolf.
  rewrite inord_val in Hsolf. 
  apply bmult_overflow_implies in Hsolf.
  


Print matrix_inj.
  unfold X_m_jacobi,vector_inj, matrix_inj,jacobi_iter  in Hsolf. rewrite !mxE in Hsolf.



 admit.
+ by apply finite_is_finite.
Admitted.

Lemma jacobi_iteration_bound {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   jacobi_preconditions A b acc k ->
   let acc2 := BMULT t acc acc in
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
   finite acc2 /\ 
   exists j,
    (j <= k)%nat /\
    let y :=  jacobi_n A b x0 j in
    let r2 := norm2 (resid y) in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) /\
    BCMP t Lt false (norm2 (resid (jacobi_n A b x0 j))) acc2 = false.
Proof.
intros.
contradiction H.
Qed.

End WITH_NANS.

Module Experiment.
(***************** Some sanity checks about diag_of_matrix and matrix_of_diag ***)

(* This turned out to be much lengthier than I expected.    I had to devel
  a whole theory of extensional matrices.  It started to feel like I was
  recapitulating all of MathComp.  My conclusion
  is that all of these lemmas should be done at the MathComp level
  and not at the list-of-lists level.  None of these lemmas are needed
  by the VST proofs, for example. *)

Section WITH_NANS.
Context {NANS: Nans}.

Local Ltac inv H := inversion H; clear H; subst.

Lemma length_diag_of_matrix: forall {t} (m: matrix t),
   matrix_cols_nat m (matrix_rows_nat m) ->
   length (diag_of_matrix m) = matrix_rows_nat m.
Proof.
 intros.
 unfold diag_of_matrix.
 rewrite map_length. rewrite seq_length. auto.
Qed.

Lemma rows_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_rows_nat (matrix_of_diag v) = length v.
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_rows.
Qed.

Lemma cols_matrix_of_diag: forall {t} (v: diagmatrix t),
   matrix_cols_nat (matrix_of_diag v) (length v).
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_cols.
Qed.

Lemma diag_of_matrix_of_diag:
  forall {t} (d: diagmatrix t),
  diag_of_matrix (matrix_of_diag d) = d.
Proof.
intros.
unfold diag_of_matrix, matrix_of_diag.
apply (all_nth_eq (Zconst t 0));
rewrite map_length, seq_length, matrix_by_index_rows. auto.
intros.
set (f := fun _ => _).
transitivity (nth i (map f (seq 0 (length d))) (f (length d))).
f_equal. subst f. simpl.
unfold matrix_by_index.
unfold matrix_index.
rewrite nth_overflow; auto.
rewrite nth_overflow; auto.
simpl; lia.
rewrite map_length. rewrite seq_length. lia.
rewrite map_nth.
rewrite seq_nth by auto.
simpl.
subst f. simpl.
rewrite matrix_by_index_index by auto.
destruct (Nat.eq_dec i); try contradiction; auto.
Qed.

Lemma Forall_diag_of_matrix {t}: forall (P: ftype t -> Prop) (m: matrix t),
 matrix_cols_nat m (matrix_rows_nat m) ->
 Forall (Forall P) m -> Forall P (diag_of_matrix m).
Proof.
intros.
apply Forall_map.
apply Forall_seq.
intros.
red in H.
unfold matrix_index.
unfold matrix_rows_nat in *.
rewrite Forall_nth in H0.
specialize (H0 i nil ltac:(lia)).
rewrite Forall_nth in H0.
apply (H0 i (Zconst t 0)).
rewrite Forall_forall in H.
specialize (H (nth i m nil)).
rewrite H. lia.
apply nth_In. lia.
Qed.

Lemma matrix_binop_by_index:
  forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->  
  Forall2 (Forall2 feq) (map2 (map2 op) m1 m2)
  (matrix_by_index (matrix_rows_nat m1) cols (fun i j => op (matrix_index m1 i j) (matrix_index m2 i j))).
Proof.
intros.
apply (matrix_extensionality _ _ cols); auto.
-
rewrite matrix_by_index_rows.
clear H0 H1.
revert m2 H; induction m1; destruct m2; simpl; intros; inv H; auto.
f_equal; eauto.
-
clear H.
revert m2 H1; induction H0; destruct m2; simpl; intros; constructor.
inv H1.
unfold uncurry, map2.
rewrite map_length.
rewrite combine_length.
rewrite H4. apply  Nat.min_id.
apply IHForall.
inv H1; auto.
-
apply matrix_by_index_cols.
-
intros.
 assert (matrix_rows_nat (map2 (map2 op) m1 m2) = matrix_rows_nat m1). {
  clear - H. revert m2 H; induction m1; destruct m2; simpl; intros; inv H; f_equal; eauto.
 }
 rewrite H4 in *.
 rewrite matrix_by_index_index; auto.
 revert m2 H H1 i H2 H4; induction m1; destruct m2; simpl; intros; inv H.
 + lia.
 + destruct i; simpl.
   * clear IHm1.
       unfold matrix_index.
       unfold map2 at 1. unfold combine. simpl.
       unfold map2.
       inv H0. inv H1.
       clear - H3 H5.
       revert j H3 l H5; induction a; destruct j,l; simpl; intros; inv H5; auto.
       inv H3. inv H3.
       simpl in H3.
       eapply IHa; eauto. lia.
   *  unfold matrix_add.
     change (map2 (map2 ?f) (a::m1) (l::m2)) with (map2 f a l :: map2 (map2 f) m1 m2).
      repeat change (matrix_index (?x::?y) (S i) j) with (matrix_index y i j).
     inv H1. inv H0.
     eapply IHm1; eauto. lia.
Qed.

Lemma matrix_rows_nat_remove_diag: forall {t} (m: matrix t),
    matrix_cols_nat m (matrix_rows_nat m) ->
  matrix_rows_nat m = matrix_rows_nat (remove_diag m).
Proof.
 intros.
 symmetry;
 apply matrix_by_index_rows.
Qed.

Lemma matrix_rows_nat_matrix_binop:
 forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t),
 matrix_rows_nat m1 = matrix_rows_nat m2 ->
 matrix_rows_nat (map2 (map2 op) m1 m2) = matrix_rows_nat m1.
Proof.
intros.
unfold matrix_rows_nat in *.
unfold map2.
rewrite map_length.
rewrite combine_length.
lia.
Qed.

Lemma matrix_cols_nat_matrix_binop:
 forall {t} (op: ftype t -> ftype t -> ftype t) (m1 m2: matrix t) cols,
 matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
 matrix_cols_nat (map2 (map2 op) m1 m2) cols.
Proof.
induction m1; destruct m2; simpl; intros.
constructor.
constructor.
constructor.
inv H.
inv H0.
unfold map2 at 1.
unfold combine; fold (combine m1 m2).
simpl.
constructor; auto.
unfold map2. rewrite map_length.
rewrite combine_length; lia.
apply IHm1; auto.
Qed.

Lemma matrix_cols_nat_matrix_unop:
 forall {t} (op: ftype t -> ftype t) (m: matrix t) cols,
 matrix_cols_nat m cols ->
 matrix_cols_nat (map (map op) m) cols.
Proof.
induction 1.
constructor.
constructor.
rewrite map_length. auto.
apply IHForall.
Qed.

Lemma matrix_cols_nat_remove_diag: forall {t} (m: matrix t),
    matrix_cols_nat m (matrix_rows_nat m) ->
  matrix_cols_nat (remove_diag m) (matrix_rows_nat m).
Proof.
intros.
 apply matrix_by_index_cols.
Qed.

Local Open Scope nat.

Lemma matrix_index_diag:
 forall {t} (d: diagmatrix t) i j,
   i < length d -> j < length d ->
   matrix_index (matrix_of_diag d) i j =
    if (Nat.eq_dec i j) then nth i d (Zconst t 0) else Zconst t 0.
Proof.
intros.
unfold matrix_of_diag.
apply matrix_by_index_index; auto.
Qed.

Lemma binop_matrix_index:
 forall {t} (f: ftype t -> ftype t -> ftype t)
  (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  forall i j, i < matrix_rows_nat m1 -> j < cols ->
  matrix_index (map2 (map2 f) m1 m2) i j =
  f (matrix_index m1 i j) (matrix_index m2 i j).
Proof.
unfold matrix_rows_nat.
induction m1; destruct m2; simpl; intros; inv H.
simpl in H2. lia.
inv H0.
inv H1.
destruct i.
unfold matrix_index. simpl.
unfold map2.
clear - H3 H4.
revert j H3 l H4; induction a; destruct l,j; simpl; intros; inv H4; auto.
simpl in H3; lia. simpl in H3; lia.
simpl in H3. apply IHa; auto. lia.
apply (IHm1 m2 (length a)); auto.
lia.
Qed.

Lemma remove_plus_diag: forall {t} (m: matrix t),
   matrix_cols_nat m (matrix_rows_nat m) ->
   Forall (Forall finite) m ->
   Forall2 (Forall2 feq) (matrix_add  (matrix_of_diag (diag_of_matrix m)) (remove_diag m)) m.
Proof.
intros.
apply matrix_extensionality with (cols := matrix_rows_nat m); auto.
unfold matrix_add.
rewrite matrix_rows_nat_matrix_binop.
unfold matrix_of_diag.
rewrite matrix_by_index_rows.
apply length_diag_of_matrix; auto.
unfold matrix_of_diag.
rewrite matrix_by_index_rows.
rewrite length_diag_of_matrix; auto.
unfold remove_diag.
rewrite matrix_by_index_rows; auto.
apply matrix_cols_nat_matrix_binop.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
apply length_diag_of_matrix; auto.
apply matrix_by_index_cols.
unfold matrix_add at 1.
rewrite matrix_rows_nat_matrix_binop.
2:{ unfold matrix_of_diag. rewrite matrix_by_index_rows.
    unfold remove_diag.  rewrite matrix_by_index_rows.
    apply length_diag_of_matrix; auto.
}
unfold matrix_of_diag at 1.
rewrite matrix_by_index_rows; auto.
rewrite length_diag_of_matrix; auto.
intros.
unfold matrix_add.
rewrite binop_matrix_index with (cols := matrix_rows_nat m); auto.
unfold matrix_of_diag, remove_diag.
rewrite !matrix_by_index_index; auto.
destruct (Nat.eq_dec i j).
unfold diag_of_matrix.
rewrite nth_map_seq; auto.
subst j.
apply BPLUS_0_r.
eapply matrix_index_prop; eauto.
apply BPLUS_0_l.
eapply matrix_index_prop; eauto.
rewrite length_diag_of_matrix; auto.
rewrite length_diag_of_matrix; auto.
unfold matrix_of_diag, remove_diag.
rewrite !matrix_by_index_rows; auto.
apply length_diag_of_matrix; auto.
replace (matrix_rows_nat m) with (length (diag_of_matrix m)).
apply matrix_by_index_cols.
apply length_diag_of_matrix; auto.
apply matrix_by_index_cols.
unfold matrix_of_diag.
rewrite matrix_by_index_rows; auto.
rewrite length_diag_of_matrix; auto.
Qed.
End WITH_NANS.
End Experiment.


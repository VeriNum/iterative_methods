Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
(*Require Import vcfloat.FPCompCert.*)
(*Require Import VSTlib.spec_math.*)

Set Bullet Behavior "Strict Subproofs".

Close Scope R.
Open Scope logic.

Lemma Zlength_jacobi_iter: 
  forall {NAN: Nans} {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_iter A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_iter, diagmatrix_vector_mult,
        vector_sub, map2, invert_diagmatrix.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite !Zlength_map.
      rewrite Zlength_combine.
      unfold matrix_vector_mult.
      rewrite Zlength_map. unfold matrix_rows in *. lia.
Qed.

Lemma Znth_jacobi_iter {NAN: Nans}{t}:
  forall i A1 A2 (b x: vector t) (y: ftype t),
  Zlength A1 = matrix_rows A2 -> 
  Zlength b = matrix_rows A2 -> 
  Zlength x = matrix_rows A2 -> 
  0 <= i < matrix_rows A2 ->
  feq y (dotprod (Znth i A2) x) ->
  feq (Znth i (jacobi_iter A1 A2 b x))
     (BMULT t (BDIV t (Zconst t 1) (Znth i A1))
         (BMINUS t (Znth i b) y)).
Proof.
intros. unfold matrix_rows in *.
 unfold jacobi_iter, diagmatrix_vector_mult, vector_sub, map2,
   matrix_vector_mult, invert_diagmatrix.
  rewrite Znth_map.
2:rewrite Zlength_combine, !Zlength_map,
     Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite !Zlength_map, Zlength_combine, Zlength_map; lia.
rewrite Znth_map by lia.
rewrite Znth_map
 by (rewrite Zlength_combine, Zlength_map; lia).
rewrite Znth_combine by (rewrite Zlength_map; lia).
rewrite Znth_map by lia.
unfold uncurry.
apply BMULT_congr; auto.
apply BMINUS_congr; auto.
symmetry.
auto.
Qed.

Lemma matrix_cols_remove_diag:
  forall {t} (m: matrix t), matrix_cols m (matrix_rows m) ->
    matrix_cols (remove_diag m) (matrix_rows m).
Proof.
 unfold remove_diag. intros.
 rewrite <- Zmatrix_rows_nat.
 rewrite <- Zmatrix_cols_nat.
 apply matrix_by_index_cols.
Qed.

Lemma finite_remove_diag:
 forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   Forall (Forall finite) m ->
   Forall (Forall finite) (remove_diag m).
Proof.
intros.
 apply matrix_by_index_prop.
 constructor.
 intros.
 if_tac. constructor.
 eapply matrix_index_prop; eauto.
 rewrite <- Zmatrix_rows_nat in H.
 rewrite <- Zmatrix_cols_nat in H.
 auto.
Qed.

Lemma matrix_rows_remove_diag: forall {t} (m: matrix t), 
     matrix_rows (remove_diag m) = matrix_rows m.
Proof.
intros.
rewrite <- !Zmatrix_rows_nat.
f_equal.
apply matrix_by_index_rows.
Qed.

#[export] Hint Rewrite @Zmatrix_rows_nat : sublist rep_lia.

Add Parametric Morphism  {NAN: Nans}{t}: (@diagmatrix_vector_mult _ t)
  with signature Forall2 feq ==> Forall2 feq ==> Forall2 feq 
 as diagmatrix_vector_mult_mor.
Proof.
intros.
unfold diagmatrix_vector_mult.
apply Forall2_map.
revert x0 y0 H0; induction H; simpl; intros; auto.
destruct x0,y0; inv H1; simpl; intros; auto.
constructor; auto.
unfold uncurry.
apply BMULT_congr; auto.
Qed.

Add Parametric Morphism  {NAN: Nans}{t}:  (@jacobi_iter _ t)
 with signature Forall2 strict_feq ==> Forall2 (Forall2 feq) 
       ==> Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as jacobi_iter_mor.
Proof.
unfold jacobi_iter; intros.
apply diagmatrix_vector_mult_mor.
unfold invert_diagmatrix.
apply Forall2_map.
clear - H.
eapply Forall2_impl; try apply H; intros.
apply BDIV_mor; auto.
apply vector_sub_mor; auto.
apply matrix_vector_mult_mor; auto.
Qed.

Add Parametric Morphism  {NAN: Nans}{t}:  (@jacobi_residual _ t)
 with signature Forall2 strict_feq ==> Forall2 (Forall2 feq) 
       ==> Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as jacobi_residual_mor.
Proof.
unfold jacobi_residual; intros.
apply diagmatrix_vector_mult_mor; auto.
eapply Forall2_impl. apply subrelation_strict_feq. auto.
apply vector_sub_mor; auto.
apply jacobi_iter_mor; auto.
Qed.

Lemma finite_dist2_e2: 
  forall  {NAN: Nans}{t} (x y: vector t), 
  Zlength x = Zlength y ->
  finite (dist2 x y) -> 
  Forall finite y.
Proof.
  intros.
   unfold dist2.
   apply finite_norm2_e in H0.
   rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
   revert y H H0; induction x; destruct y; simpl; intros; 
     inv H; inv H0; constructor; auto.
   clear - H3.
   rewrite finite_is_finite in H3.
   destruct a, f; inv H3; try constructor; auto.
   destruct s,s0; inv H0.
Qed.

Lemma Zlength_diag_of_matrix: 
    forall {t} (A: matrix t), Zlength (diag_of_matrix A) = matrix_rows A.
Proof.
intros.
unfold diag_of_matrix.
rewrite Zlength_map.
unfold matrix_rows, matrix_rows_nat.
rewrite !Zlength_correct, seq_length.
auto.
Qed.

Add Parametric Morphism  {NAN: Nans}{t: type} : (@dist2 _ t)
  with signature Forall2 feq ==> Forall2 feq ==> feq
  as dist2_mor.
Proof.
intros.
unfold dist2.
rewrite H, H0. auto.
Qed.

Add Parametric Morphism {t} : (@going t)
  with signature feq ==> strict_feq ==> eq
  as going_mor.
Proof.
 intros.
destruct x,y; inv H; simpl; auto.
destruct x0,y0; inv H0; simpl; auto.
destruct H2; subst; auto.
proof_irr.
destruct x0,y0; inv H0;  auto.
destruct H1; subst; auto.
Qed.

Ltac iter_stop_S :=
   change (@iter_stop ?t _  ?norm2 ?res ?f (S ?n) ?acc ?x) with
        (if going (norm2 (res x)) acc
           then iter_stop norm2 res f n acc (f x) else (norm2 (res x), x)).

Lemma iter_stop_congr {t}:
 forall (norm2: vector t -> ftype t) residual f acc (FINacc: finite acc) n (z z': vector t),
   Proper (Forall2 feq ==> feq) norm2 ->
   Proper (Forall2 feq ==> Forall2 feq) residual ->
   Proper (Forall2 feq ==> Forall2 feq) f ->
 Forall2 feq z z' ->
 Forall2 feq (snd (iter_stop norm2 residual f n acc z))
    (snd (iter_stop norm2 residual f n acc z')).
Proof.
induction n; simpl; intros.
auto.
assert (feq (norm2 (residual z)) (norm2 (residual z'))).
apply H; apply H0; auto.
unfold going.
replace  (Binary.is_finite (fprec t) (femax t) (norm2 (residual z')))
  with (Binary.is_finite (fprec t) (femax t) (norm2 (residual z)))
  by (rewrite H3; auto).
destruct (Binary.is_finite _ _ _) eqn:?H.
simpl.
apply finite_is_finite in H4.
replace (BCMP t Gt true (norm2 (residual z')) acc) 
     with (BCMP t Gt true (norm2 (residual z)) acc)
  by (apply BCMP_mor; auto; apply strict_feq_i1; auto).
destruct (BCMP _ _ _ _ _).
apply IHn; auto.
simpl; auto.
simpl.
auto.
Qed.

Fixpoint iter_stop_n {t} {A} (norm2: A -> ftype t) (residual: A -> A) (f : A -> A) (n: nat) (acc: ftype t) (x: A) :=
   match n with
 | O => Some x
 | S n' => if going (norm2 (residual x)) acc
                then iter_stop_n norm2 residual f n' acc (f x)
                else None
  end.

Lemma iter_stop_n_S:
  forall {t}{A} (norm2: A -> ftype t) (resid f: A -> A) (n: nat) 
            (acc: ftype t) x v,
  iter_stop_n norm2 resid f n acc x = Some v ->
  going (norm2 (resid v)) acc = true ->
  iter_stop_n norm2 resid f (S n) acc x = Some (f v).
Proof.
intros.
revert x v H H0; induction n; simpl; intros.
inv H. rewrite H0. auto.
destruct (going (norm2 (resid x)) acc) eqn:J.
apply IHn in H; auto.
inv H.
Qed.


Lemma iter_stop_n_lem1:
  forall t A norm2 (residual: A -> A) (f: A->A) (acc: ftype t) k n x y, 
   iter_stop_n norm2 residual f n acc x = Some y ->
   going (norm2 (residual y)) acc = false ->
   iter_stop norm2 residual f (n+k) acc x = (norm2 (residual y), y).
Proof.
induction n; simpl; intros; auto.
inv H; auto.
destruct k; auto. simpl. fold (going (norm2 (residual y)) acc).  rewrite H0. auto.
 fold (going (norm2 (residual x)) acc). 
destruct (going (norm2 (residual x)) acc) eqn:J; try discriminate.
apply IHn; auto.
Qed.  

Lemma iter_stop_n_lem2: 
  forall t A norm2 residual (f: A->A) (acc: ftype t) n x y, 
   iter_stop_n norm2 residual f n acc x = Some y ->
   going (norm2 (residual y)) acc = true ->
   iter_stop norm2 residual f n acc x = (norm2 (residual y), y).
Proof.
induction n; simpl; intros; auto.
inv H; auto.
fold (going (norm2 (residual x)) acc). 
destruct (going (norm2 (residual x)) acc) eqn:J; try discriminate.
apply IHn; auto.
Qed.  

Lemma iter_stop_n_Zlength:
 forall  {NAN: Nans}{t} residual f N n acc x v
    (LENf: forall x, Zlength x = N -> Zlength (f x) = Zlength x)
    (CONGR_f: forall x x' : list (ftype t),
          Zlength x = N ->
          Forall2 strict_feq x x' -> Forall2 feq (f x) (f x'))
    (FINRES: forall x, Zlength x = N -> Forall finite (residual x) -> Forall finite (f x)),
    Zlength x = N -> Forall finite x ->
    iter_stop_n norm2 residual f n acc x = Some v ->
    Zlength v = N.
Proof.
intros.
revert x H H0 H1; induction n; simpl; intros.
inv H1; auto.
destruct (going _ _) eqn:?H in H1; try discriminate.
unfold going in H2.
rewrite andb_true_iff in H2. destruct H2.
apply finite_is_finite in H2.
apply finite_norm2_e in H2.
apply IHn in H1; auto.
rewrite LENf; auto.
Qed.

Lemma finres_jacobi  {NAN: Nans}{t}: forall A1 A2 b (x: vector t),
   Zlength A1 = Zlength x ->
   Zlength (jacobi_iter A1 A2 b x) = Zlength x ->
   Forall finite (jacobi_residual A1 A2 b x) ->
   Forall finite (jacobi_iter A1 A2 b x).
Proof.
intros.
unfold jacobi_residual in *.
set (y := jacobi_iter _ _ _ _) in *. clearbody y.
unfold diagmatrix_vector_mult, vector_sub in H1.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H, H0.
revert A1 y H H0 H1; induction x; destruct A1,y; intros; inv H; inv H0; inv H1; 
  constructor; auto.
-
clear - H4.
assert (finite (BMINUS t f0 a))
  by (destruct f, (BMINUS t f0 a); try contradiction H4; simpl; auto).
clear H4.
destruct f0,a; try destruct s; try destruct s0; try contradiction H; simpl; auto.
-
apply (IHx _ _ H3 H2 H5).
Qed.

Lemma Zlength_jacobi_residual: 
  forall {NAN: Nans} {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_residual A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_residual, diagmatrix_vector_mult,
        vector_sub, map2.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite !Zlength_map.
      rewrite Zlength_combine.
      rewrite Zlength_jacobi_iter by auto. lia.
Qed.

Lemma diag_of_matrix_prop:
  forall {t} (P: ftype t -> Prop) (A: matrix t), 
      matrix_cols A (matrix_rows A) ->
      Forall (Forall P) A -> Forall P (diag_of_matrix A).
Proof.
intros.
unfold diag_of_matrix.
apply Forall_map, Forall_seq.
intros. red.
assert (0 <= matrix_rows A).
unfold matrix_rows in *. rep_lia.
rewrite <- Z2Nat.id in H by lia.
apply Zmatrix_cols_nat in H.
eapply matrix_index_prop. eauto. auto. lia.
rewrite <- Zmatrix_rows_nat. lia.
Qed.


Local Open Scope nat.

Lemma exists_nat_dec:
  forall (P: nat -> Prop),
  (forall n, Decidable.decidable (P n)) ->
   forall n, Decidable.decidable (exists k, k<n /\ P k).
Proof.
  induction n.
  right. intros [? [? ?]]; lia.
  destruct (H n). left; exists n; split; auto.
  destruct IHn.
  destruct H1 as [k [? ?]].
  left; exists k; repeat split; auto.
  right. intros [k [? ?]]. destruct (lt_dec k n).
  apply H1; exists k; split; auto.
  assert (k=n) by lia. subst; contradiction.
Qed.

Lemma first_occurrence: forall (P: nat -> Prop),
  (forall n, Decidable.decidable (P n)) ->
  forall n, 
   P n -> exists k, k <= n /\ P k /\ forall j, j<k -> ~P j.
Proof.  (* this proof seems a bit more clumsy than necessary *)
intros.
set (b := n).
assert (exists n, n<=b /\ P n) by eauto.
clearbody b. clear H0 n. 
revert H1; induction b; intros [n [? ?]].
-
exists n; repeat split; auto. intros; lia.
-
destruct (Nat.eq_dec n (S b)).
+ subst n.
destruct (exists_nat_dec _ H (S b)) as [[k [? ?]]|].
destruct (IHb ltac:(exists k; split; [lia | auto])) as [k' [? [? ?]]].
exists k'; repeat split; auto.
exists (S b); repeat split; auto. 
intros.
contradict H2. exists j; split; auto.
+
assert (n <= b) by lia. clear n0 H0.
destruct (IHb ltac:(exists n; split; [lia | auto])) as [k [? [? ?]]].
exists k; repeat split; auto.
Qed.

Lemma min_iter: 
  forall {A} (f: A -> A) (P: A -> Prop) (DECP: forall x, Decidable.decidable (P x)) (x: A) (k: nat),
  P (Nat.iter k f x) ->
  exists j, j <= k /\ P (Nat.iter j f x) /\ forall i, i<j -> ~P (Nat.iter i f x).
Proof.
intros.
apply (first_occurrence (fun k => P (Nat.iter k f x)) ltac:(intros; apply DECP) k H).
Qed.

Lemma iter_swap: forall {A} (f: A-> A) i x,
  Nat.iter i f (f x) = f (Nat.iter i f x).
Proof.
induction i; simpl; intros; f_equal; auto.
Qed.

Lemma jacobi_n_jacobi {NAN: Nans} {t: type}:
  forall A b acc k maxiter, 
   jacobi_iteration_bound A b acc k ->
   (k <= maxiter)%nat ->
  let acc2 := BMULT t acc acc in
  let x0 := (repeat  (Zconst t 0) (length b)) in
  exists j,
   (j<=k)%nat /\
   let '(r2,xj) := jacobi A b x0 acc2 (S maxiter) in
   r2 = norm2 (jacobi_residual (diag_of_matrix A) (remove_diag A) b xj) /\
   xj = jacobi_n A b x0 j.
Proof.
intros.
apply jacobi_iteration_bound_correct in H.
destruct H as [FINacc2 [j [? [? [? ?]]]]].
unfold jacobi.
fold x0 in H2, H3.
set (resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b) in *.
unfold jacobi_n in *.
set (f := jacobi_iter _ _ _) in *.
simpl pred.
fold acc2 in FINacc2,H1,H3.
clearbody acc2. clear acc.
clearbody f. clearbody resid.
clearbody x0.
set (P x := BCMP t Gt true (norm2 (resid x)) acc2 = false).
assert (forall x, Decidable.decidable (P x)).
clear.
intros. subst P. simpl. destruct (BCMP _ _ _ _ _); [right|left]; auto.
destruct (min_iter f P H4 x0 j) as [i [? [? ?]]].
apply H3.
exists i; split; auto. lia.
assert (i <= maxiter) by lia.
clear k H H0.
assert (forall i', i' <= i -> finite (norm2 (resid (Nat.iter i' f x0)))).
intros; apply H2; lia.
clear j H5 H2 H3.
clear H4. subst P. simpl in *.
replace maxiter with (i + (maxiter-i)) by lia.
forget (maxiter-i) as k.
clear H8 maxiter.
rewrite (iter_stop_n_lem1 _ _ norm2 resid f acc2 k i x0
  (Nat.iter i f x0)).
split; auto.
2: unfold going; rewrite H6, andb_false_iff; auto.
revert x0 H6 H H7; induction i; simpl; intros; auto.
specialize (IHi (f x0)).
rewrite IHi.
specialize (H7 0 ltac:(lia)).
apply not_false_is_true in H7.
simpl in H7.
unfold going.
rewrite H7.
specialize (H 0 ltac:(lia)). 
apply finite_is_finite in H. simpl in H.
rewrite H.
simpl.
f_equal.
apply iter_swap.
rewrite iter_swap; auto.
intros.
rewrite iter_swap.
 apply (H (S i')). lia.
intros.
rewrite iter_swap.
apply (H7 (S i0)). lia.
Qed.


Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model spec_sparse spec_jacobi.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import VSTlib.spec_malloc.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:Ctypes.type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Gprog: funspecs := surely_malloc_spec :: JacobiASI ++ SparseASI ++ MathASI ++ MallocASI.

Lemma matrix_by_index_prop:
 forall {t} (f: nat -> nat -> ftype t) (P: ftype t -> Prop) rows cols,
  P (Zconst t 0) ->
  (forall i j, (i < rows)%nat -> (j < cols)%nat -> P (f i j)) ->
  Forall (Forall P) (matrix_by_index rows cols f).
Proof.
intros.
unfold matrix_by_index.
apply Forall_nth; intros.
rewrite map_length, seq_length in H1.
rewrite nth_map_seq by auto.
apply Forall_nth; intros.
rewrite map_length, seq_length in H2.
rewrite nth_map_seq by auto.
apply H0; auto.
Qed.

Lemma Zmatrix_cols_nat: 
 forall {t} (m: matrix t) cols,
  matrix_cols_nat m cols  <-> matrix_cols m (Z.of_nat cols).
Proof.
induction m; simpl; intros; split; intro; inv H; constructor; auto.
apply Zlength_correct.
clear - H3.
induction H3; constructor; auto. rewrite <- H; apply Zlength_correct.
rewrite Zlength_correct in H2. lia.
clear - H3.
induction H3; constructor; auto. rewrite Zlength_correct in H; lia.
Qed.

Lemma Zlength_seq: forall lo n, Zlength (seq lo n) = Z.of_nat n.
Proof.
intros. rewrite Zlength_correct. f_equal. apply seq_length.
Qed.
#[export] Hint Rewrite Zlength_seq : sublist rep_lia.

Lemma Zmatrix_rows_nat: forall {t} (m: matrix t), Z.of_nat (matrix_rows_nat m) = matrix_rows m.
Proof.
unfold matrix_rows.
induction m; simpl; auto. list_solve.
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

Definition first_loop : statement.
let c := constr:(f_jacobi2) in
let c := eval red in c in 
match c with context [Ssequence (Sset _i ?e) ?s] =>
 exact (Ssequence (Sset _i e ) s)
end.
Defined.

Definition second_loop : statement.
let c := constr:(f_jacobi2) in
let c := eval red in c in 
match c with context [Sloop ?a ?b] => match a with context [Sset _maxiter] => idtac end;
 exact (Sloop a b)
end.
Defined.

Lemma jacobi2_first_loop: forall {Espec : OracleKind}
  (sh1 : share) gv acc maxiter
  (A : matrix Tdouble)
  (yp xp A2p bp A1p : val)
  (SH : readable_share sh1),
  let N := matrix_rows A in
  forall  (H : matrix_cols A N)
  (H0 : 0 < N < Int.max_unsigned)
  (H1 : Forall (Forall finite) A)
  (A1ip : val)
  (FR1 : mpred),
semax (func_tycontext f_jacobi2 Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp; 
   temp _s (Vfloat (Float.of_bits (Int64.repr 0))); temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; data_at_ Ews (tarray tdouble N) A1ip;
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p))
   first_loop
 (normal_ret_assert
  (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp; 
   temp _s (Vfloat (Float.of_bits (Int64.repr 0))); temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; data_at Ews (tarray tdouble N) (map Vfloat (invert_diagmatrix (diag_of_matrix A))) A1ip;
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p))).
Proof.
intros.
unfold first_loop.
abbreviate_semax.
assert (Zlength (diag_of_matrix A) = N)
  by (unfold diag_of_matrix; autorewrite with sublist; auto).
forward_for_simple_bound N
  (EX i:Z, PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp;
   temp _s (Vfloat (Float.of_bits (Int64.repr 0))); temp _N (Vint (Int.repr N)); 
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; 
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p;
   data_at Ews (tarray tdouble N)
        (map Vfloat (sublist 0 i (map (BDIV _ (Zconst _ 1)) (diag_of_matrix A)))
          ++ Zrepeat Vundef (N-i)) A1ip))%assert.
-
  entailer!. simpl; apply derives_refl.
- 
   forward.
   forward.
   change float with (ftype Tdouble) in *.
   rewrite Znth_map by list_solve.
   simpl force_val.
   entailer!.
   apply derives_refl'; f_equal.
   clear - H3 H2 H0 H H1.
   rewrite (sublist_split 0 i (i+1)) by list_solve.
   rewrite sublist_len_1 by list_solve.
   replace (matrix_rows A - i) with (matrix_rows A - (i+1) + 1) by lia.
   rewrite <- Zrepeat_app by lia.
   change (Zrepeat Vundef 1) with [Vundef].
   list_simplify.
   rewrite Znth_app1 by list_solve. f_equal.
   list_simplify.
-
list_simplify.
rewrite sublist_map.
rewrite sublist_same by auto.
fold (invert_diagmatrix (diag_of_matrix A)).
entailer!.
Qed.

Definition choose {A} n (a b: A) := if Nat.odd n then a else b.

Lemma choose_S {A}: forall n (a b: A), choose (S n) a b = choose n b a.
Proof. 
intros. unfold choose. rewrite Nat.odd_succ, <-Nat.negb_odd;
        destruct (Nat.odd n); auto.
Qed.

Lemma floatlist_eqv_refl {t}: forall (x: vector t), floatlist_eqv x x.
Proof.
induction x; constructor; auto.
Qed.

Lemma jacobi_iter_congr: 
 forall {t} A1 A2 (b: vector t) x x',
  strict_floatlist_eqv x x' ->
  Forall finite A1 ->
  Forall (Forall finite) A2 ->
  Forall finite b ->  
   Zlength b = matrix_rows A2 ->
   Zlength A1 = matrix_rows A2 ->
   matrix_cols A2 (Zlength x) ->
   floatlist_eqv (jacobi_iter A1 A2 b x) (jacobi_iter A1 A2 b x') .
Proof.
intros.
unfold jacobi_iter.
unfold diagmatrix_vector_mult.
unfold map2.
apply Forall2_map.
rewrite <- Zmatrix_rows_nat in *.
rewrite Zlength_correct in *.
apply Zmatrix_cols_nat in H5.
apply Nat2Z.inj in H3,H4.
unfold matrix_rows_nat in *.
revert A1 A2 H0 H1 H3 H4 H5; induction H2; 
   destruct A1 as [|A1r A1]; destruct A2 as [|A2r A2]; intros;
  try inv H0; try inv H1; try inv H3; try inv H4; constructor; auto;
   inv H5; inv H6.
-
unfold uncurry.
 apply BMULT_congr; auto.
 apply BMINUS_congr; auto.
 apply dotprod_congr; auto.
-
 apply IHForall; auto.
Qed.

Lemma floatlist_eqv_trans: forall {t} (x y z: list (ftype t)),
  floatlist_eqv x y -> floatlist_eqv y z -> floatlist_eqv x z.
Proof.
induction x; destruct y,z; intros; inv H; inv  H0; constructor; auto.
rewrite H4; auto.
eapply IHx; eauto.
Qed.

Lemma strict_floatlist_eqv_i1: 
   forall {t} (a b: list (ftype t)),
    Forall finite a -> floatlist_eqv a b -> strict_floatlist_eqv a b.
Proof.
induction 2; inv H;constructor.
apply strict_float_eqv_i1; auto.
apply IHForall2; auto.
Qed.

Lemma finite_is_finite: forall {t} (x: ftype t),
   finite x <-> Binary.is_finite _ _ x = true.
Proof.
split; intros;
destruct x; inv H; try reflexivity.
constructor; auto.
Qed.

Lemma float_eqv_strict_float_eqv:
 forall {t} (x y: ftype t),
   finite x -> float_eqv x y -> strict_float_eqv x y.
Proof.
 intros.
 destruct x; inv H; destruct y; inv H0; constructor; auto.
Qed.

Lemma strict_float_eqv_finite1:
  forall {t} (x y: ftype t),
    strict_float_eqv x y -> finite x.
Proof.
intros.
destruct x,y; inv H; constructor; auto.
Qed.

Lemma finite_dotprod_e: forall {t} (x y: vector t),
  Zlength x = Zlength y ->
  finite (dotprod x y) -> Forall finite x /\ Forall finite y.
Proof.
intros.
rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
unfold dotprod in H0.
rewrite <- fold_left_rev_right in H0.
rewrite rev_combine in H0 by auto.
rewrite <- (rev_length x), <- (rev_length y) in H.
assert (Forall finite (rev x) /\ Forall finite (rev y)).
2:rewrite <- (rev_involutive x), <- (rev_involutive y);
   destruct H1; split; apply Forall_rev; auto.
forget (rev x) as a; forget (rev y) as b.
revert b H H0; induction a; destruct b; intros; inv H.
split; constructor.
specialize (IHa _ H2).
simpl in H0.
set (u := fold_right _ _ _) in *. clearbody u.
assert (finite a /\ finite f /\ finite u); [ | split; constructor; tauto].
clear - H0.
apply finite_is_finite in H0.
destruct a,f,u; inv H0; try solve [split3; constructor; auto].
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
Qed.


Lemma finite_norm2_e: forall {t} (x: vector t),
  finite (norm2 x) -> Forall finite x.
Proof.
intros.
apply finite_dotprod_e in H; auto.
destruct H; auto.
Qed.

Lemma finite_norm2_sub: 
  forall {t} s (x y: vector t), 
  Zlength x = Zlength y ->
  finite s -> 
  float_eqv s (norm2 (vector_sub x y)) ->
  Forall finite y.
Proof.
  intros.
   apply float_eqv_strict_float_eqv in H1; auto.
   apply strict_float_eqv_sym in H1.
   apply strict_float_eqv_finite1 in H1. clear s H0.
   apply finite_norm2_e in H1.
   rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
   revert y H H1; induction x; destruct y; simpl; intros; 
     inv H; inv H1; constructor; auto.
   clear - H3.
   rewrite finite_is_finite in H3.
   destruct a, f; inv H3; try constructor; auto.
   destruct s,s0; inv H0.
Qed.

Lemma jacobi2_second_loop: forall {Espec : OracleKind}
 (shA1 shA2 shb shx shy : share)
  (A : matrix Tdouble)
  (A1p A2p bp xp : val)
  (b x : vector Tdouble)
  (acc : ftype Tdouble)
  (maxiter : Z)
  (gv : globals)
  (SHA1 : readable_share shA1)
  (SHA2 : readable_share shA2)
  (SHb : readable_share shb)
  (SHx : writable_share shx)
  (SHy : writable_share shy)
  (N := matrix_rows A : Z)
  (COLS: matrix_cols A N)
  (H1 : Forall (Forall finite) A)
  (H1': Forall finite (invert_diagmatrix (diag_of_matrix A)))
  (H2 : Forall finite b)
  (H3 : Forall finite x)
  (H4 : finite acc)
  (H5 : 0 < maxiter <= Int.max_unsigned)
  (H0 : 0 < N < Int.max_unsigned)
  (yp  A1ip : val)
  (FR1 : list mpred),
semax (func_tycontext f_jacobi2 Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp; temp _s (Vfloat (Zconst Tdouble 0));
   temp _N (Vint (Int.repr (matrix_rows A))); gvars gv; temp _A1 A1p; 
   temp _A2 A2p; temp _b bp; temp _x xp; temp _acc (Vfloat acc);
   temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FRZL FR1; 
      data_at_ shy (tarray tdouble N) yp; 
      crs_rep shA2 (remove_diag A) A2p;
      data_at shb (tarray tdouble N) (map Vfloat b) bp;
      data_at shx (tarray tdouble N) (map Vfloat x) xp;
      data_at shA1 (tarray tdouble (matrix_rows A))
          (map Vfloat (invert_diagmatrix (diag_of_matrix A))) A1ip)) second_loop
  (normal_ret_assert
     (EX (n : nat) (z : vector Tdouble) (s : ftype Tdouble),
      PROP (0 < Z.of_nat n <= maxiter; floatlist_eqv z (jacobi_n A b x n);
      float_eqv s (norm2 (vector_sub (jacobi_n A b x (Init.Nat.pred n)) z));
      Z.of_nat n = maxiter \/ BCMP Tdouble Gt true s acc = false \/ ~finite s)
      LOCAL (temp _A1inv A1ip; temp _y (choose n xp yp); temp _z (choose n yp xp);
      temp _N (Vint (Int.repr (matrix_rows A))); gvars gv; 
      temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp; 
      temp _acc (Vfloat acc); temp _s (Vfloat s))
      SEP (FRZL FR1; 
         data_at_ (choose n shx shy) (tarray tdouble N) (choose n xp yp);
         crs_rep shA2 (remove_diag A) A2p;
         data_at shb (tarray tdouble N) (map Vfloat b) bp;
         data_at (choose n shy shx) (tarray tdouble N) (map Vfloat z) (choose n yp xp);
         data_at shA1 (tarray tdouble (matrix_rows A))
           (map Vfloat (invert_diagmatrix (diag_of_matrix A))) A1ip))%argsassert).
Proof.
intros.
unfold second_loop.
abbreviate_semax.
forward_loop 
  (EX n:nat, EX z: vector Tdouble, EX s: ftype Tdouble,
   PROP (0 <= Z.of_nat n < maxiter;
             floatlist_eqv z (jacobi_n A b x n);
             Forall finite z;
             (n>0)%nat -> float_eqv s (norm2 (vector_sub (jacobi_n A b x (Init.Nat.pred n)) z)))
   LOCAL (temp _A1inv A1ip; temp _y (choose n xp yp); temp _z (choose n yp xp);
   temp _N (Vint (Int.repr (matrix_rows A))); gvars gv; temp _A1 A1p; 
   temp _A2 A2p; temp _b bp; temp _x xp; temp _acc (Vfloat acc);
   temp _maxiter (Vint (Int.repr (maxiter- Z.of_nat n)));
   temp _s (Vfloat s))
   SEP (FRZL FR1;
   data_at_ (choose n shx shy) (tarray tdouble N) (choose n xp yp); 
   crs_rep shA2 (remove_diag A) A2p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at (choose n shy shx) (tarray tdouble N) (map Vfloat z) (choose n yp xp);
   data_at shA1 (tarray tdouble (matrix_rows A))
     (map Vfloat (invert_diagmatrix (diag_of_matrix A))) A1ip))%assert.
-
Exists O x (Zconst Tdouble 0).
entailer!.
unfold jacobi_n. simpl Nat.iter.
apply floatlist_eqv_refl.
compute_every @choose.
auto.
-
Intros n z s.
fold N.
progress change float with (ftype Tdouble) in *.
forward_call (shA1,shA2,shb, choose n shy shx, choose n shx shy,
                       A1ip, invert_diagmatrix (diag_of_matrix A), A2p, 
                        (remove_diag A),
                         bp, b, choose n yp xp,
                         z,   choose n xp yp).
rewrite matrix_rows_remove_diag.
fold N. cancel.
rewrite matrix_rows_remove_diag.
fold N.
split3; [ | | split3]; auto; try lia.
unfold choose; destruct (Nat.odd n); auto. 
unfold choose; destruct (Nat.odd n); auto.
apply matrix_cols_remove_diag; auto.
apply finite_remove_diag; auto.
Intros a.  clear s H8. destruct a as [y s]. unfold fst, snd in *.
forward.
forward.
forward.
forward.
forward_if (temp _t'4 (Val.of_bool (Binary.is_finite (fprec Tdouble) (femax Tdouble) s && BCMP _ Gt true s acc))).
  { forward. 
    entailer!.
   change (Float.cmp Cgt s acc) with ((s>acc)%F64).
   replace (Binary.is_finite _ _ _) with true; auto.
   symmetry.
   clear - H8. destruct s; try discriminate; reflexivity.
  } 
  { forward.
    entailer!.
   replace (Binary.is_finite _ _ _) with false; auto.
   symmetry. clear - H8. destruct s; try discriminate; try reflexivity.
  }
forward_if (temp _t'5 (Val.of_bool (Binary.is_finite (fprec Tdouble) (femax Tdouble) s 
                         && BCMP _ Gt true s acc && Z.gtb maxiter (Z.of_nat n + 1)))).
  { forward. change 1024 with (femax Tdouble) in H8.  rewrite H8. 
    entailer!. simpl andb. 
    destruct (Z.gtb_spec maxiter (Z.of_nat n + 1)).
    rewrite Int.eq_false. reflexivity.
   intro. apply repr_inj_unsigned in H26; try rep_lia.
   replace (maxiter - Z.of_nat n - 1) with 0 by lia.
   rewrite Int.eq_true. reflexivity.
  }
  { change 1024 with (femax Tdouble) in H8.  rewrite H8.
    forward. entailer!. rewrite H8. reflexivity.
  }
forward_if.
+
  forward. 
 Exists (S n) y s.
 rewrite !choose_S.
 entailer!.
 * rewrite !andb_true_iff in H8. destruct H8 as [[H8a H8b] H8c].
   assert (FINy: Forall finite y). { 
    clear - H25 H22 H8a H10.

  change 1024 with (femax Tdouble) in H8a.
  rewrite <- finite_is_finite in H8a.
  eapply finite_norm2_sub in H10; auto. list_solve.
  }
  split; [ | split3]; auto. 
  --
     eapply floatlist_eqv_trans; [apply H9 | clear H9].
     apply jacobi_iter_congr; auto.
     change (strict_floatlist_eqv z (jacobi_n A b x n)).
    apply strict_floatlist_eqv_i1; auto.
     apply finite_remove_diag; auto.
     clear - H19. rewrite Zlength_map in H19. unfold matrix_rows in *. rep_lia.
     rewrite Zlength_map in H16; rewrite H16. clear; unfold matrix_rows; rep_lia.
     rewrite Zlength_map in H22; rewrite H22.
     rewrite matrix_rows_remove_diag.
     rewrite Z.max_r by lia.
     apply matrix_cols_remove_diag. auto.
 --
   intros _.
   simpl pred. clear - H10 H6 H8a. 
   eapply float_eqv_trans; [apply H10 | ].
   change 1024 with (femax Tdouble) in H8a.
   apply finite_is_finite in H8a.
   apply float_eqv_strict_float_eqv in H10; auto.
   apply strict_float_eqv_sym in H10.
   apply strict_float_eqv_finite1 in H10. clear s H8a.
   apply finite_norm2_e in H10.
   apply norm2_congr.
   apply vector_sub_congr; auto.
   apply floatlist_eqv_refl.
 --
    f_equal. f_equal. lia.
 *
  rewrite matrix_rows_remove_diag.
  fold N. cancel.
+
 forward.
 Exists (S n) y s.
 rewrite !choose_S.
 entailer!.
 *
    split3; auto.
  --
    unfold jacobi_n in *.
   simpl Nat.iter.
   eapply floatlist_eqv_trans; [apply H9 | ]. clear y H9 H10 H25 H26.
   apply jacobi_iter_congr; auto.
     change (strict_floatlist_eqv z (jacobi_n A b x n)).
    apply strict_floatlist_eqv_i1; auto.
     apply finite_remove_diag; auto.
     clear - H19. rewrite Zlength_map in H19. unfold matrix_rows in *. rep_lia.
     rewrite Zlength_map in H16; rewrite H16. clear; unfold matrix_rows; rep_lia.
     rewrite Zlength_map in H22; rewrite H22.
     rewrite matrix_rows_remove_diag.
     rewrite Z.max_r by lia.
     apply matrix_cols_remove_diag. auto.
 --
   simpl pred.
   clear - H10 H6.
   eapply float_eqv_trans; [apply H10 | ]. clear dependent s.
   apply norm2_congr.
   apply vector_sub_congr; auto.
   apply floatlist_eqv_refl.
 --
     rewrite !andb_false_iff in H8.
     decompose [or] H8.
     right; right. clear - H28. intro. destruct s; inv H28; inv H.
     right. left. auto.
     left. rewrite inj_S. 
     destruct (Z.gtb_spec maxiter (Z.of_nat n + 1)); inv H27. lia.
*
  rewrite matrix_rows_remove_diag. fold N. cancel.
Qed.

Lemma body_jacobi2: semax_body Vprog Gprog f_jacobi2 jacobi2_spec.
Proof.
start_function.
forward_call.
rewrite matrix_rows_remove_diag; lia.
forward.
forward.
rewrite matrix_rows_remove_diag.
set (N := matrix_rows A) in *.
forward_call (tarray tdouble N, gv).
  entailer!. simpl. do 3 f_equal.  rep_lia.
  simpl. rep_lia.
Intros yp.
forward_call (tarray tdouble N, gv).
  entailer!. simpl. do 3 f_equal.  rep_lia.
  simpl. rep_lia.
Intros A1ip.
freeze FR1 := - (data_at_ _ _ A1ip) (data_at _ _ _ A1p).
change (Sfor _ _ _ _ ) with first_loop.
eapply semax_seq'.
apply jacobi2_first_loop; auto.
abbreviate_semax.
thaw FR1.
freeze FR1 := (mem_mgr gv) (malloc_token _ _ _)(malloc_token _ _ _) (data_at _ _ _ A1p).
eapply semax_seq'.
eapply jacobi2_second_loop; try eassumption; auto.
Intros n z s.
abbreviate_semax.
thaw FR1.
fold N.
progress change float with (ftype Tdouble).
freeze FR2 := - ( data_at_ _ _ (choose n xp yp))
                         (data_at _ _ _ (choose n yp xp)).
apply semax_seq' with
 (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp;
   temp _N (Vint (Int.repr N)); 
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; 
   temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
   SEP (FRZL FR2; 
       data_at_ Ews (tarray tdouble N) yp;
       data_at Ews (tarray tdouble N)  (map Vfloat z) xp)).
-
 unfold choose. destruct (Nat.odd n) eqn:ODD;
 forward_if; try contradiction.
 + forward_for_simple_bound N
        (EX i:Z, (PROP ( )
             LOCAL (temp _A1inv A1ip; temp _y xp; temp _z yp;
                temp _N (Vint (Int.repr N)); gvars gv; 
                temp _A1 A1p; temp _A2 A2p; temp _b bp; 
                temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
            SEP (FRZL FR2; 
                     data_at Ews (tarray tdouble N) 
                          (sublist 0 i (map Vfloat z) ++ Zrepeat Vundef (N-i)) xp;
                     data_at Ews (tarray tdouble N) (map Vfloat z) yp)))%assert.
  * rewrite sublist_nil, app_nil_l. entailer!. apply derives_refl.
  * forward. forward. entailer!. apply derives_refl'; f_equal.
     progress change float with (ftype Tdouble) in *.
     clear - H12 H0 H18. rewrite Zlength_map in H18. simpl.
     forget (matrix_rows A) as N. list_solve.
  * forward. entailer!. list_simplify.
 + forward. entailer!. 
 + forward. entailer!.
-
 thaw FR2.
 abbreviate_semax.
 forward_call free_spec_sub (yp, gv).
 saturate_local. destruct yp; try contradiction; simpl. cancel.
 forward_call free_spec_sub (A1ip, gv).
 saturate_local. destruct A1ip; try contradiction; simpl. cancel.
 forward.
 Exists z (pred n) s.
 fold N. replace (S (pred n)) with n by lia.
 entailer!.
Qed.

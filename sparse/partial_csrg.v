Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.
From Iterative.sparse Require Import sparse_model distinct partial_csr.

Set Bullet Behavior "Strict Subproofs".

Lemma coog_entry_bounds [coog : coog_matrix] :
  coog_matrix_wellformed coog ->
  forall i, 
  0 <= i < Zlength (coog_entries coog) ->
  0 <= fst (Znth i (coog_entries coog)) < coog_rows coog /\
  0 <= snd (Znth i (coog_entries coog)) < coog_cols coog.
Proof.
  intros.
  unfold coog_matrix_wellformed in H.
  destruct H as [[? ?] ?].
  rewrite Forall_Znth in H2.
  apply H2. exact H0.
Qed.

Definition coog_upto (i : Z) (coog : coog_matrix) :=
  Build_coog_matrix (coog_rows coog) (coog_cols coog) (sublist 0 i (coog_entries coog)).

Definition cd_upto_coog (i : Z) (coog : coog_matrix) : Z :=
  count_distinct (sublist 0 i (coog_entries coog)).

Definition entries_correspond_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall h,
  0 <= h < Zlength (coog_entries coog) ->
  let '(r, c) := Znth h (coog_entries coog) in 
  let k := cd_upto_coog (h + 1) coog - 1 in 
    Znth r (csr_row_ptr csr) <= k < Znth (r + 1) (csr_row_ptr csr) /\
    Znth k (csr_col_ind csr) = c.

Definition no_extra_zeros_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall r k, 0 <= r < coog_rows coog ->
    Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) ->
    let c := Znth k (csr_col_ind csr) in 
    In (r, c) (coog_entries coog).

Inductive coog_csr {t} (coog : coog_matrix) (csr : csr_matrix t) : Prop :=
  build_coog_csr : forall 
    (coog_csr_rows : coog_rows coog = csr_rows csr)
    (coog_csr_cols : coog_cols coog = csr_cols csr)
    (coog_csr_vals : Zlength (csr_vals csr) = count_distinct (coog_entries coog))
    (coog_csr_entries : entries_correspond_coog coog csr)
    (coog_csr_zeros : no_extra_zeros_coog coog csr),
    coog_csr coog csr.

Inductive partial_CSRG (h : Z) (r : Z) (coog : coog_matrix) 
  (rowptr : list val) (colind : list val) : Prop :=
  build_partial_CSRG : forall 
    (partial_CSRG_coog : coog_matrix_wellformed coog)
    (partial_CSRG_coog_sorted : sorted coord2_le (coog_entries coog))
    (partial_CSRG_i : 0 <= h <= Zlength (coog_entries coog))
    (partial_CSRG_r : -1 <= r <= coog_rows coog)
    (partial_CSRG_r' : Forall (fun e => fst e <= r) (coog_entries (coog_upto h coog)))
    (partial_CSRG_r'' : Forall (fun e => fst e >= r) (sublist h (Zlength (coog_entries coog)) (coog_entries coog)))
    (csr : csr_matrix Tdouble)
    (partial_CSRG_wf : csr_matrix_wellformed csr)
    (partial_CSRG_coog_csr : coog_csr (coog_upto h coog) csr)
    (partial_CSRG_colind : sublist 0 (Zlength (csr_col_ind csr)) colind = map (Vint oo Int.repr) (csr_col_ind csr))
    (partial_CSRG_rowptr : sublist 0 (r + 1) rowptr = map (Vint oo Int.repr) (sublist 0 (r + 1) (csr_row_ptr csr)))
    (partial_CSRG_colind' : Zlength colind = count_distinct (coog_entries coog))
    (partial_CSRG_rowptr' : Zlength rowptr = coog_rows coog + 1)
    (partial_CSRG_dbound : count_distinct (coog_entries coog) <= (Int.max_unsigned))
    , partial_CSRG h r coog rowptr colind.

Lemma cd_upto_coog_pos i coog :
  0 <= cd_upto_coog i coog.
Proof.
  unfold cd_upto_coog.
  pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))). lia. 
Qed.

Lemma last_cons {A : Type} (x : A) l default :
  last (x :: l) default = x \/
  last (x :: l) default = last l default.
Proof.
  destruct l.
  + left. simpl. auto.
  + right. simpl. auto.
Qed.

Lemma last_repeat {A : Type} (a : A) (n : nat) default :
  (n > 0)%nat -> last (repeat a n) default = a.
Proof.
  induction n as [|n']; intros.
  + inversion H.
  + destruct n' as [|n''].
    - simpl. auto.
    - replace (repeat a (S (S n''))) with (a :: repeat a (S n'')) by list_solve.
    pose proof (last_cons a (repeat a (S n'')) default).
    destruct H0; auto.
    apply IHn'. lia.
Qed.
    
Lemma last_Zrepeat {A : Type} (a : A) n default :
  n > 0 ->
  last (Zrepeat a n) default = a.
Proof.
  intros.
  unfold Zrepeat. apply last_repeat. lia.
Qed.

Lemma repeat_not_nil {A : Type} (a : A) n :
  (n > 0)%nat ->
  repeat a n <> [].
Proof.
  destruct n as [|n']; intros.
  inversion H.
  simpl. intros contra. inversion contra.
Qed.

Lemma Zrepeat_not_nil {A : Type} (a : A) n :
  n > 0 ->
  Zrepeat a n <> [].
Proof.
  unfold Zrepeat. intros. apply repeat_not_nil. lia.
Qed.

Lemma sublist_longer {A : Type} lo hi (l : list A) :
  Zlength l <= hi ->
  sublist lo hi l = sublist lo (Zlength l) l.
Proof.
  intros. unfold sublist. simpl. f_equal.
  generalize dependent hi. induction l as [|x l']; intros.
  + rewrite !firstn_nil. auto.
  + destruct (hi >? 0) eqn:E.
    2:{ assert (hi <= 0) by lia.
      rewrite Zlength_cons in H.
      pose proof (Zlength_nonneg l'). lia. }
    assert (hi > 0) by lia.
    replace (Z.to_nat hi) with (S (Z.to_nat (hi - 1))) by lia.
    rewrite firstn_cons.
    rewrite Zlength_cons.
    rewrite Z2Nat.inj_succ by list_solve.
    rewrite firstn_cons. f_equal.
    destruct (hi - 1 >? 0) eqn:E1.
    - apply IHl'. list_solve.
    - assert (hi = 1) by lia. subst hi.
      replace (Z.to_nat (1 - 1)) with O by lia. rewrite firstn_O.
      rewrite Zlength_cons in H.
      assert (Zlength l' <= 0) by lia.
      pose proof (Zlength_nonneg l').
      replace (Zlength l') with 0 by lia.
      replace (Z.to_nat 0) with O by lia. 
      rewrite firstn_O. auto.
Qed.


Lemma partial_CSRG_rowptr' : forall {t} r (coog : coog_matrix) (csr : csr_matrix t),
  coog_matrix_wellformed coog ->
  csr_matrix_wellformed csr ->
  coog_csr coog csr ->
  -1 <= r <= coog_rows coog ->
  Forall (fun e => fst e <= r) (coog_entries coog) ->
  sublist (r + 1) (coog_rows coog + 1) (csr_row_ptr csr) = Zrepeat (Zlength (csr_vals csr)) (coog_rows coog - r).
  (* All remaining rows are empty *)
Proof.
  intros.
  inversion_clear H1.
  unfold csr_rows in *.
  apply Znth_eq_ext. list_solve.
  intros.
  rewrite Znth_sublist by list_solve.
  rewrite Znth_Zrepeat by list_solve.
  autorewrite with sublist in H1.
  inversion_clear H0.
  unfold csr_rows in *.
  pose proof rowptr_sorted_e _ CSR_wf_sorted (i+(r+1)) (Zlength (csr_row_ptr csr) - 1) ltac:(list_solve).
  destruct H0 as [[? ?] _].
  destruct (zlt (Znth (i+(r+1)) (csr_row_ptr csr)) (Zlength (csr_vals csr))); [ | lia].
  exfalso. clear H0.
  clear CSR_wf_rowsorted.
  assert (exists i', i + (r + 1) <= i' < coog_rows coog /\ Znth i' (csr_row_ptr csr) < Znth (i' + 1) (csr_row_ptr csr)).
  { rewrite CSR_wf_vals' in l.
    rewrite coog_csr_rows in H1|-*.
    clear -H1 CSR_wf_sorted l H2. destruct H2 as [H2 _].
    unfold csr_rows in *.
    forget (csr_row_ptr csr) as al.
    assert (0 <= i+(r+1) < Zlength al) by lia; clear H1 H2.
    forget (i+(r+1)) as r'. clear r i. rename r' into r.
    pose (bl := sublist r (Zlength al) al).
    assert (Znth 0 bl < Znth (Zlength bl - 1) bl) by (subst bl; list_solve).
    assert (exists i, 0 <= i < Zlength bl-1 /\ Znth i bl < Znth (i+1) bl). 
    2:{ destruct H1 as [i [? ?]]. exists (i+r); split. subst bl; list_solve. subst bl; list_solve. }
    assert (list_solver.sorted Z.le bl). {
    clear - CSR_wf_sorted H.
    intros x y [? ?].
    subst bl.
    rewrite !Znth_sublist by list_solve.
    apply (rowptr_sorted_e _ CSR_wf_sorted (x+r) (y+r) ltac:(list_solve)). }
      assert (0 < Zlength bl) by (subst bl; list_solve).
    clearbody bl. clear - H1 H0 H2.
    destruct bl; [list_solve|].
    autorewrite with sublist in *. clear H2.
    unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
    revert z H0 H1; induction bl; simpl; intros.
    list_solve.
    autorewrite with sublist in *.
    rewrite Znth_pos_cons in H0 by list_solve.
    unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
    destruct (zlt z a).
    exists 0; list_solve.
    assert (a=z). { specialize (H1 0 1). list_solve. }
    subst a.
    destruct (IHbl z) as [i [? ?]].
    list_solve. intros x y ?; specialize (H1 (x+1) (y+1)).
    destruct H.
    rewrite !(Znth_pos_cons (_ + 1)) in H1 by list_solve.
    rewrite !Z.add_simpl_r in H1.
    apply H1. list_solve.
    exists (i+1). list_solve. }
  destruct H0 as [i' [? ?]].
  unfold csr_rows in *.
  pose proof coog_csr_zeros i' (Znth i' (csr_row_ptr csr)) ltac:(lia).
  specialize (H6 ltac:(lia)).
  rewrite Forall_forall in H3.
  apply In_Znth in H6. destruct H6 as [b [??]].
  specialize (H3 (Znth b (coog_entries coog))).
  spec H3. apply Znth_In. list_solve.
  rewrite H7 in H3. simpl in H3. lia.
Qed.

Lemma BPO2_eqv_iff: forall a b, @BPO.eqv _ _ Coord2BPO a b <-> a = b.
Proof.
  intros. destruct a as [a1 a2]. destruct b as [b1 b2].
  split; intros.
  + unfold BPO.eqv in H. unfold coord2_le in H. destruct H.
    simpl in *. destruct H, H0; try lia.
    assert (a2 = b2) by lia. destruct H. rewrite H, H1. auto.
  + unfold BPO.eqv. unfold coord2_le. rewrite H. lia. 
Qed.

Lemma partial_CSRG_duplicate:
    forall h r coog ROWPTR COLIND,
    0 < h < Zlength (coog_entries coog) ->
    (Znth (h-1) (coog_entries coog)) = (Znth h (coog_entries coog)) ->
    r = (fst (Znth (h-1) (coog_entries coog))) ->
    (* Znth (cd_upto_coog h coog - 1) VAL = Vfloat f -> *)
    partial_CSRG h r coog ROWPTR COLIND ->
    partial_CSRG (h+1) r coog ROWPTR COLIND .
Proof.
  intros. rename H0 into Hdup.
  inversion_clear H2. apply build_partial_CSRG with csr; auto.
  + (* partial_CSRG_i *)
    split; try lia.
  + (* partial_CSRG_r' *)
    unfold coog_upto in partial_CSRG_r'. simpl in partial_CSRG_r'.
    unfold coog_upto. simpl.
    rewrite sublist_last_1 by list_solve.
    rewrite Forall_app. split; auto.
    apply Forall_cons; [|apply Forall_nil].
    rewrite <-Hdup. rewrite H1. lia.
  + (* partial_CSRG_r''*)
    rewrite (sublist_split h (h + 1)) in partial_CSRG_r'' by list_solve.
    rewrite Forall_app in partial_CSRG_r''.
    destruct partial_CSRG_r''. auto.
  + (* partial_CSRG_coog_csr *)
    inversion_clear partial_CSRG_coog_csr.
    apply build_coog_csr; try auto.
    - (* coog_csr_vals *)
      rewrite coog_csr_vals.
      unfold coog_upto; simpl.
      apply count_distinct_noincr; try list_solve.
      rewrite Hdup.
      remember (Znth h (coog_entries coog)) as xy.
      destruct xy as [x y].
      unfold BPO.lt, coord2_le. lia.
    - (* coog_csr_entries *) 
      unfold entries_correspond_coog.
      intros. simpl.
      remember (Znth h0 (sublist 0 (h + 1) (coog_entries coog))) as r0c0. 
      destruct r0c0 as [r0 c0].
      unfold entries_correspond_coog in coog_csr_entries.
      unfold coog_upto in H0. simpl in H0.
      rewrite Zlength_sublist in H0 by list_solve. 
      destruct (h0 <? h) eqn:E.
      { rewrite Z.ltb_lt in E. 
        assert (0 <= h0 < Zlength (coog_entries (coog_upto h coog))).
        { unfold coog_upto. simpl. rewrite Zlength_sublist by list_solve. lia. } 
        specialize (coog_csr_entries h0 H2); clear H2.
        simpl in coog_csr_entries.
        assert (Znth h0 (sublist 0 h (coog_entries coog)) = Znth h0 (sublist 0 (h + 1) (coog_entries coog))).
        { rewrite Znth_sublist by list_solve.
          rewrite Znth_sublist by list_solve.
          auto. }
        rewrite H2 in coog_csr_entries. clear H2.
        rewrite <-Heqr0c0 in coog_csr_entries.
        (* destruct coog_csr_entries as [H101 H102]. *)
        assert (cd_upto_coog (h0 + 1) (coog_upto h coog) = cd_upto_coog (h0 + 1) (coog_upto (h + 1) coog)).
          { unfold coog_upto, cd_upto_coog. simpl.
            rewrite sublist_sublist00 by list_solve.
            rewrite sublist_sublist00 by list_solve. auto. } 
        rewrite H2 in coog_csr_entries. auto. } 
      rewrite Z.ltb_ge in E. assert (h = h0) by lia. subst h0.
      specialize (coog_csr_entries (h-1)).
      assert (0 <= h - 1 < Zlength (coog_entries (coog_upto h coog))).
      { split. lia. unfold coog_upto; simpl. list_solve. } 
      specialize (coog_csr_entries H2); clear H2.
      assert (Znth (h - 1) (coog_entries (coog_upto h coog)) = Znth (h - 1) (coog_entries coog)).
      { unfold coog_upto; simpl. list_solve. } 
      rewrite H2 in coog_csr_entries. rewrite Hdup in coog_csr_entries.
      assert (Znth h (coog_entries coog) = Znth h (sublist 0 (h + 1) (coog_entries coog))).
      { rewrite Znth_sublist by list_solve. list_solve. } 
      rewrite H3 in coog_csr_entries.
      rewrite <- Heqr0c0 in coog_csr_entries.
      assert (cd_upto_coog (h - 1 + 1) (coog_upto h coog) = cd_upto_coog (h + 1) (coog_upto (h + 1) coog)).
      { unfold coog_upto, cd_upto_coog; simpl. 
        rewrite sublist_sublist00 by list_solve.
        rewrite sublist_sublist00 by list_solve.
        replace (h - 1 + 1) with h by lia.
        apply count_distinct_noincr; try list_solve.
        rewrite Hdup. unfold BPO.lt. unfold coord2_le. lia. } 
      rewrite H4 in coog_csr_entries. auto. 
    - (* coog_csr_zeros *)
      unfold no_extra_zeros_coog in *.
      intros r0 k0 ? ?.
      assert (coog_rows (coog_upto (h + 1) coog) = coog_rows (coog_upto h coog)).
      { unfold coog_upto. simpl. auto. } 
      rewrite H3 in H0; clear H3.
      specialize (coog_csr_zeros r0 k0 H0 H2).
      unfold coog_upto; simpl.
      unfold coog_upto in coog_csr_zeros; simpl in coog_csr_zeros.
      rewrite (sublist_split _ h) by list_solve.
      apply in_or_app. left. auto.
Qed.

Lemma partial_CSRG_newcol:
   forall i r c coog ROWPTR COLIND,
   0 < i < Zlength (coog_entries coog) ->
   Znth i (coog_entries coog) = (r, c) ->
   r = fst (Znth (i-1) (coog_entries coog)) ->
   c <> snd (Znth (i-1) (coog_entries coog)) ->
   partial_CSRG i r coog ROWPTR COLIND  ->
   partial_CSRG (i + 1) r coog ROWPTR
  (upd_Znth (count_distinct (sublist 0 i (coog_entries coog))) COLIND (Vint (Int.repr c))).
  (* (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) VAL (Vfloat x)). *)
Proof.
  intros. rename H1 into Hrow. rename H2 into Hcol.
  inversion_clear H3.
  assert (Hcsrlen: 0 < Zlength (csr_row_ptr csr) - (r + 1)).
      { inversion_clear partial_CSRG_coog_csr.
        rename coog_csr_rows into H100.
        unfold csr_rows, coog_upto in H100. simpl in H100.
        replace (Zlength (csr_row_ptr csr) - (r + 1)) with (coog_rows coog - r) by lia.
        inversion_clear partial_CSRG_coog.
        rewrite Forall_Znth in H2.
        assert (0 <= i - 1 < Zlength (coog_entries coog)) by lia.
        specialize (H2 (i-1) H3). lia. }
  assert (Hcd_incr: cd_upto_coog i coog + 1 = cd_upto_coog (i+1) coog).
  { unfold cd_upto_coog. apply count_distinct_incr; [|lia].
    pose proof sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia) ltac:(lia).
    unfold BPO.lt. split;[auto|].
    unfold not. intros.
    rewrite H0 in H1, H2.
    destruct (Znth (i-1) (coog_entries coog)) as [r0 c0] eqn:Er0c0.
    unfold coord2_le in H1, H2. simpl in H1, H2.
    assert (c = c0) by lia. subst c0. destruct Hcol. auto. }
  pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) ++ Zrepeat (cd_upto_coog i coog + 1) (Zlength (csr_row_ptr csr) - (r+1))).
  assert (Hnew_row_ptr_len: Zlength new_row_ptr = Zlength (csr_row_ptr csr)).
  { unfold new_row_ptr. rewrite Zlength_app by list_solve.
    rewrite Zlength_sublist, Zlength_Zrepeat by list_solve. lia. }
  pose (csr' := Build_csr_matrix Tdouble (csr_cols csr) 
       (Zrepeat (Zconst Tdouble 0) (cd_upto_coog i coog) ++ [Zconst Tdouble 0]) (* csr_vals does not matter *)
       (sublist 0 (cd_upto_coog i coog) (csr_col_ind csr) ++ [c])
       new_row_ptr).
  apply build_partial_CSRG with csr'; auto.
  + (* partial_CSRG_i *) 
    lia.
  + (* partial_CSRG_r' *) 
    unfold coog_upto; simpl.
    unfold coog_upto in partial_CSRG_r'; simpl in *.
    rewrite (sublist_split _ i) by list_solve.
    rewrite Forall_app; split; auto.
    rewrite sublist_len_1 by list_solve.
    apply Forall_cons; [|apply Forall_nil].
    rewrite H0. simpl. lia.
  + (* partial_CSRG_r'' *)
    rewrite (sublist_split _ (i+1)) in partial_CSRG_r'' by list_solve.
    rewrite Forall_app in partial_CSRG_r''. 
    destruct partial_CSRG_r''. apply H2.
  + (* partial_CSRG_wf *)
    inversion_clear partial_CSRG_wf.
    assert (Hcsr'vals: Zlength (csr_vals csr') = cd_upto_coog i coog + 1).
    { unfold csr'. simpl. 
      rewrite Zlength_app. rewrite Zlength_Zrepeat.
      rewrite Zlength_cons, Zlength_nil; simpl. auto.
      apply cd_upto_coog_pos. }
    apply build_csr_matrix_wellformed; auto.
    - (* CSR_wf_rows *) 
      unfold csr_rows; subst csr'; simpl.
      unfold csr_rows in CSR_wf_rows.
      assert (Zlength new_row_ptr = Zlength (csr_row_ptr csr)).
      { unfold new_row_ptr. rewrite Zlength_app.
        rewrite Zlength_Zrepeat, Zlength_sublist. lia. lia.
        replace (Zlength (csr_row_ptr csr)) with (csr_rows csr + 1).
        replace (csr_rows csr) with (coog_rows coog). lia. 
        inversion partial_CSRG_coog_csr. auto.
        unfold csr_rows. lia. 
        replace (Zlength (csr_row_ptr csr)) with (csr_rows csr + 1).
        replace (csr_rows csr) with (coog_rows coog). lia.
        inversion partial_CSRG_coog_csr. auto.
        unfold csr_rows. lia. } 
      rewrite H1. lia.
    - (* CSR_wf_vals *)
      subst csr'; simpl.
      pose proof (cd_upto_coog_pos i coog).
      rewrite Zlength_app by list_solve.
      rewrite Zlength_Zrepeat by lia.
      rewrite Zlength_cons, Zlength_nil; simpl.
      rewrite Zlength_app by list_solve.
      rewrite Zlength_cons, Zlength_nil; simpl.
      rewrite Zlength_sublist; try lia.
      inversion_clear partial_CSRG_coog_csr.
      rewrite <- CSR_wf_vals, coog_csr_vals.
      unfold cd_upto_coog, coog_upto; simpl. lia.
    - (* CSR_wf_vals' *)
      rewrite Hcsr'vals.
      assert (0 < Zlength (csr_row_ptr csr) - (r + 1)).
      { inversion_clear partial_CSRG_coog_csr.
        rename coog_csr_rows into H100.
        unfold csr_rows, coog_upto in H100. simpl in H100.
        replace (Zlength (csr_row_ptr csr) - (r + 1)) with (coog_rows coog - r) by lia.
        inversion_clear partial_CSRG_coog.
        rewrite Forall_Znth in H2.
        assert (0 <= i - 1 < Zlength (coog_entries coog)) by lia.
        specialize (H2 (i-1) H3). lia. }
      replace (csr_rows csr') with (Zlength (csr_row_ptr csr') - 1) by (unfold csr_rows; lia).
      rewrite Znth_last.
      unfold csr', new_row_ptr; simpl.
      rewrite last_app.
      2:{ apply Zrepeat_not_nil. lia. }
      rewrite last_Zrepeat by lia.
      unfold cd_upto_coog. auto.
    - (* CSR_wf_sorted *)
      pose proof (rowptr_sorted_e _ CSR_wf_sorted).
      unfold list_solver.sorted.  intros a b [Hab Hbl].
      unfold csr', new_row_ptr; simpl.
      destruct (0 <? a) eqn:E0a.
      2:{ (* case a = 0 *)
          assert (a = 0) by lia. subst a. clear E0a.
          rewrite Znth_0_cons. 
          destruct (0 <? b) eqn:E0b.
          2:{ assert (b = 0) by lia. subst b. rewrite Znth_0_cons. lia. }
          destruct (b <=? r+1) eqn:Ebr.
          { change (?A :: ?B ++ ?C) with ((A::B)++C).
            rewrite Znth_app1 by list_solve. 
            change (?A :: ?B ++ ?C) with ((A::B)++C).
            rewrite Znth_app1 by list_solve.
            rewrite Znth_pos_cons by lia.
            rewrite Znth_sublist by list_solve. list_solve. } 
          assert (b >= r+2) by lia. clear Ebr E0b.
          rewrite Znth_pos_cons by list_solve.
          rewrite <-app_assoc. rewrite Znth_app2 by list_solve.
          rewrite Zlength_sublist by list_solve.
          replace (b - 1 - (r + 1 - 0)) with (b-r-2) by lia.
          destruct (b-r-2 <? Zlength (csr_row_ptr csr) - (r + 1)) eqn:Ebr.
          { assert (b-r-2 < Zlength (csr_row_ptr csr) - (r + 1)) by lia.
            rewrite Znth_app1 by list_solve.
            rewrite Znth_Zrepeat by list_solve.
            pose proof (cd_upto_coog_pos i coog). lia. }
          assert (b-r-2 >= Zlength (csr_row_ptr csr) - (r + 1)) by lia.
          rewrite Znth_app2 by list_solve.
          rewrite Zlength_Zrepeat by list_solve.
          assert (b >= Zlength (csr_row_ptr csr) + 1) by lia. clear H3.
          assert (b < Zlength (csr_row_ptr csr) + 2).
          { rewrite Zlength_cons, Zlength_app, Zlength_cons, Zlength_nil in Hbl.
            simpl in Hbl. unfold new_row_ptr in Hbl. list_solve. }
          replace (b - r - 2 - (Zlength (csr_row_ptr csr) - (r + 1))) with 0 by lia.
          rewrite Znth_0_cons. 
          destruct (Int.unsigned_range_2 (Int.repr 1)). 
          eapply Z.le_trans with (Int.unsigned (Int.repr 1)); auto. }
      (* a > 0 *)
      assert (H0a: 0 < a) by lia; clear E0a.
      assert (H0b: 0 < b) by lia.
      destruct (a <=? r+1) eqn:Ear.
      { (* a <= r+1 *)
        assert (0 < a <= r+1) by lia. clear H0a Ear.
        assert (Znth a (0 :: (sublist 0 (r + 1) (csr_row_ptr csr) ++
          Zrepeat (cd_upto_coog i coog + 1) (Zlength (csr_row_ptr csr) - (r + 1))) ++
          [Int.max_unsigned]) = (Znth (a-1) (sublist 0 (r+1) (csr_row_ptr csr)))).
        { rewrite Znth_pos_cons by list_solve.
          rewrite Znth_app1 by list_solve.
          rewrite Znth_app1 by list_solve. auto. }
        rewrite H3; clear H3.
        rewrite (Znth_pos_cons b) by list_solve.
        destruct (b<=?r+1) eqn:Ebr.
        { (* b <= r+1 *)
          rewrite Znth_app1 by list_solve.
          rewrite Znth_app1 by list_solve.
          specialize (H1 (a-1) (b-1)). list_solve. }
        assert (b >= r+2) by lia. clear Ebr.
        destruct (b-r-2 <? Zlength (csr_row_ptr csr) - (r + 1)) eqn:Ebr.
        { (* b not the last element *) 
          (* The only interesting case in sortedness proof *)
          assert (b <= Zlength (csr_row_ptr csr)) by lia.
          rewrite <- app_assoc. rewrite Znth_app2 by list_solve.
          rewrite Znth_app1 by list_solve.
          rewrite Znth_Zrepeat by list_solve.
          rewrite Znth_sublist by list_solve. 
          apply Z.le_trans with (Znth r (csr_row_ptr csr)).
          + specialize (H1 (a-1+0) (r)). list_solve.
          + inversion_clear partial_CSRG_coog_csr.
            unfold entries_correspond_coog in coog_csr_entries.
            specialize (coog_csr_entries (i-1)).
            assert (0 <= i-1 < Zlength (coog_entries (coog_upto i coog))).
            { unfold coog_upto; simpl. rewrite Zlength_sublist by list_solve. lia. }
            specialize (coog_csr_entries H5); clear H5.
            assert ((Znth (i - 1) (coog_entries (coog_upto i coog))) =
              (Znth (i - 1) (coog_entries coog))).
            { unfold coog_upto. simpl. rewrite Znth_sublist by list_solve. list_solve. }
            rewrite H5 in coog_csr_entries; clear H5.
            destruct (Znth (i-1) (coog_entries coog)) as [r0 c0] eqn:Er0c0.
            assert (r = r0) by auto. subst r0.
            destruct coog_csr_entries.
            replace (i-1+1) with i in H5 by lia.
            destruct H5.
            eapply Z.le_trans; [apply H5|]. 
            unfold cd_upto_coog. simpl.
            rewrite sublist_prefix. replace (Z.min i i) with i by lia. lia. }
        (* b is the last element *)
        assert (b >= Zlength (csr_row_ptr csr) +1 ) by lia. clear Ebr.
        rewrite <- app_assoc. rewrite Znth_app2 by list_solve.
        rewrite Znth_app2 by list_solve.
        assert (b <= Zlength ((csr_row_ptr csr)) + 1).
        { rewrite Zlength_cons, Zlength_app, Zlength_cons, Zlength_nil in Hbl.
          simpl in Hbl. unfold new_row_ptr in Hbl. simpl in Hbl.
          rewrite Zlength_app in Hbl. rewrite Zlength_sublist in Hbl by list_solve.
          rewrite Zlength_Zrepeat in Hbl by list_solve. lia. }
        assert (b = Zlength (csr_row_ptr csr) + 1) by lia. clear H4 H5.
        rewrite Zlength_sublist by list_solve.
        rewrite Zlength_Zrepeat by list_solve.
        assert ((b - 1 - (r + 1 - 0) - (Zlength (csr_row_ptr csr) - (r + 1)) = 0)) by lia.
        rewrite H4. rewrite Znth_0_cons.
        specialize (H1 (a-1) (a-1)).
        destruct H1. split; [lia|list_solve].
        rewrite Znth_sublist by list_solve. replace (a-1+0) with (a-1) by lia. exact H5. }
      (* a second to last *)
      assert (a > r + 1) by lia. clear Ear.
      destruct (a-r-2 <? Zlength (csr_row_ptr csr) - (r + 1)) eqn:Ear.
      { (* a is not the last element *)
        assert (Znth a (0 :: (sublist 0 (r + 1) (csr_row_ptr csr) ++
          Zrepeat (cd_upto_coog i coog + 1) (Zlength (csr_row_ptr csr) - (r + 1))) ++ [Int.max_unsigned])
          = cd_upto_coog i coog + 1).
        { rewrite Znth_pos_cons by list_solve.
          rewrite <- app_assoc. rewrite Znth_app2 by list_solve.
          rewrite Znth_app1 by list_solve.
          rewrite Znth_Zrepeat by list_solve. reflexivity. }
        rewrite H3. clear H3.
        destruct (b-r-2 <? Zlength (csr_row_ptr csr) - (r + 1)) eqn:Ebr.
        { (* b is not the last element *)
          assert (b > r + 1) by list_solve.
          assert (Znth b (0 :: (sublist 0 (r + 1) (csr_row_ptr csr) ++
            Zrepeat (cd_upto_coog i coog + 1) (Zlength (csr_row_ptr csr) - (r + 1))) ++ [Int.max_unsigned])
             = cd_upto_coog i coog + 1).
          { rewrite Znth_pos_cons by list_solve.
            rewrite <- app_assoc. rewrite Znth_app2 by list_solve.
            rewrite Znth_app1 by list_solve.
            rewrite Znth_Zrepeat by list_solve. reflexivity. }
          rewrite H4. clear H4. lia. }
        (* b is the last element *)
        assert (b >= Zlength (csr_row_ptr csr) +1 ) by lia. clear Ebr.
        rewrite <- app_assoc by list_solve. 
        rewrite Znth_pos_cons by list_solve. 
        rewrite Znth_app2 by list_solve.
        rewrite Znth_app2 by list_solve.
        assert (b <= Zlength ((csr_row_ptr csr)) + 1).
        { rewrite Zlength_cons, Zlength_app, Zlength_cons, Zlength_nil in Hbl.
          simpl in Hbl. unfold new_row_ptr in Hbl. simpl in Hbl.
          rewrite Zlength_app in Hbl. rewrite Zlength_sublist in Hbl by list_solve.
          rewrite Zlength_Zrepeat in Hbl by list_solve. lia. }
        assert (b = Zlength (csr_row_ptr csr) + 1) by lia. clear H3 H4.
        rewrite Zlength_sublist by list_solve.
        rewrite Zlength_Zrepeat by list_solve.
        assert ((b - 1 - (r + 1 - 0) - (Zlength (csr_row_ptr csr) - (r + 1)) = 0)) by lia.
        rewrite H3. rewrite Znth_0_cons.
        rewrite Hcd_incr. pose proof (count_distinct_mono (coog_entries coog) (i+1)).
        unfold cd_upto_coog. lia. }
      (* a is the last element *)
      assert (a >= Zlength (csr_row_ptr csr) + 1) by lia. clear Ear.
      rewrite Zlength_cons in Hbl by list_solve.
      rewrite Zlength_app in Hbl by list_solve.
      unfold csr', new_row_ptr in Hbl. simpl in Hbl.
      rewrite Zlength_app in Hbl by list_solve.
      rewrite Zlength_sublist in Hbl by list_solve.
      rewrite Zlength_Zrepeat in Hbl by list_solve.
      rewrite Zlength_cons, Zlength_nil in Hbl by list_solve.
      replace (Z.succ (r + 1 - 0 + (Zlength (csr_row_ptr csr) - (r + 1)) + Z.succ 0)) 
        with (Zlength (csr_row_ptr csr) + 2) in Hbl by lia.
      assert (a = Zlength (csr_row_ptr csr) + 1) by lia.
      assert (b = Zlength (csr_row_ptr csr) + 1) by lia.
      rewrite H4, H5. lia.
    - (* CSR_wf_rowsorted *)
      replace (csr_rows csr') with (csr_rows csr) by (unfold csr', csr_rows; simpl; list_solve).
      intros r0 Hr0. pose proof (CSR_wf_rowsorted r0 Hr0) as Hrowr0.
      assert (Hcol_ind_len: Zlength (csr_col_ind csr) = cd_upto_coog i coog).
      { rewrite <-CSR_wf_vals.
        Search (Zlength (csr_vals _)).
        inversion_clear partial_CSRG_coog_csr.
        rewrite coog_csr_vals. unfold cd_upto_coog.
        unfold coog_upto. simpl. lia. }
      destruct (r0 <? r) eqn:Er0r.
      { (* r0 < r *)
        assert (r0 < r) by lia; clear Er0r.
        unfold csr', new_row_ptr; simpl.
        rewrite Znth_app1 by list_solve. rewrite Znth_sublist by list_solve.
        replace (r0 + 0) with r0 by lia.
        rewrite Znth_app1 by list_solve. rewrite Znth_sublist by list_solve.
        replace (r0 + 1 + 0) with (r0 + 1) by lia.
        rewrite sublist_app1 by list_solve.
        assert ((sublist 0 (cd_upto_coog i coog) (csr_col_ind csr)) = csr_col_ind csr) by list_solve.
        rewrite H2. auto. }
      destruct (r0 >? r) eqn:Err0.
      { (* r > r0 *)
        assert (r0 > r) by lia; clear Err0.
        unfold csr', new_row_ptr; simpl.
        rewrite sublist_over by list_solve.
        replace (-1 :: [] ++ [csr_cols csr]) with (-1 :: (csr_cols csr) :: nil) by list_solve.
        apply sorted_cons; [lia |]. apply sorted_1. }
      assert (r = r0) by lia. clear Er0r Err0. subst r0.
      unfold csr', new_row_ptr; simpl.
      rewrite Znth_app1 by list_solve.
      rewrite Znth_sublist by list_solve. replace (r+0) with r by lia.
      rewrite Znth_app2 by list_solve.
      rewrite Zlength_sublist by list_solve.
      replace (r + 1 - (r + 1 - 0)) with 0 by lia.
      rewrite Znth_Zrepeat by lia.
      replace (sublist 0 (cd_upto_coog i coog) (csr_col_ind csr)) with (csr_col_ind csr) by list_solve.
      replace (sublist (Znth r (csr_row_ptr csr)) (cd_upto_coog i coog + 1) (csr_col_ind csr ++ [c]))
        with (sublist (Znth r (csr_row_ptr csr)) (Znth (r + 1) (csr_row_ptr csr)) (csr_col_ind csr) ++ [c]).
      2:{ rewrite sublist_app' by list_solve.
          rewrite Hcol_ind_len. rewrite sublist_0_cons by list_solve.
          replace (cd_upto_coog i coog + 1 - cd_upto_coog i coog - 1) with 0 by lia.
          rewrite sublist_of_nil. rewrite app_inv_tail_iff.
          (* rewrite <- Hcol_ind_len. *)
          inversion_clear partial_CSRG_coog_csr.
          unfold entries_correspond_coog in coog_csr_entries.
          specialize (coog_csr_entries (i-1)).
          spec coog_csr_entries. unfold coog_upto. simpl. list_solve.
          destruct (Znth (i - 1) (coog_entries (coog_upto i coog))) as [r0 c0] eqn:Er0c0.
          unfold coog_upto in Er0c0. simpl in Er0c0. rewrite Znth_sublist in Er0c0 by list_solve.
          replace (i-1+0) with (i-1) in Er0c0 by lia.
          rewrite Er0c0 in Hrow. simpl in Hrow. subst r0.
          replace (i-1+1) with i in coog_csr_entries by lia.
          assert (Zlength (csr_col_ind csr) <= Znth (r+1) (csr_row_ptr csr)).
          { rewrite Hcol_ind_len. replace (cd_upto_coog i coog) with (cd_upto_coog i (coog_upto i coog)).
            lia. unfold coog_upto, cd_upto_coog; simpl.
            rewrite sublist_sublist00; lia. }
          rewrite <- Hcol_ind_len.
          rewrite sublist_longer; auto. }
      apply sorted_i; [unfold Transitive; lia|].
      intros a b Hab Hbl.
      destruct (a =? 0) eqn:Ea0.
      { (* a = 0 *)
        assert (a = 0) by lia. subst a.
        replace (Znth 0 (-1 :: (sublist (Znth r (csr_row_ptr csr)) 
          (Znth (r + 1) (csr_row_ptr csr)) (csr_col_ind csr) ++ [c]) ++ [csr_cols csr]))
          with (-1) by list_solve.
        assert (b > 0) by lia.
        Search "sorted" "app".
          


        (* Search (count_distinct (sublist _ _ _)).
        pose proof (count_distinct_mono (coog_entries coog) i). *)
        
          
        
          




      (* list_solver.sorted =
fun (A : Type) (d : Inhabitant A) (le : A -> A -> Prop) (l : list A) =>
forall i j : Z, 0 <= i <= j /\ j < Zlength l -> le (Znth i l) (Znth j l)
     : forall {A : Type}, Inhabitant A -> (A -> A -> Prop) -> list A -> Prop *)
      
      (* Useful lemmas *)
      pose proof @sorted_i.
      pose proof @sorted_e.





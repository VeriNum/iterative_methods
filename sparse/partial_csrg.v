Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse_model distinct partial_csr.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

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




Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import build_csr sparse_model spec_sparse spec_build_csr.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Build_CSR_ASI ++ SparseASI ++ MathASI.



Lemma body_coo_to_csr_matrix: semax_body Vprog Gprog f_coo_to_csr_matrix coo_to_csr_matrix_spec.
Proof.
start_function.
unfold coo_rep.
Intros r c n maxn rp cp vp.
forward.
assert_PROP (n = Zlength (coo_entries coo))
  by (entailer!; list_solve).
forward_call (sh,coo,p,0,n).
  unfold coo_rep; Exists r c n maxn rp cp vp; entailer!!.
Intros coo'.
generalize H5; intros [? [? ?]].
generalize H9; intro.
apply Permutation_Zlength in H10.
autorewrite with sublist in H6.
forward_call.
eapply coo_matrix_wellformed_equiv; eauto.
set (k := coo_count_distinct _).
forward_call (Tstruct _csr_matrix noattr, gv).
Intros q.
forward_call (tarray tdouble k, gv).
 entailer!!.
  simpl. do 3 f_equal. admit.
  simpl. admit.
Intros val_p.
forward.
forward_call (tarray tuint k, gv).
  entailer!!.
  simpl. do 3 f_equal. admit.
  simpl. admit.
Intros colind_p.
forward.
forward.
forward_call (tarray tuint (r0+1), gv).
  entailer!!.
  simpl. do 3 f_equal. admit.
  simpl. admit.
Intros rowptr_p.
forward.
forward.
forward.

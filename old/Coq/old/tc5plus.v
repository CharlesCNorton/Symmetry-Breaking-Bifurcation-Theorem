Require Import Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition α : R := 1.

Lemma α_nonzero : α <> 0.
Proof.
  unfold α. (* α is 1 *)
  apply R1_neq_R0.
Qed.

Lemma unique_root : forall T:R, α*(T - 0.5) = 0 -> T = 0.5.
Proof.
  intros T H.
  apply Rmult_integral in H.
  destruct H as [Hαeq | HTeq].
  - exfalso. apply α_nonzero. exact Hαeq.
  - unfold Rminus in HTeq.
    apply Rminus_diag_uniq in HTeq.
    exact HTeq.
Qed.

Definition t_c : R := 0.5.

Lemma t_c_in_interval : 0 <= t_c <= 1.
Proof.
  unfold t_c. split; lra.
Qed.

Definition ε : R := 0.1.

Lemma epsilon_in_interval : 0 < ε < 1.
Proof.
  unfold ε. split; lra.
Qed.

Definition regularizedBase (t : R) : R := t - t_c + ε.

Lemma regularizedBase_pos :
  forall t : R,
    t_c <= t ->
    0 < regularizedBase t.
Proof.
  intros t Hge.
  unfold regularizedBase, t_c, ε in *.
  lra.
Qed.
Require Import Reals.
Open Scope R_scope.

(* Define α as a known nonzero real number, e.g., 1 *)
Definition α : R := 1.

(* Prove that α is nonzero using the known fact that 1 <> 0 *)
Lemma α_nonzero : α <> 0.
Proof.
  unfold α. (* α is 1 *)
  apply R1_neq_R0. (* From Coq's standard library: 1 <> 0 *)
Qed.

(* Now α and α_nonzero are fully proven facts, not assumptions. *)
Lemma unique_root : forall T:R, α*(T - 0.5) = 0 -> T = 0.5.
Proof.
  intros T H.
  apply Rmult_integral in H.
  destruct H as [Hαeq | HTeq].
  - (* Case α=0 *)
    exfalso. apply α_nonzero. exact Hαeq.
  - (* Case T-0.5=0 *)
    unfold Rminus in HTeq.
    apply Rminus_diag_uniq in HTeq.
    exact HTeq.
Qed.

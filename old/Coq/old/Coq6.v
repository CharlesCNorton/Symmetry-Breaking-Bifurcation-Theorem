Require Import Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Reals.Rpower.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Reals.RIneq.  (* for ln_increasing, ln_1, etc. *)
Require Import Lia.              (* NEW import for the 'lia' tactic *)

Open Scope R_scope.

Definition α : R := 1.

Lemma α_nonzero : α <> 0.
Proof.
  unfold α.
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

Definition A : R := 2.

Lemma A_pos : 0 < A.
Proof.
  unfold A. lra.
Qed.

Definition k : R := 0.7.

Lemma k_pos : 0 < k.
Proof.
  unfold k. lra.
Qed.

Definition B : R := 1.2.

Lemma B_pos : 0 < B.
Proof.
  unfold B. lra.
Qed.

Definition C : R := 0.3.

Lemma C_pos : 0 < C.
Proof.
  unfold C. lra.
Qed.

Definition n : nat := 6.

Lemma n_min : (2 <= n)%nat.
Proof.
  unfold n.
  auto.
Qed.

Definition nR : R := INR n.

Lemma nR_pos : 0 < nR.
Proof.
  unfold nR, n.
  apply lt_0_INR.
  auto with arith.
Qed.

Lemma Rpower_pos : forall x y : R, 0 < x -> 0 < Rpower x y.
Proof.
  intros x y H.
  unfold Rpower.
  apply exp_pos.
Qed.

Definition DeltaG (t : R) : R :=
  if Rle_dec t t_c then 0
  else (A / Rpower nR k) * Rpower (regularizedBase t) (B + C).

Lemma DeltaG_zero_up_to_t_c :
  forall t : R,
    t <= t_c ->
    DeltaG t = 0.
Proof.
  intros t Hle.
  unfold DeltaG.
  destruct (Rle_dec t t_c).
  - reflexivity.
  - lra.
Qed.

Lemma DeltaG_pos_after_t_c :
  forall t : R,
    t_c < t ->
    0 < DeltaG t.
Proof.
  intros t Hgt.
  unfold DeltaG.
  destruct (Rle_dec t t_c).
  - lra.
  - unfold A, nR, k, regularizedBase, B, C, t_c, ε in *.
    apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * lra.       (* 0 < A *)
      * apply Rpower_pos. apply nR_pos.
    + apply Rpower_pos. lra.
Qed.

Theorem DeltaG_piecewise_bifurcation :
  forall t : R,
    0 <= t <= 1 ->
    (if Rle_dec t t_c then DeltaG t = 0 else 0 < DeltaG t).
Proof.
  intros t [Hlow Hhigh].
  destruct (Rle_dec t t_c).
  - rewrite (DeltaG_zero_up_to_t_c t r). reflexivity.
  - apply DeltaG_pos_after_t_c. lra.
Qed.

Lemma ln_1_zero : 0 = ln 1.
Proof.
  apply eq_sym.
  apply ln_1.
Qed.

(* We avoid rewriting directly in 0< ln x. Instead, we build an assertion ln 1 < ln x. *)
Lemma ln_gt_1 : forall x : R, 1 < x -> 0 < ln x.
Proof.
  intros x Hx.
  assert (Hln: ln 1 < ln x).
  { apply ln_increasing; [lra | exact Hx]. }
  rewrite <- ln_1_zero in Hln.
  exact Hln.
Qed.

Definition k_log : R := ln nR.

Lemma k_log_pos :
  (2 <= n)%nat ->
  0 < k_log.
Proof.
  intros Hn.
  unfold k_log, nR.
  apply ln_gt_1.
  assert (1 < n)%nat by lia.  
  apply lt_INR in H.
  exact H.
Qed.

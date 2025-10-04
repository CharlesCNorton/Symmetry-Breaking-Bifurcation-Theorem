Require Import Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Reals.Rpower.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Reals.RIneq.  
Require Import Lia.              

Open Scope R_scope.

(*************************************************************)
(*  1) Basic Real Constants and Lemmas                       *)
(*************************************************************)

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

(*************************************************************)
(*  2) Threshold t_c and Epsilon                             *)
(*************************************************************)

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

(*************************************************************)
(*  3) A Regularized Base Term: (t - t_c + ε)                *)
(*************************************************************)

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

(*************************************************************)
(*  4) Simple Constants A, k, B, C, plus integer n            *)
(*************************************************************)

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
  unfold n. auto.
Qed.

Definition nR : R := INR n.
Lemma nR_pos : 0 < nR.
Proof.
  unfold nR, n.
  apply lt_0_INR.
  auto with arith.
Qed.

(*************************************************************)
(*  5) Rpower Positivity                                      *)
(*************************************************************)

Lemma Rpower_pos : forall x y : R, 0 < x -> 0 < Rpower x y.
Proof.
  intros x y H.
  unfold Rpower.
  apply exp_pos.
Qed.

(*************************************************************)
(*  6) The Piecewise DeltaG(t) and Main Proofs                *)
(*************************************************************)

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
      * lra.                   (* 0 < A *)
      * apply Rpower_pos. apply nR_pos.
    + apply Rpower_pos. lra.   (* 0 < (t - t_c + ε)^(B + C) *)
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

(*************************************************************)
(*  7) ln(1)=0 and ln_gt_1 for x>1 => ln(x)>0                *)
(*************************************************************)

Lemma ln_1_zero : 0 = ln 1.
Proof.
  apply eq_sym.
  apply ln_1.  (* from RIneq, which states ln(1)=0 *)
Qed.

Lemma ln_gt_1 : forall x : R, 1 < x -> 0 < ln x.
Proof.
  intros x Hx.
  assert (Hln: ln 1 < ln x).
  { apply ln_increasing; [lra | exact Hx]. }
  rewrite <- ln_1_zero in Hln.
  exact Hln.
Qed.

(*************************************************************)
(*  8) A Logarithmic k: k_log = ln(nR).                       *)
(*************************************************************)

Definition k_log : R := ln nR.

Lemma k_log_pos :
  (2 <= n)%nat ->
  0 < k_log.
Proof.
  intros Hn0.
  unfold k_log, nR.
  apply ln_gt_1.
  assert (1 < n)%nat by lia.
  apply lt_INR in H.
  exact H.
Qed.

(*************************************************************)
(*  9) Dimension d => param-based approach for (k,B,C).       *)
(*************************************************************)

Definition d : nat := 3.
Lemma d_min : (2 <= d)%nat.
Proof.
  unfold d. auto.
Qed.

Parameter k_fun : nat -> R.
Parameter B_fun : nat -> R.
Parameter C_fun : nat -> R.

Definition k_d : R := k_fun d.
Definition B_d : R := B_fun d.
Definition C_d : R := C_fun d.

Parameter k_d_pos : 0 < k_d.
Parameter B_d_pos : 0 < B_d.
Parameter C_d_pos : 0 < C_d.

(*************************************************************)
(* 10) Dimension-based complexity n_fun => n_d => nR_d       *)
(*************************************************************)

Parameter n_fun : nat -> nat.

Definition n_d : nat := n_fun d.

Parameter n_d_min : (2 <= n_d)%nat.

Definition nR_d : R := INR n_d.

Parameter nR_d_pos : 0 < nR_d.

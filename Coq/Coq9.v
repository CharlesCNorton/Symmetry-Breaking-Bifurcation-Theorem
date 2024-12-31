Require Import Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Reals.Rpower.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Reals.RIneq.  (* for ln_increasing, ln_1, etc. *)
Require Import Lia.              (* for the 'lia' tactic *)

Open Scope R_scope.

Parameter A_fun : nat -> R.
Parameter k_fun : nat -> R.
Parameter B_fun : nat -> R.
Parameter C_fun : nat -> R.

Parameter n_fun : nat -> nat.

Parameter dimension_complexity_pos : forall d : nat,
  (2 <= d)%nat ->
  (2 <= n_fun d)%nat ->
  0 < A_fun d /\
  0 < k_fun d /\
  0 < B_fun d /\
  0 < C_fun d /\
  0 < INR (n_fun d).

Parameter euler_fun : nat -> Z.
Parameter c_1 : R.
Parameter c_1_pos : 0 < c_1.

Definition C_prime_d (d : nat) : R :=
  C_fun d
    + c_1
      * (IZR (euler_fun d) / ln (INR (n_fun d))).

Definition ε : R := 0.1.

Lemma epsilon_in_interval : 0 < ε < 1.
Proof.
  unfold ε. split; lra.
Qed.

Definition t_c : R := 0.5.
Lemma t_c_in_interval : 0 <= t_c <= 1.
Proof.
  unfold t_c. split; lra.
Qed.

Definition regularizedBase (t : R) : R := t - t_c + ε.

Lemma regularizedBase_pos :
  forall t : R, t_c <= t -> 0 < regularizedBase t.
Proof.
  intros t Ht.
  unfold regularizedBase, t_c, ε in *.
  lra.
Qed.

Lemma ln_1_eq : 0 = ln 1.
Proof.
  apply eq_sym.
  apply ln_1.
Qed.

Lemma ln_gt_1 : forall x : R, 1 < x -> 0 < ln x.
Proof.
  intros x Hx.
  assert (Hln: ln 1 < ln x).
  { apply ln_increasing; [lra | exact Hx]. }
  rewrite <- ln_1_eq in Hln.
  exact Hln.
Qed.

Lemma Rpower_pos : forall x y : R, 0 < x -> 0 < Rpower x y.
Proof.
  intros x y Hx.
  unfold Rpower.
  apply exp_pos.
Qed.

Definition DeltaG_d (t : R) (d : nat) : R :=
  if Rle_dec t t_c then 0
  else
    let A_d := A_fun d in
    let k_d := k_fun d in
    let B_d := B_fun d in
    let C_d := C_fun d in
    let n_d := n_fun d in
    (A_d / Rpower (INR n_d) k_d)
      * Rpower (regularizedBase t)
               (B_d * ln (INR n_d) + C_d).

Lemma DeltaG_d_zero_up_to_t_c :
  forall (t : R) (d : nat),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    t <= t_c ->
    DeltaG_d t d = 0.
Proof.
  intros t d Hd Hn Hle.
  unfold DeltaG_d.
  destruct (Rle_dec t t_c).
  - reflexivity.
  - lra.
Qed.

Lemma DeltaG_d_pos_after_t_c :
  forall (t : R) (d : nat),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    t_c < t ->
    0 < DeltaG_d t d.
Proof.
  intros t d Hd Hn Hgt.
  unfold DeltaG_d.
  destruct (Rle_dec t t_c).
  - lra.
  - pose proof (dimension_complexity_pos d Hd Hn)
      as [HAd [Hkd [HBd [HCd HnR]]]].
    apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * exact HAd.    (* 0 < A_fun d *)
      * apply Rpower_pos. exact HnR.
    + apply Rpower_pos.
      unfold regularizedBase, t_c, ε in *.
      lra.
Qed.

Theorem SymmetryBreaking_piecewise_d :
  forall (d : nat) (t : R),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    0 <= t <= 1 ->
    (if Rle_dec t t_c then DeltaG_d t d = 0 else 0 < DeltaG_d t d).
Proof.
  intros d t Hd Hn [Hlow Hhigh].
  destruct (Rle_dec t t_c).
  - rewrite (DeltaG_d_zero_up_to_t_c t d Hd Hn r). reflexivity.
  - apply DeltaG_d_pos_after_t_c; auto. lra.
Qed.

Definition DeltaG_prime_d (t : R) (d : nat) : R :=
  if Rle_dec t t_c then 0
  else
    let A_d := A_fun d in
    let k_d := k_fun d in
    let B_d := B_fun d in
    let n_d := n_fun d in
    (A_d / Rpower (INR n_d) k_d)
      * Rpower (regularizedBase t)
               (B_d * ln (INR n_d) + C_prime_d d).

Lemma DeltaG_prime_d_zero_up_to_t_c :
  forall (t : R) (d : nat),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    t <= t_c ->
    DeltaG_prime_d t d = 0.
Proof.
  intros t d Hd Hn Hle.
  unfold DeltaG_prime_d.
  destruct (Rle_dec t t_c).
  - reflexivity.
  - lra.
Qed.

Lemma DeltaG_prime_d_pos_after_t_c :
  forall (t : R) (d : nat),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    t_c < t ->
    0 < DeltaG_prime_d t d.
Proof.
  intros t d Hd Hn Hgt.
  unfold DeltaG_prime_d.
  destruct (Rle_dec t t_c).
  - lra.
  - (* Retrieve positivity from dimension_complexity_pos. *)
    pose proof (dimension_complexity_pos d Hd Hn)
      as [HAd [Hkd [HBd [HCd HnR]]]].
    apply Rmult_lt_0_compat.
    + (* A_fun(d) / (INR(n_fun(d))^k_fun(d)) > 0 *)
      apply Rdiv_lt_0_compat.
      * exact HAd.  (* 0 < A_fun d *)
      * apply Rpower_pos. exact HnR.
    + (* (t - t_c + ε) ^ (B_fun(d)*ln(...) + C_prime_d(d)) > 0 *)
      apply Rpower_pos.
      unfold regularizedBase, t_c, ε in *.
      lra.
Qed.

Theorem SymmetryBreaking_prime_piecewise_d :
  forall (d : nat) (t : R),
    (2 <= d)%nat ->
    (2 <= n_fun d)%nat ->
    0 <= t <= 1 ->
    (if Rle_dec t t_c then DeltaG_prime_d t d = 0
     else 0 < DeltaG_prime_d t d).
Proof.
  intros d t Hd Hn [Hlow Hhigh].
  destruct (Rle_dec t t_c).
  - rewrite (DeltaG_prime_d_zero_up_to_t_c t d Hd Hn r). reflexivity.
  - apply DeltaG_prime_d_pos_after_t_c; auto. lra.
Qed.
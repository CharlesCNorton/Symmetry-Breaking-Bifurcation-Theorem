Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import Classical.
Require Import Reals.Rpower.
Require Import Reals.Rtrigo_def.
Require Import Reals.Ranalysis5.
Require Import Psatz.

Open Scope R_scope.

Definition positive_real (r : R) : Prop := r > 0.

Record GeometricObject : Type := {
  complexity : nat;
  dimension : nat;
  complexity_ge_3 : (complexity >= 3)%nat;
  dimension_ge_2 : (dimension >= 2)%nat;
  dimension_le_4 : (dimension <= 4)%nat
}.

Definition deformation_parameter : Type := { t : R | 0 <= t <= 1 }.

Definition make_deformation (t : R) (H0 : 0 <= t) (H1 : t <= 1) : deformation_parameter :=
  exist _ t (conj H0 H1).

Definition critical_threshold : R := 0.5.

Lemma critical_threshold_valid : 0 <= critical_threshold <= 1.
Proof.
  unfold critical_threshold.
  lra.
Qed.

Record SymmetryGroup : Type := {
  group_carrier : Type;
  group_size : nat;
  group_size_pos : (group_size > 0)%nat
}.

Record IsotropySubgroup (G : SymmetryGroup) (t : deformation_parameter) : Type := {
  isotropy_carrier : Type;
  isotropy_size : nat;
  isotropy_subgroup : (isotropy_size <= group_size G)%nat
}.

Definition expected_isotropy_size (G : SymmetryGroup) (t : deformation_parameter)
  (H : IsotropySubgroup G t) : R := INR (isotropy_size G t H).

Definition delta_G (G : SymmetryGroup) (t : deformation_parameter)
  (H : IsotropySubgroup G t) : R :=
  INR (group_size G) - expected_isotropy_size G t H.

Lemma delta_G_nonneg : forall (G : SymmetryGroup) (t : deformation_parameter)
  (H : IsotropySubgroup G t),
  delta_G G t H >= 0.
Proof.
  intros G t H.
  unfold delta_G, expected_isotropy_size.
  assert (isotropy_size G t H <= group_size G)%nat as Hle.
  { destruct H as [carrier size subgroup_proof]. simpl. exact subgroup_proof. }
  assert (INR (isotropy_size G t H) <= INR (group_size G)) as HleR.
  { apply le_INR. exact Hle. }
  lra.
Qed.

Definition safe_ln (n : nat) : R :=
  if (n <=? 1)%nat then 0 else ln (INR n).

Definition epsilon : R := 0.05.

Lemma epsilon_pos : epsilon > 0.
Proof.
  unfold epsilon.
  lra.
Qed.

Definition A_d (obj : GeometricObject) (G : SymmetryGroup) : R :=
  INR (group_size G).

Definition k_d (obj : GeometricObject) : R :=
  safe_ln (complexity obj).

Definition B_d (obj : GeometricObject) (geom_measure : R) : R :=
  let n := complexity obj in
  let ln_n := safe_ln n in
  (1 / geom_measure) * ln_n * ln_n + (0.1 + 0.01 * ln_n).

Definition C_d (obj : GeometricObject) (euler_char : Z) : R :=
  match dimension obj with
  | 2 => 2.23
  | 3 => 1.77
  | 4 => 1.0 + 0.1 * (IZR euler_char / safe_ln (complexity obj))
  | _ => 1.0
  end.

Definition bifurcation_exponent (obj : GeometricObject) (geom_measure : R)
  (euler_char : Z) : R :=
  B_d obj geom_measure * safe_ln (complexity obj) + C_d obj euler_char.

Definition bifurcation_base (t : deformation_parameter) : R :=
  let t_val := proj1_sig t in
  t_val - critical_threshold + epsilon.

Definition delta_G_bifurcation (obj : GeometricObject) (G : SymmetryGroup)
  (t : deformation_parameter) (geom_measure : R) (euler_char : Z) : R :=
  let t_val := proj1_sig t in
  if Rle_dec t_val critical_threshold then 0
  else
    let A := A_d obj G in
    let k := k_d obj in
    let base := bifurcation_base t in
    let exp_val := bifurcation_exponent obj geom_measure euler_char in
    (A / Rpower (INR (complexity obj)) k) * Rpower base exp_val.

Lemma pre_bifurcation_no_symmetry_breaking :
  forall (obj : GeometricObject) (G : SymmetryGroup)
    (t : deformation_parameter) (geom_measure : R) (euler_char : Z),
  proj1_sig t <= critical_threshold ->
  delta_G_bifurcation obj G t geom_measure euler_char = 0.
Proof.
  intros obj G t geom_measure euler_char Hle.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig t) critical_threshold) as [Hle'|Hgt].
  - reflexivity.
  - exfalso. apply Hgt. exact Hle.
Qed.

Lemma epsilon_positive : 0 < epsilon.
Proof.
  unfold epsilon.
  nra.
Qed.

Lemma bifurcation_base_positive :
  forall t : deformation_parameter,
  proj1_sig t > critical_threshold ->
  bifurcation_base t > 0.
Proof.
  intros t Hgt.
  unfold bifurcation_base.
  destruct t as [t_val Ht]. simpl in *.
  unfold Rgt in *.
  apply Rlt_0_minus in Hgt.
  apply Rplus_lt_0_compat.
  - exact Hgt.
  - apply epsilon_positive.
Qed.

Lemma post_bifurcation_nonneg :
  forall (obj : GeometricObject) (G : SymmetryGroup)
    (t : deformation_parameter) (geom_measure : R) (euler_char : Z),
  geom_measure > 0 ->
  proj1_sig t > critical_threshold ->
  delta_G_bifurcation obj G t geom_measure euler_char >= 0.
Proof.
  intros obj G t geom_measure euler_char Hgm Hgt.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig t) critical_threshold) as [Hle|Hgt'].
  - lra.
  - assert (Hbase : bifurcation_base t > 0).
    { apply bifurcation_base_positive. exact Hgt. }
    assert (HA : A_d obj G > 0).
    { unfold A_d. apply lt_0_INR.
      destruct G as [carr sz pos]. simpl. lia. }
    assert (Hcomplexity : INR (complexity obj) > 0).
    { apply lt_0_INR. destruct obj as [c d c3 d2 d4]. simpl. lia. }
    assert (Hpow1 : Rpower (INR (complexity obj)) (k_d obj) > 0).
    { apply exp_pos. }
    assert (Hpow2 : Rpower (bifurcation_base t)
                     (bifurcation_exponent obj geom_measure euler_char) >= 0).
    { apply Rle_ge. apply Rle_trans with (r2 := 0).
      - right. reflexivity.
      - left. apply exp_pos. }
    assert (Hdiv : A_d obj G / Rpower (INR (complexity obj)) (k_d obj) >= 0).
    { apply Rle_ge. apply Rlt_le. apply Rdiv_lt_0_compat. lra. lra. }
    nra.
Qed.

Theorem symmetry_breaking_bifurcation_theorem :
  forall (obj : GeometricObject) (G : SymmetryGroup)
    (t : deformation_parameter) (H : IsotropySubgroup G t)
    (geom_measure : R) (euler_char : Z),
  geom_measure > 0 ->
  delta_G G t H = delta_G_bifurcation obj G t geom_measure euler_char ->
  (proj1_sig t <= critical_threshold -> delta_G G t H = 0) /\
  (proj1_sig t > critical_threshold -> delta_G G t H >= 0).
Proof.
  intros obj G t H geom_measure euler_char Hgm Heq.
  split.
  - intros Hle.
    rewrite Heq.
    apply pre_bifurcation_no_symmetry_breaking.
    exact Hle.
  - intros Hgt.
    rewrite Heq.
    apply post_bifurcation_nonneg.
    + exact Hgm.
    + exact Hgt.
Qed.

Definition square_example : GeometricObject.
Proof.
  refine {| complexity := 4; dimension := 2 |}.
  - lia.
  - lia.
  - lia.
Defined.

Definition square_symmetry_group : SymmetryGroup.
Proof.
  refine {| group_carrier := unit; group_size := 8 |}.
  lia.
Defined.

Lemma square_bifurcation_example :
  forall (t : deformation_parameter) (H : IsotropySubgroup square_symmetry_group t),
  let geom_measure := 4 in
  let euler_char := 0%Z in
  proj1_sig t > critical_threshold ->
  delta_G_bifurcation square_example square_symmetry_group t geom_measure euler_char >= 0.
Proof.
  intros t H geom_measure euler_char Hgt.
  apply post_bifurcation_nonneg.
  - unfold geom_measure. nra.
  - exact Hgt.
Qed.

Definition t_06_lower : 0 <= 3/5.
Proof. nra. Qed.

Definition t_06_upper : 3/5 <= 1.
Proof. nra. Qed.

Definition deformation_06 : deformation_parameter :=
  make_deformation (3/5) t_06_lower t_06_upper.

Lemma t_06_past_threshold : proj1_sig deformation_06 > critical_threshold.
Proof.
  unfold deformation_06, make_deformation, critical_threshold.
  simpl. nra.
Qed.

Lemma square_nonneg_breaking_at_t_06 :
  forall (H : IsotropySubgroup square_symmetry_group deformation_06),
  delta_G_bifurcation square_example square_symmetry_group deformation_06 4 0%Z >= 0.
Proof.
  intros H.
  apply post_bifurcation_nonneg.
  - lra.
  - apply t_06_past_threshold.
Qed.

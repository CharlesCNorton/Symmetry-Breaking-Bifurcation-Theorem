Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import Classical.
Require Import Reals.Rpower.
Require Import Reals.Rtrigo_def.
Require Import Reals.Ranalysis5.
Require Import Psatz.

Open Scope R_scope.

(** Predicate for strictly positive reals *)
Definition positive_real (r : R) : Prop := r > 0.

(** Geometric object with complexity n ≥ 3, dimension d ∈ {2,3,4} *)
Record GeometricObject : Type := {
  complexity : nat;
  dimension : nat;
  complexity_ge_3 : (complexity >= 3)%nat;
  dimension_ge_2 : (dimension >= 2)%nat;
  dimension_le_4 : (dimension <= 4)%nat
}.

(** Deformation parameter t ∈ [0,1] *)
Definition deformation_parameter : Type := { t : R | 0 <= t <= 1 }.

(** Constructor for deformation parameter from bounds *)
Definition make_deformation (t : R) (H0 : 0 <= t) (H1 : t <= 1) : deformation_parameter :=
  exist _ t (conj H0 H1).

(** Bifurcation threshold t_c = 0.5 *)
Definition critical_threshold : R := 0.5.

(** Bifurcation threshold lies in unit interval *)
Lemma critical_threshold_valid : 0 <= critical_threshold <= 1.
Proof.
  unfold critical_threshold.
  lra.
Qed.

(** Symmetry group G with carrier and positive size |G| *)
Record SymmetryGroup : Type := {
  group_carrier : Type;
  group_size : nat;
  group_size_pos : (group_size > 0)%nat
}.

(** Isotropy subgroup H(t) ⊆ G with |H(t)| ≤ |G| *)
Record IsotropySubgroup (G : SymmetryGroup) (t : deformation_parameter) : Type := {
  isotropy_carrier : Type;
  isotropy_size : nat;
  isotropy_subgroup : (isotropy_size <= group_size G)%nat
}.

(** Expected isotropy subgroup size E[|H(t)|] *)
Definition expected_isotropy_size (G : SymmetryGroup) (t : deformation_parameter)
  (H : IsotropySubgroup G t) : R := INR (isotropy_size G t H).

(** Symmetry loss ΔG(t) = |G| - E[|H(t)|] *)
Definition delta_G (G : SymmetryGroup) (t : deformation_parameter)
  (H : IsotropySubgroup G t) : R :=
  INR (group_size G) - expected_isotropy_size G t H.

(** ΔG(t) ≥ 0 by subgroup constraint *)
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

(** Natural logarithm with safe domain: ln(n) if n > 1, else 0 *)
Definition safe_ln (n : nat) : R :=
  if (n <=? 1)%nat then 0 else ln (INR n).

(** Regularization constant ε = 0.05 *)
Definition epsilon : R := 0.05.

(** ε > 0 *)
Lemma epsilon_pos : epsilon > 0.
Proof.
  unfold epsilon.
  lra.
Qed.

(** Symmetry group constant A_d = |G| *)
Definition A_d (obj : GeometricObject) (G : SymmetryGroup) : R :=
  INR (group_size G).

(** Complexity scaling constant k_d = ln(n) *)
Definition k_d (obj : GeometricObject) : R :=
  safe_ln (complexity obj).

(** Logarithmic deformation factor B_d = (1/μ)ln²(n) + 0.1 + 0.01·ln(n)
    where μ = geometric measure (perimeter for 2D, surface area for 3D, hypervolume for 4D) *)
Definition B_d (obj : GeometricObject) (geom_measure : R) : R :=
  let n := complexity obj in
  let ln_n := safe_ln n in
  (1 / geom_measure) * ln_n * ln_n + (0.1 + 0.01 * ln_n).

(** Dimensional adjustment constant C_d
    - 2D: 2.23 (from deformation rate calibration)
    - 3D: 1.77 (from eigenvalue analysis)
    - 4D: 1.0 + 0.1·χ/ln(n) (Euler characteristic correction) *)
Definition C_d (obj : GeometricObject) (euler_char : Z) : R :=
  match dimension obj with
  | 2 => 2.23
  | 3 => 1.77
  | 4 => 1.0 + 0.1 * (IZR euler_char / safe_ln (complexity obj))
  | _ => 1.0
  end.

(** A_d > 0 *)
Lemma A_d_positive : forall obj G, A_d obj G > 0.
Proof.
  intros obj G.
  unfold A_d.
  apply lt_0_INR.
  destruct G as [carrier size pos]. simpl. exact pos.
Qed.

(** k_d ≥ 0 *)
Lemma k_d_nonneg : forall obj, k_d obj >= 0.
Proof.
  intros obj.
  unfold k_d, safe_ln.
  destruct (complexity obj <=? 1)%nat eqn:E.
  - right. reflexivity.
  - left. assert (INR (complexity obj) > 1).
    { apply lt_1_INR.
      apply Nat.leb_gt in E. lia. }
    assert (ln 1 < ln (INR (complexity obj))).
    { apply ln_increasing; lra. }
    rewrite ln_1 in H0. exact H0.
Qed.

(** IZR 0 = 0 *)
Lemma IZR_0_eq : IZR 0 = 0.
Proof.
  reflexivity.
Qed.

(** IZR(0)/r = 0 for r > 0 *)
Lemma IZR_0_div_pos : forall r, r > 0 -> IZR 0 / r = 0.
Proof.
  intros r Hr.
  unfold Rdiv.
  replace (IZR 0) with 0 by apply IZR_0_eq.
  apply Rmult_0_l.
Qed.

(** χ > 0 and r > 0 implies χ/r > 0 *)
Lemma euler_pos_frac_pos : forall euler_char r,
  (euler_char > 0)%Z -> r > 0 -> IZR euler_char / r > 0.
Proof.
  intros euler_char r He Hr.
  apply Rdiv_lt_0_compat.
  - apply IZR_lt. lia.
  - exact Hr.
Qed.

(** χ < 0 and r > 0 implies χ/r < 0 *)
Lemma euler_neg_frac_neg : forall euler_char r,
  (euler_char < 0)%Z -> r > 0 -> IZR euler_char / r < 0.
Proof.
  intros euler_char r He Hr.
  assert (IZR euler_char < 0) by (apply IZR_lt; lia).
  assert (/ r > 0) by (apply Rinv_0_lt_compat; exact Hr).
  unfold Rdiv.
  nra.
Qed.

(** ln(n) > 0 for n > 1 *)
Lemma safe_ln_pos_or_zero : forall n, (n > 1)%nat -> safe_ln n > 0.
Proof.
  intros n Hn.
  unfold safe_ln.
  destruct (n <=? 1)%nat eqn:E.
  - apply Nat.leb_le in E. lia.
  - assert (INR n > 1).
    { apply lt_1_INR. lia. }
    assert (ln 1 < ln (INR n)).
    { apply ln_increasing; lra. }
    rewrite ln_1 in H0. exact H0.
Qed.

(** C_2 = 2.23 > 0 *)
Lemma C_d_2_positive : 2.23 > 0.
Proof.
  lra.
Qed.

(** C_3 = 1.77 > 0 *)
Lemma C_d_3_positive : 1.77 > 0.
Proof.
  lra.
Qed.

(** C_4 > 0 for non-negative Euler characteristic *)
Lemma C_d_4_positive : forall c euler_char,
  (c >= 3)%nat ->
  (euler_char >= 0)%Z ->
  1 + 0.1 * (IZR euler_char / safe_ln c) > 0.
Proof.
  intros c euler_char Hc Hepos.
  assert (Hln : safe_ln c > 0) by (apply safe_ln_pos_or_zero; lia).
  destruct (Z.eq_dec euler_char 0).
  - rewrite e. rewrite IZR_0_div_pos by exact Hln. lra.
  - assert (H: IZR euler_char / safe_ln c > 0).
    { apply euler_pos_frac_pos; [lia | exact Hln]. }
    assert (0.1 * (IZR euler_char / safe_ln c) > 0).
    { apply Rmult_lt_0_compat; lra. }
    lra.
Qed.

(** Bifurcation exponent B_d·ln(n) + C_d *)
Definition bifurcation_exponent (obj : GeometricObject) (geom_measure : R)
  (euler_char : Z) : R :=
  B_d obj geom_measure * safe_ln (complexity obj) + C_d obj euler_char.

(** Bifurcation base (t - t_c + ε) *)
Definition bifurcation_base (t : deformation_parameter) : R :=
  let t_val := proj1_sig t in
  t_val - critical_threshold + epsilon.

(** Bifurcation equation ΔG(t,n,d) with piecewise definition *)
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

(** Pre-bifurcation: ΔG = 0 for t ≤ t_c *)
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

(** ε > 0 (duplicate for visibility) *)
Lemma epsilon_positive : 0 < epsilon.
Proof.
  unfold epsilon.
  nra.
Qed.

(** Bifurcation base positive for t > t_c *)
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

(** Post-bifurcation: ΔG ≥ 0 for t > t_c *)
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

(** Main theorem: Bifurcation characterization via isotropy *)
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

(** Square: n=4, d=2 *)
Definition square_example : GeometricObject.
Proof.
  refine {| complexity := 4; dimension := 2 |}.
  - lia.
  - lia.
  - lia.
Defined.

(** Dihedral group D_4 with 8 elements *)
Definition square_symmetry_group : SymmetryGroup.
Proof.
  refine {| group_carrier := unit; group_size := 8 |}.
  lia.
Defined.

(** Square bifurcation non-negative for t > t_c (geom_measure=4, χ=0) *)
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

(** Lower bound for t = 3/5 *)
Definition t_06_lower : 0 <= 3/5.
Proof. nra. Qed.

(** Upper bound for t = 3/5 *)
Definition t_06_upper : 3/5 <= 1.
Proof. nra. Qed.

(** Deformation at t = 0.6 *)
Definition deformation_06 : deformation_parameter :=
  make_deformation (3/5) t_06_lower t_06_upper.

(** t = 0.6 exceeds bifurcation threshold *)
Lemma t_06_past_threshold : proj1_sig deformation_06 > critical_threshold.
Proof.
  unfold deformation_06, make_deformation, critical_threshold.
  simpl. nra.
Qed.

(** Square: ΔG(0.6) ≥ 0 *)
Lemma square_nonneg_breaking_at_t_06 :
  forall (H : IsotropySubgroup square_symmetry_group deformation_06),
  delta_G_bifurcation square_example square_symmetry_group deformation_06 4 0%Z >= 0.
Proof.
  intros H.
  apply post_bifurcation_nonneg.
  - lra.
  - apply t_06_past_threshold.
Qed.

(** Square: ΔG(0.6) > 0 (strict positivity) *)
Lemma square_STRICT_breaking_at_t_06 :
  forall (H : IsotropySubgroup square_symmetry_group deformation_06),
  delta_G_bifurcation square_example square_symmetry_group deformation_06 4 0%Z > 0.
Proof.
  intros H.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_06) critical_threshold) as [Hle|Hgt].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle.
  - apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * unfold A_d, square_example, square_symmetry_group. simpl.
        replace (INR 8) with 8 by (simpl; ring). lra.
      * unfold k_d, square_example. simpl.
        unfold safe_ln. simpl.
        apply exp_pos.
    + unfold bifurcation_base, bifurcation_exponent.
      apply exp_pos.
Qed.

Definition cube_example : GeometricObject.
Proof.
  refine {| complexity := 6; dimension := 3 |}.
  - lia.
  - lia.
  - lia.
Defined.

Definition cube_symmetry_group : SymmetryGroup.
Proof.
  refine {| group_carrier := unit; group_size := 24 |}.
  lia.
Defined.

Definition t_07_lower : 0 <= 7/10.
Proof. nra. Qed.

Definition t_07_upper : 7/10 <= 1.
Proof. nra. Qed.

Definition deformation_07 : deformation_parameter :=
  make_deformation (7/10) t_07_lower t_07_upper.

Lemma t_07_past_threshold : proj1_sig deformation_07 > critical_threshold.
Proof.
  unfold deformation_07, make_deformation, critical_threshold.
  simpl. nra.
Qed.

Lemma cube_breaking_at_t_06 :
  forall (H : IsotropySubgroup cube_symmetry_group deformation_06),
  delta_G_bifurcation cube_example cube_symmetry_group deformation_06 6 2%Z > 0.
Proof.
  intros H.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_06) critical_threshold) as [Hle|Hgt].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle.
  - apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * unfold A_d, cube_symmetry_group. simpl.
        replace (INR 24) with 24 by (simpl; ring). lra.
      * apply exp_pos.
    + apply exp_pos.
Qed.

Lemma cube_breaking_at_t_07 :
  forall (H : IsotropySubgroup cube_symmetry_group deformation_07),
  delta_G_bifurcation cube_example cube_symmetry_group deformation_07 6 2%Z > 0.
Proof.
  intros H.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_07) critical_threshold) as [Hle|Hgt].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_07) (r2 := critical_threshold).
    + apply t_07_past_threshold.
    + exact Hle.
  - apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * unfold A_d, cube_symmetry_group. simpl.
        replace (INR 24) with 24 by (simpl; ring). lra.
      * apply exp_pos.
    + apply exp_pos.
Qed.

Lemma cube_monotonicity_06_to_07 :
  forall (H06 : IsotropySubgroup cube_symmetry_group deformation_06)
         (H07 : IsotropySubgroup cube_symmetry_group deformation_07),
  delta_G_bifurcation cube_example cube_symmetry_group deformation_06 6 2%Z <
  delta_G_bifurcation cube_example cube_symmetry_group deformation_07 6 2%Z.
Proof.
  intros H06 H07.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_06) critical_threshold) as [Hle06|Hgt06];
  destruct (Rle_dec (proj1_sig deformation_07) critical_threshold) as [Hle07|Hgt07].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle06.
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle06.
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_07) (r2 := critical_threshold).
    + apply t_07_past_threshold.
    + exact Hle07.
  - assert (Hbase06 : bifurcation_base deformation_06 > 0).
    { apply bifurcation_base_positive. apply t_06_past_threshold. }
    assert (Hbase07 : bifurcation_base deformation_07 > 0).
    { apply bifurcation_base_positive. apply t_07_past_threshold. }
    assert (Hbase_order : bifurcation_base deformation_06 < bifurcation_base deformation_07).
    { unfold bifurcation_base, deformation_06, deformation_07, make_deformation.
      simpl. unfold critical_threshold, epsilon. nra. }
    assert (Hcoeff_pos : A_d cube_example cube_symmetry_group /
                         Rpower (INR (complexity cube_example)) (k_d cube_example) > 0).
    { apply Rdiv_lt_0_compat.
      - unfold A_d, cube_symmetry_group. simpl.
        replace (INR 24) with 24 by (simpl; ring). lra.
      - apply exp_pos. }
    assert (Hexp_pos : bifurcation_exponent cube_example 6 2 > 0).
    { unfold bifurcation_exponent, B_d, C_d, cube_example. simpl.
      unfold safe_ln. simpl.
      assert (Hln6 : ln (INR 6) > 0).
      { assert (Hinr6 : INR 6 > 1).
        { replace (INR 6) with 6 by (simpl; ring). lra. }
        assert (Hln_inc : ln 1 < ln (INR 6)) by (apply ln_increasing; lra).
        rewrite ln_1 in Hln_inc. exact Hln_inc. }
      assert (H1 : (1 / 6 * ln (INR 6) * ln (INR 6) + (0.1 + 0.01 * ln (INR 6))) * ln (INR 6) > 0).
      { apply Rmult_lt_0_compat.
        - apply Rplus_lt_0_compat.
          + apply Rmult_lt_0_compat.
            * apply Rmult_lt_0_compat.
              -- nra.
              -- exact Hln6.
            * exact Hln6.
          + nra.
        - exact Hln6. }
      assert (H2 : 1.77 > 0) by lra.
      apply Rplus_lt_0_compat.
      - exact H1.
      - exact H2. }
    apply Rmult_lt_compat_l.
    + exact Hcoeff_pos.
    + assert (Hrp06 : Rpower (bifurcation_base deformation_06)
                             (bifurcation_exponent cube_example 6 2) =
                     exp (bifurcation_exponent cube_example 6 2 *
                         ln (bifurcation_base deformation_06))).
      { unfold Rpower. reflexivity. }
      assert (Hrp07 : Rpower (bifurcation_base deformation_07)
                             (bifurcation_exponent cube_example 6 2) =
                     exp (bifurcation_exponent cube_example 6 2 *
                         ln (bifurcation_base deformation_07))).
      { unfold Rpower. reflexivity. }
      rewrite Hrp06, Hrp07.
      apply exp_increasing.
      apply Rmult_lt_compat_l.
      * exact Hexp_pos.
      * apply ln_increasing.
        -- exact Hbase06.
        -- exact Hbase_order.
Qed.

(** 600-Cell: n=600, d=4 *)
Definition cell_600_example : GeometricObject.
Proof.
  refine {| complexity := 600; dimension := 4 |}.
  - lia.
  - lia.
  - lia.
Defined.

(** Helper: 14400 > 0 *)
Lemma size_14400_pos : (14400 > 0)%nat.
Proof.
  unfold gt. unfold lt. apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

(** 600-cell symmetry group with 14400 elements *)
Definition cell_600_symmetry_group : SymmetryGroup.
Proof.
  refine {| group_carrier := unit; group_size := 14400 |}.
  exact size_14400_pos.
Defined.

(** 600-cell: ΔG(0.6) > 0 (hypervolume=150, χ=120) *)
Lemma cell_600_breaking_at_t_06 :
  forall (H : IsotropySubgroup cell_600_symmetry_group deformation_06),
  delta_G_bifurcation cell_600_example cell_600_symmetry_group deformation_06 150 120%Z > 0.
Proof.
  intros H.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_06) critical_threshold) as [Hle|Hgt].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle.
  - apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * unfold A_d, cell_600_symmetry_group. simpl.
        replace (INR 14400) with 14400 by (simpl; ring). lra.
      * apply exp_pos.
    + apply exp_pos.
Qed.

(** Lower bound for t = 3/4 *)
Definition t_075_lower : 0 <= 3/4.
Proof. nra. Qed.

(** Upper bound for t = 3/4 *)
Definition t_075_upper : 3/4 <= 1.
Proof. nra. Qed.

(** Deformation at t = 0.75 *)
Definition deformation_075 : deformation_parameter :=
  make_deformation (3/4) t_075_lower t_075_upper.

(** t = 0.75 exceeds bifurcation threshold *)
Lemma t_075_past_threshold : proj1_sig deformation_075 > critical_threshold.
Proof.
  unfold deformation_075, make_deformation, critical_threshold.
  simpl. nra.
Qed.

(** 600-cell: ΔG(0.75) > 0 *)
Lemma cell_600_breaking_at_t_075 :
  forall (H : IsotropySubgroup cell_600_symmetry_group deformation_075),
  delta_G_bifurcation cell_600_example cell_600_symmetry_group deformation_075 150 120%Z > 0.
Proof.
  intros H.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_075) critical_threshold) as [Hle|Hgt].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_075) (r2 := critical_threshold).
    + apply t_075_past_threshold.
    + exact Hle.
  - apply Rmult_lt_0_compat.
    + apply Rdiv_lt_0_compat.
      * unfold A_d, cell_600_symmetry_group. simpl.
        replace (INR 14400) with 14400 by (simpl; ring). lra.
      * apply exp_pos.
    + apply exp_pos.
Qed.

(** Helper: ln(600) > 0 *)
Lemma ln_600_pos : ln (INR 600) > 0.
Proof.
  assert (Hinr600 : INR 600 > 1).
  { replace (INR 600) with 600 by (simpl; ring). lra. }
  assert (Hln_inc : ln 1 < ln (INR 600)) by (apply ln_increasing; lra).
  rewrite ln_1 in Hln_inc. exact Hln_inc.
Qed.

(** Helper: B_d term for 600-cell is positive *)
Lemma B_d_600_ln_600_pos :
  (1 / 150 * ln (INR 600) * ln (INR 600) + (0.1 + 0.01 * ln (INR 600))) * ln (INR 600) > 0.
Proof.
  apply Rmult_lt_0_compat.
  - apply Rplus_lt_0_compat.
    + apply Rmult_lt_0_compat.
      * apply Rmult_lt_0_compat.
        -- nra.
        -- apply ln_600_pos.
      * apply ln_600_pos.
    + assert (Hln : ln (INR 600) > 0) by apply ln_600_pos.
      nra.
  - apply ln_600_pos.
Qed.

(** Helper: C_d term for 600-cell is positive *)
Lemma C_d_600_pos : 1 + 0.1 * (IZR 120 / safe_ln 600) > 0.
Proof.
  assert (Hln : safe_ln 600 > 0).
  { unfold safe_ln. simpl. apply ln_600_pos. }
  assert (H120 : IZR 120 > 0).
  { vm_compute. lra. }
  assert (Hfrac : IZR 120 / safe_ln 600 > 0).
  { apply Rdiv_lt_0_compat; assumption. }
  nra.
Qed.

(** Helper: bifurcation exponent for 600-cell is positive *)
Lemma bifurcation_exp_600_pos :
  bifurcation_exponent cell_600_example 150 120 > 0.
Proof.
  unfold bifurcation_exponent.
  assert (HB : B_d cell_600_example 150 * safe_ln (complexity cell_600_example) > 0).
  { unfold cell_600_example, B_d, safe_ln. simpl.
    apply B_d_600_ln_600_pos. }
  assert (HC : C_d cell_600_example 120 > 0).
  { unfold cell_600_example, C_d. simpl.
    assert (Hln : safe_ln 600 > 0).
    { unfold safe_ln. simpl. apply ln_600_pos. }
    assert (H120 : IZR 120 > 0) by (vm_compute; lra).
    assert (Hfrac : IZR 120 / safe_ln 600 > 0).
    { apply Rdiv_lt_0_compat; assumption. }
    nra. }
  lra.
Qed.

(** 600-cell monotonicity: ΔG(0.6) < ΔG(0.75) *)
Lemma cell_600_monotonicity_06_to_075 :
  forall (H06 : IsotropySubgroup cell_600_symmetry_group deformation_06)
         (H075 : IsotropySubgroup cell_600_symmetry_group deformation_075),
  delta_G_bifurcation cell_600_example cell_600_symmetry_group deformation_06 150 120%Z <
  delta_G_bifurcation cell_600_example cell_600_symmetry_group deformation_075 150 120%Z.
Proof.
  intros H06 H075.
  unfold delta_G_bifurcation.
  destruct (Rle_dec (proj1_sig deformation_06) critical_threshold) as [Hle06|Hgt06];
  destruct (Rle_dec (proj1_sig deformation_075) critical_threshold) as [Hle075|Hgt075].
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle06.
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_06) (r2 := critical_threshold).
    + apply t_06_past_threshold.
    + exact Hle06.
  - exfalso. apply Rgt_not_le with (r1 := proj1_sig deformation_075) (r2 := critical_threshold).
    + apply t_075_past_threshold.
    + exact Hle075.
  - assert (Hbase06 : bifurcation_base deformation_06 > 0).
    { apply bifurcation_base_positive. apply t_06_past_threshold. }
    assert (Hbase075 : bifurcation_base deformation_075 > 0).
    { apply bifurcation_base_positive. apply t_075_past_threshold. }
    assert (Hbase_order : bifurcation_base deformation_06 < bifurcation_base deformation_075).
    { unfold bifurcation_base, deformation_06, deformation_075, make_deformation.
      simpl. unfold critical_threshold, epsilon. nra. }
    assert (Hcoeff_pos : A_d cell_600_example cell_600_symmetry_group /
                         Rpower (INR (complexity cell_600_example)) (k_d cell_600_example) > 0).
    { apply Rdiv_lt_0_compat.
      - unfold A_d, cell_600_symmetry_group. simpl.
        replace (INR 14400) with 14400 by (simpl; ring). lra.
      - apply exp_pos. }
    assert (Hexp_pos : bifurcation_exponent cell_600_example 150 120 > 0).
    { apply bifurcation_exp_600_pos. }
    apply Rmult_lt_compat_l.
    + exact Hcoeff_pos.
    + assert (Hrp06 : Rpower (bifurcation_base deformation_06)
                             (bifurcation_exponent cell_600_example 150 120) =
                     exp (bifurcation_exponent cell_600_example 150 120 *
                         ln (bifurcation_base deformation_06))).
      { unfold Rpower. reflexivity. }
      assert (Hrp075 : Rpower (bifurcation_base deformation_075)
                             (bifurcation_exponent cell_600_example 150 120) =
                     exp (bifurcation_exponent cell_600_example 150 120 *
                         ln (bifurcation_base deformation_075))).
      { unfold Rpower. reflexivity. }
      rewrite Hrp06, Hrp075.
      apply exp_increasing.
      apply Rmult_lt_compat_l.
      * exact Hexp_pos.
      * apply ln_increasing.
        -- exact Hbase06.
        -- exact Hbase_order.
Qed.

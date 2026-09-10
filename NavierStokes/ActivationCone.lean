import NavierStokes.ConeAlgebra
import NavierStokes.StressActivation
import NavierStokes.UniformCone
import NavierStokes.NaturalEntrance
import NavierStokes.ActivationBounds
import NavierStokes.ActivationStocks
import Mathlib.Tactic.GCongr
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Initial activation cone estimates

The scalar estimates keep every error proportional to the activation itself.
In particular, none of their constants involves the inverse of the retained
damping parameter. The later results use the constructed activation fields.
-/

noncomputable section

namespace NavierStokes.ActivationCone

open Set Filter
open scoped Topology ContDiff
open ConeAlgebra StressActivation ProfileHistories

/-- Actual smooth factor in the reciprocal angular-field ratio. -/
noncomputable def inverseRelativeError (L : Field) (q : ActivationBounds.ScaledPoint) : ℝ :=
  -ActivationBounds.controlledErrorFactor L q *
    meanExp (-ActivationBounds.scaledDistance q * ActivationBounds.controlledErrorFactor L q)

theorem inverseRelativeError_smooth {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (inverseRelativeError L) (ActivationBounds.scaledDomain J) :=
  (ActivationBounds.controlledErrorFactor_smooth hJ hL).neg.mul
    (meanExp_smooth.comp_contDiffOn
      (ActivationBounds.scaledDistance_smooth.contDiffOn.neg.mul
        (ActivationBounds.controlledErrorFactor_smooth hJ hL)))

theorem inverse_relative_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    referenceAngular L (T * u, η) / activatedAngular T κ L (T * u, η) - 1 =
      ActivationBounds.scaledDistance ((κ, T), (u, η)) * inverseRelativeError L ((κ, T), (u, η)) := by
  have hd := ActivationBounds.controlled_scaled_factor hT κ hJ hL u hη
  have hrev : L (T * u, η) - controlled T κ L (T * u, η) =
      -ActivationBounds.scaledDistance ((κ, T), (u, η)) *
        ActivationBounds.controlledErrorFactor L ((κ, T), (u, η)) := by linarith
  rw [referenceAngular, activatedAngular, ← Real.exp_sub, hrev, exp_sub_one]
  unfold inverseRelativeError
  ring

/-- All fixed parameter jets of this actual ratio have uniform `C*y*ea`
bounds as the ramp width and retained damping tend to zero. -/
theorem inverse_relative_uniform_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {L : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          referenceAngular L (y, ξ) / activatedAngular T κ L (y, ξ) - 1) η| ≤
            M * y * activation T κ y := by
  apply ActivationBounds.width_uniform_jet_bound hJ hK hKJ (inverseRelativeError_smooth hJ hL)
  intro κ T hT u η hη
  exact inverse_relative_scaled_factor hT.ne' κ hJ hL u hη

/-- A quantitative cone estimate retaining the small activation factor.
The error scale `s` is `C*y` in the activation ramp. -/
theorem ramp_cone_of_errors {c B r e s P J v : ℝ}
    (hc : 0 < c) (hr : 2 + c ≤ r) (hrB : r ≤ B)
    (he : 0 < e) (he1 : e ≤ 1) (hs : 0 ≤ s)
    (hsquarter : s ≤ 1 / 4) (hsc : s ≤ c / 2)
    (hsB : (B + 1) * s ≤ 1 / 4)
    (hP : |P - r| ≤ s * e) (hv : |v - (1 - e) * r| ≤ s * e)
    (hJ : |J| ≤ s * e) :
    e ≤ P - v ∧ 2 + c / 4 < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2 := by
  have hrpos : 0 < r := by linarith
  have hBpos : 0 < B := lt_of_lt_of_le hrpos hrB
  obtain ⟨hPl, hPu⟩ := abs_le.mp hP
  obtain ⟨hvl, hvu⟩ := abs_le.mp hv
  obtain ⟨hJl, hJu⟩ := abs_le.mp hJ
  have hse : 0 ≤ s * e := mul_nonneg hs he.le
  have hsle : s * e ≤ s := mul_le_of_le_one_right hs he1
  have hrgap : 1 ≤ r - 2 * s := by linarith
  have hgap : e ≤ P - v := by
    have h := mul_le_mul_of_nonneg_left hrgap he.le
    nlinarith
  have hPgt : 2 + c / 4 < P := by linarith
  have hvB : v - 2 ≤ B := by
    have h := mul_nonneg he.le hrpos.le
    nlinarith
  have hJsq : J ^ 2 ≤ s ^ 2 * e ^ 2 := by
    have h := mul_nonneg (show 0 ≤ s * e - J by linarith)
      (show 0 ≤ s * e + J by linarith)
    nlinarith
  have hBs : B * s ≤ 1 / 4 := by nlinarith
  have hBss : B * s ^ 2 ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_right hBs hs
    nlinarith
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  have hquad : (v - 2) * J ^ 2 < 2 * (P - v) ^ 2 := calc
    (v - 2) * J ^ 2 ≤ B * J ^ 2 := mul_le_mul_of_nonneg_right hvB (sq_nonneg J)
    _ ≤ B * (s ^ 2 * e ^ 2) := mul_le_mul_of_nonneg_left hJsq hBpos.le
    _ = (B * s ^ 2) * e ^ 2 := by ring
    _ ≤ (1 / 16 : ℝ) * e ^ 2 := mul_le_mul_of_nonneg_right hBss he2.le
    _ < 2 * e ^ 2 := by nlinarith
    _ ≤ 2 * (P - v) ^ 2 := by nlinarith
  exact ⟨hgap, hPgt, hquad⟩

/-- A small activation preserves a uniform part of the reference `v > 2`
margin. There is no inverse-damping loss. -/
theorem collar_lower_of_errors {c B r e s v : ℝ}
    (hc : 0 < c) (hr : 2 + c ≤ r) (hrB : r ≤ B)
    (he : 0 ≤ e) (hs : s ≤ 1) (heB : e * (B + 1) ≤ c / 4)
    (hv : |v - (1 - e) * r| ≤ s * e) :
    2 + c / 2 < v := by
  have hl := (abs_le.mp hv).1
  have hm := mul_le_mul_of_nonneg_left (show r + s ≤ B + 1 by linarith) he
  nlinarith

/-- Combining the ramp and collar estimates gives the actual lower-root
criterion, including the strict lower bound on `v`. -/
theorem true_collar_of_errors {c B r e s P J v : ℝ}
    (hc : 0 < c) (hr : 2 + c ≤ r) (hrB : r ≤ B)
    (he : 0 < e) (he1 : e ≤ 1) (hs : 0 ≤ s)
    (hsquarter : s ≤ 1 / 4) (hsc : s ≤ c / 2)
    (hsB : (B + 1) * s ≤ 1 / 4) (heB : e * (B + 1) ≤ c / 4)
    (hP : |P - r| ≤ s * e) (hv : |v - (1 - e) * r| ≤ s * e)
    (hJ : |J| ≤ s * e) :
    e ≤ P - v ∧ 2 + c / 2 < v ∧ 2 < P ∧ v < coneBound P J := by
  obtain ⟨hgap, _, hquad⟩ := ramp_cone_of_errors hc hr hrB he he1 hs hsquarter hsc hsB hP hv hJ
  have hvc := collar_lower_of_errors hc hr hrB he.le (by linarith) heB hv
  have hv2 : 2 < v := by linarith
  have hcone := (true_cone_iff hv2).mpr ⟨by linarith, hquad⟩
  exact ⟨hgap, hvc, hcone⟩

/-- A single error tolerance is chosen from the fixed reference bounds. -/
noncomputable def errorTolerance (c B : ℝ) : ℝ :=
  min (1 / 4) (min (c / 2) (1 / (4 * (B + 1))))

theorem errorTolerance_pos {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    0 < errorTolerance c B := by
  unfold errorTolerance
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem errorTolerance_bounds {c B s : ℝ} (hB : 0 ≤ B) (hs : s ≤ errorTolerance c B) :
    s ≤ 1 / 4 ∧ s ≤ c / 2 ∧ (B + 1) * s ≤ 1 / 4 := by
  have h1 : s ≤ 1 / 4 := hs.trans (min_le_left _ _)
  have h2 : s ≤ c / 2 := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : s ≤ 1 / (4 * (B + 1)) :=
    hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp : 0 < 4 * (B + 1) := by positivity
  have hm := (le_div_iff₀ hp).mp h3
  refine ⟨h1, h2, ?_⟩
  nlinarith

/-- Positivity of the actual flat activation on the nonzero ramp. -/
theorem activation_pos {T κ y : ℝ} (hT : 0 < T) (hκ : κ < 1) (hy : 0 < y) :
    0 < activation T κ y := by
  unfold activation OutgoingSchedule.sigma
  exact mul_pos (sub_pos.mpr hκ)
    (div_pos (FlatCutoff.edge_pos 1 (div_pos hy hT)) (OutgoingSchedule.sigma_denom_pos _))

/-- For any requested small activation, a fixed fraction of the ramp works
uniformly in its width and in every retained damping `κ ∈ [0,1]`. -/
theorem activation_uniform_collar {m : ℝ} (hm : 0 < m) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∀ T : ℝ, 0 < T → ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) (θ * T), activation T κ y < m := by
  have hcont := OutgoingSchedule.sigma_contDiff.continuous.continuousAt (x := (0 : ℝ))
  obtain ⟨δ, hδ, hδprop⟩ := Metric.continuousAt_iff.mp hcont m hm
  refine ⟨min (δ / 2) 1, lt_min (by positivity) zero_lt_one, min_le_right _ _, ?_⟩
  intro T hT κ hκ y hy
  have hu : 0 ≤ y / T := div_nonneg hy.1 hT.le
  have huy : y / T ≤ min (δ / 2) 1 := (div_le_iff₀ hT).mpr hy.2
  have hud : dist (y / T) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hu]
    have := huy.trans (min_le_left _ _)
    linarith
  have hsigma : OutgoingSchedule.sigma (y / T) < m := by
    have h := hδprop hud
    simpa only [OutgoingSchedule.sigma_zero le_rfl, Real.dist_eq, sub_zero,
      abs_of_nonneg (OutgoingSchedule.sigma_nonneg _)] using h
  have hact : activation T κ y ≤ OutgoingSchedule.sigma (y / T) := by
    unfold activation
    exact mul_le_of_le_one_left (OutgoingSchedule.sigma_nonneg _) (by linarith [hκ.1])
  exact hact.trans_lt hsigma

/-- Uniform conversion of proved comparison estimates into a complete
initial ramp and a first true-cone collar. The constants are chosen before
the retained damping parameter. -/
theorem uniform_ramp_from_comparison {K : Set ℝ} {r : Field}
    {P J v : ℝ → ℝ → Field} {c B C T0 : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT0 : 0 < T0)
    (href : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ K, 2 + c ≤ r (y, η) ∧ r (y, η) ≤ B)
    (herr : ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Ioo (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |P T κ (y, η) - r (y, η)| ≤ C * y * activation T κ y ∧
        |v T κ (y, η) - damping T κ y * r (y, η)| ≤ C * y * activation T κ y ∧
        |J T κ (y, η)| ≤ C * y * activation T κ y) :
    ∃ Tstar θ : ℝ, 0 < Tstar ∧ Tstar ≤ T0 ∧ 0 < θ ∧ θ ≤ 1 ∧
      ∀ T ∈ Ioc (0 : ℝ) Tstar, ∀ κ ∈ Ioo (0 : ℝ) 1,
        ∀ y ∈ Ioc (0 : ℝ) T, ∀ η ∈ K,
          activation T κ y ≤ P T κ (y, η) - v T κ (y, η) ∧
          2 + c / 4 < P T κ (y, η) ∧
          (v T κ (y, η) - 2) * J T κ (y, η) ^ 2 <
            2 * (P T κ (y, η) - v T κ (y, η)) ^ 2 ∧
          v T κ (y, η) < coneBound (P T κ (y, η)) (J T κ (y, η)) ∧
          (y ≤ θ * T → 2 + c / 2 < v T κ (y, η)) := by
  have htolerance : 0 < errorTolerance c B := errorTolerance_pos hc hB
  have hCp : 0 < C + 1 := by linarith
  have hBp : 0 < 4 * (B + 1) := by positivity
  obtain ⟨θ, hθ, hθone, hsmallactivation⟩ :=
    activation_uniform_collar (div_pos hc hBp)
  let Tstar := min T0 (errorTolerance c B / (C + 1))
  have hTstar : 0 < Tstar := lt_min hT0 (div_pos htolerance hCp)
  refine ⟨Tstar, θ, hTstar, min_le_left _ _, hθ, hθone, ?_⟩
  intro T hT κ hκ y hy η hη
  have hTbound : T ≤ T0 := hT.2.trans (min_le_left _ _)
  have hyT0 : y ≤ T0 := hy.2.trans hTbound
  have herrors := herr T ⟨hT.1, hTbound⟩ κ hκ y ⟨hy.1.le, hy.2⟩ η hη
  have hr := href y ⟨hy.1.le, hyT0⟩ η hη
  have he : 0 < activation T κ y := activation_pos hT.1 hκ.2 hy.1
  have heone : activation T κ y ≤ 1 := activation_le_one T κ y ⟨hκ.1.le, hκ.2.le⟩
  have hs : 0 ≤ C * y := mul_nonneg hC hy.1.le
  have hytol : y ≤ errorTolerance c B / (C + 1) :=
    hy.2.trans (hT.2.trans (min_le_right _ _))
  have hstol : C * y ≤ errorTolerance c B := by
    have h := (le_div_iff₀ hCp).mp hytol
    nlinarith
  obtain ⟨hsq, hsc, hsB⟩ := errorTolerance_bounds hB hstol
  have hve : |v T κ (y, η) - (1 - activation T κ y) * r (y, η)| ≤
      (C * y) * activation T κ y := herrors.2.1
  obtain ⟨hgap, hPgt, hquad⟩ := ramp_cone_of_errors hc hr.1 hr.2 he heone hs hsq hsc hsB herrors.1 hve herrors.2.2
  have hP2 : 2 < P T κ (y, η) := by linarith
  have hroot : v T κ (y, η) < coneBound (P T κ (y, η)) (J T κ (y, η)) := by
    by_cases hv2 : 2 < v T κ (y, η)
    · exact ((true_cone_iff hv2).mpr ⟨by linarith, hquad⟩).2
    · exact relaxed_cone_of_le_two hP2 (le_of_not_gt hv2)
  refine ⟨hgap, hPgt, hquad, hroot, ?_⟩
  intro hycollar
  have hsmall := hsmallactivation T hT.1 κ ⟨hκ.1.le, hκ.2.le⟩ y ⟨hy.1.le, hycollar⟩
  have heB : activation T κ y * (B + 1) ≤ c / 4 := by
    have h := (lt_div_iff₀ hBp).mp hsmall
    nlinarith
  exact collar_lower_of_errors hc hr.1 hr.2 he.le (by linarith) heB hve

/-- Exact stress factorization when stock and shear-ratio errors carry the
constructed factor `y*e`. Neither component divides by the damping. -/
theorem stress_factorization (F A B κ y e dA dB dR : ℝ) (hκ : κ = 1 - e) :
    (F * ((A + y * e * dA) - κ * A),
      F * ((B + y * e * dB) - κ * B * (1 + y * e * dR))) =
    (e * (F * (A + y * dA)),
      e * (F * (B + y * (dB - κ * B * dR)))) := by
  subst κ
  congr 1 <;> ring

/-- The smooth extension of stress divided by the activation factor. -/
noncomputable def reducedStress (F A B κ y dA dB dR : ℝ) : ℝ × ℝ :=
  (F * (A + y * dA), F * (B + y * (dB - κ * B * dR)))

@[simp] theorem reducedStress_at_edge (F A B κ dA dB dR : ℝ) :
    reducedStress F A B κ 0 dA dB dR = (F * A, F * B) := by
  simp [reducedStress]

/-- This extension is smooth without dividing by either activation or damping. -/
theorem reducedStress_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {F A B κ y dA dB dR : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F S) (hA : ContDiffOn ℝ ∞ A S)
    (hB : ContDiffOn ℝ ∞ B S) (hκ : ContDiffOn ℝ ∞ κ S)
    (hy : ContDiffOn ℝ ∞ y S) (hdA : ContDiffOn ℝ ∞ dA S)
    (hdB : ContDiffOn ℝ ∞ dB S) (hdR : ContDiffOn ℝ ∞ dR S) :
    ContDiffOn ℝ ∞ (fun p => reducedStress (F p) (A p) (B p) (κ p) (y p) (dA p) (dB p) (dR p)) S :=
  (hF.mul (hA.add (hy.mul hdA))).prodMk
    (hF.mul (hB.add (hy.mul (hdB.sub ((hκ.mul hB).mul hdR)))))

/-- A common coefficient bound makes the normalized stress direction nonzero
on a uniform first collar; the bound does not involve inverse damping. -/
theorem reducedStress_first_positive {F A B κ y dA dB dR α M : ℝ}
    (hF : 0 < F) (hα : 0 < α) (hA : α ≤ A) (hy : 0 ≤ y)
    (hdA : |dA| ≤ M) (hsmall : y * M ≤ α / 2) :
    0 < (reducedStress F A B κ y dA dB dR).1 := by
  apply mul_pos hF
  have hlo := (abs_le.mp hdA).1
  have hm := mul_le_mul_of_nonneg_left hlo hy
  nlinarith

theorem reducedStress_nonzero {F A B κ y dA dB dR α M : ℝ}
    (hF : 0 < F) (hα : 0 < α) (hA : α ≤ A) (hy : 0 ≤ y)
    (hdA : |dA| ≤ M) (hsmall : y * M ≤ α / 2) :
    reducedStress F A B κ y dA dB dR ≠ 0 := by
  intro hz
  have hpos := reducedStress_first_positive (B := B) (κ := κ) (dB := dB) (dR := dR)
    hF hα hA hy hdA hsmall
  rw [hz] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

theorem reducedStress_edge_projection (F A B κ dA dB dR : ℝ) :
    (reducedStress F A B κ 0 dA dB dR).1 +
      (B / A) * (reducedStress F A B κ 0 dA dB dR).2 =
      F * (A + B ^ 2 / A) := by
  simp only [reducedStress_at_edge]
  ring

/-- The true angular directional margin has a strictly positive edge limit. -/
theorem reducedStress_edge_margin {F A B c κ dA dB dR : ℝ}
    (hF : 0 < F) (hc : 0 < c) (hr : 2 + c ≤ A + B ^ 2 / A) :
    2 * F < (reducedStress F A B κ 0 dA dB dR).1 +
      (B / A) * (reducedStress F A B κ 0 dA dB dR).2 := by
  rw [reducedStress_edge_projection]
  nlinarith

/-- The quadratic cone gap after removing the square of the flat activation. -/
noncomputable def normalizedConeGap (r v y dP dv dJ : ℝ) : ℝ :=
  2 * (r + y * (dP - dv)) ^ 2 - (v - 2) * (y * dJ) ^ 2

theorem cone_gap_factorization (r e y dP dv dJ : ℝ) :
    2 * ((r + y * e * dP) - ((1 - e) * r + y * e * dv)) ^ 2 -
        (((1 - e) * r + y * e * dv) - 2) * (y * e * dJ) ^ 2 =
      e ^ 2 * normalizedConeGap r ((1 - e) * r + y * e * dv) y dP dv dJ := by
  unfold normalizedConeGap
  ring

@[simp] theorem normalizedConeGap_at_edge (r v dP dv dJ : ℝ) :
    normalizedConeGap r v 0 dP dv dJ = 2 * r ^ 2 := by
  simp [normalizedConeGap]

theorem normalizedConeGap_edge_positive {r : ℝ} (hr : r ≠ 0) (v dP dv dJ : ℝ) :
    0 < normalizedConeGap r v 0 dP dv dJ := by
  rw [normalizedConeGap_at_edge]
  positivity

/-- The actual cone coordinates formed from two stock coordinates and a shear ratio. -/
noncomputable def stockProjection (p q t : ℝ) : ℝ := p + q * t
noncomputable def stockCross (p q t : ℝ) : ℝ := q - p * t

noncomputable def projectionError (A B z dA dB dR : ℝ) : ℝ :=
  dA + dB * (B / A) * (1 + z * dR) + (B ^ 2 / A) * dR

noncomputable def crossError (A B z dA dB dR : ℝ) : ℝ :=
  dB - B * dR - dA * (B / A) * (1 + z * dR)

noncomputable def sizeError (κ A B z dR : ℝ) : ℝ :=
  κ * (B ^ 2 / A) * dR * (2 + z * dR)

/-- Passing from stock errors to cone errors preserves the exact common
factor. This computation contains no division by the damping `κ`. -/
theorem cone_error_factorizations (κ A B z dA dB dR : ℝ) (hA : A ≠ 0) :
    stockProjection (A + z * dA) (B + z * dB) ((B / A) * (1 + z * dR)) -
        (A + B ^ 2 / A) = z * projectionError A B z dA dB dR ∧
    stockCross (A + z * dA) (B + z * dB) ((B / A) * (1 + z * dR)) =
        z * crossError A B z dA dB dR ∧
    κ * (A + (B ^ 2 / A) * (1 + z * dR) ^ 2) - κ * (A + B ^ 2 / A) =
        z * sizeError κ A B z dR := by
  dsimp [stockProjection, stockCross, projectionError, crossError, sizeError]
  constructor
  · field_simp [hA]
    ring
  constructor <;> field_simp [hA] <;> ring

noncomputable def comparisonConstant (M : ℝ) : ℝ := M + 2 * M ^ 2 + M ^ 3

/-- One bound for the transported error factors, depending only on the
reference and primitive-factor bounds. It is uniform down to `κ = 0`. -/
theorem cone_error_bounds {κ A B z dA dB dR M : ℝ}
    (hM : 0 ≤ M) (hκ : |κ| ≤ 1) (hz : |z| ≤ 1)
    (hB : |B| ≤ M) (hBA : |B / A| ≤ M) (hB2A : |B ^ 2 / A| ≤ M)
    (hdA : |dA| ≤ M) (hdB : |dB| ≤ M) (hdR : |dR| ≤ M) :
    |projectionError A B z dA dB dR| ≤ comparisonConstant M ∧
    |crossError A B z dA dB dR| ≤ comparisonConstant M ∧
    |sizeError κ A B z dR| ≤ comparisonConstant M := by
  have hzr : |z * dR| ≤ M := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hz hdR (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h1 : |1 + z * dR| ≤ 1 + M := (abs_add_le _ _).trans (by simpa using add_le_add_right hzr 1)
  have h2 : |2 + z * dR| ≤ 2 + M := (abs_add_le _ _).trans (by simpa using add_le_add_right hzr 2)
  refine ⟨?_, ?_, ?_⟩
  · calc
      |projectionError A B z dA dB dR| ≤
          |dA| + |dB| * |B / A| * |1 + z * dR| + |B ^ 2 / A| * |dR| := by
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
          |>.trans_eq (by simp only [abs_mul])
      _ ≤ M + M * M * (1 + M) + M * M := by gcongr
      _ = comparisonConstant M := by unfold comparisonConstant; ring
  · calc
      |crossError A B z dA dB dR| ≤
          |dB| + |B| * |dR| + |dA| * |B / A| * |1 + z * dR| := by
        exact (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
          |>.trans_eq (by simp only [abs_mul])
      _ ≤ M + M * M + M * M * (1 + M) := by gcongr
      _ = comparisonConstant M := by unfold comparisonConstant; ring
  · calc
      |sizeError κ A B z dR| = |κ| * |B ^ 2 / A| * |dR| * |2 + z * dR| := by
        simp only [sizeError, abs_mul]
      _ ≤ 1 * M * M * (2 + M) := by gcongr
      _ ≤ comparisonConstant M := by unfold comparisonConstant; nlinarith

private theorem bounded_error_factor {M z x : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z)
    (hx : |x| ≤ M * z) : ∃ d : ℝ, |d| ≤ M ∧ x = z * d := by
  by_cases hz0 : z = 0
  · have hx0 : x = 0 := abs_nonpos_iff.mp (by simpa only [hz0, mul_zero] using hx)
    exact ⟨0, by simpa using hM, by simp [hx0]⟩
  · have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    refine ⟨x / z, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hzp]
      exact (div_le_iff₀ hzp).mpr hx
    · field_simp

/-- Explicit transport of actual stock and reciprocal-field error bounds to
the three cone-coordinate error bounds. -/
theorem cone_comparison_from_stock_bounds {κ A B z p q R M : ℝ}
    (hM : 0 ≤ M) (hA : A ≠ 0) (hκ : |κ| ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hB : |B| ≤ M) (hBA : |B / A| ≤ M) (hB2A : |B ^ 2 / A| ≤ M)
    (hp : |p - A| ≤ M * z) (hq : |q - B| ≤ M * z) (hR : |R - 1| ≤ M * z) :
    |stockProjection p q ((B / A) * R) - (A + B ^ 2 / A)| ≤ comparisonConstant M * z ∧
    |κ * (A + (B ^ 2 / A) * R ^ 2) - κ * (A + B ^ 2 / A)| ≤ comparisonConstant M * z ∧
    |stockCross p q ((B / A) * R)| ≤ comparisonConstant M * z := by
  obtain ⟨dA, hdA, hda⟩ := bounded_error_factor hM hz hp
  obtain ⟨dB, hdB, hdb⟩ := bounded_error_factor hM hz hq
  obtain ⟨dR, hdR, hdr⟩ := bounded_error_factor hM hz hR
  have hpval : p = A + z * dA := by linarith
  have hqval : q = B + z * dB := by linarith
  have hRval : R = 1 + z * dR := by linarith
  rw [hpval, hqval, hRval]
  obtain ⟨hfP, hfJ, hfv⟩ := cone_error_factorizations κ A B z dA dB dR hA
  obtain ⟨hbP, hbJ, hbv⟩ := cone_error_bounds (A := A) (B := B) (z := z)
    (dA := dA) (dB := dB) (dR := dR) hM hκ
    (by simpa only [abs_of_nonneg hz] using hz1) hB hBA hB2A hdA hdB hdR
  rw [hfP, hfJ, hfv]
  simp only [abs_mul, abs_of_nonneg hz]
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hbP hz],
    by nlinarith [mul_le_mul_of_nonneg_left hbv hz],
    by nlinarith [mul_le_mul_of_nonneg_left hbJ hz]⟩

/-- The genuine derivative-defined shear size has the cancellation form used
in the error transport. -/
theorem shearSize_eq (T : ℝ) {κ X0 : ℝ} (hκ : κ ∈ Ioc (0 : ℝ) 1) (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J)
    (hA : referenceP1 L (y, η) ≠ 0) :
    shearSize T κ X0 L U (y, η) = damping T κ y *
      (referenceP1 L (y, η) + (referenceP2 X0 L U (y, η) ^ 2 / referenceP1 L (y, η)) *
        (referenceAngular L (y, η) / activatedAngular T κ L (y, η)) ^ 2) := by
  have h := shearSize_error T hκ hX0 hJ hL hU y hη hA
  unfold referenceSize at h
  nlinarith

noncomputable def activatedStockOne (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : Field) (T κ : ℝ) : Field :=
  ActivationStocks.logViewOne h X0 (activatedAngular T κ L)
    (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U))

noncomputable def activatedStockTwo (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : Field) (T κ : ℝ) : Field :=
  ActivationStocks.logViewTwo h X0 (activatedAngular T κ L) (controlled T κ U)
    (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U))

noncomputable def activatedProjection (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : Field) (T κ : ℝ) : Field := fun p =>
  stockProjection (activatedStockOne h X0 initial L U T κ p)
    (activatedStockTwo h X0 initial L U T κ p) (shearSlope T κ X0 L U p)

noncomputable def activatedCross (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : Field) (T κ : ℝ) : Field := fun p =>
  stockCross (activatedStockOne h X0 initial L U T κ p)
    (activatedStockTwo h X0 initial L U T κ p) (shearSlope T κ X0 L U p)

noncomputable def activatedStress (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : Field) (T κ : ℝ) (p : Point) : ℝ × ℝ :=
  (activatedAngular T κ L p * (activatedStockOne h X0 initial L U T κ p - actualP1 T κ L p),
    activatedAngular T κ L p * (activatedStockTwo h X0 initial L U T κ p - actualP2 T κ X0 L U p))

theorem reference_coordinates_smooth {X0 : ℝ} (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (referenceP1 L) (logDomain J hJ).carrier ∧
      ContDiffOn ℝ ∞ (referenceP2 X0 L U) (logDomain J hJ).carrier := by
  have hs : ContDiff ℝ ∞ (fun p : Point => Real.sqrt (2 * radius X0 p.1)) :=
    (contDiff_const.mul (contDiff_const.mul (Real.contDiff_exp.comp contDiff_fst))).sqrt
      (fun p => (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hX0 (Real.exp_pos p.1))).ne')
  refine ⟨contDiffOn_const.mul (radialPartial_smooth (logDomain J hJ) hL), ?_⟩
  exact (contDiffOn_const.mul (radialPartial_smooth (logDomain J hJ) hU)).div
    (hs.contDiffOn.mul hL.exp) (fun p _ =>
      (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) (mul_pos hX0 (Real.exp_pos p.1))))
        (Real.exp_pos _)).ne')

/-- The actual integral-history stress has a smooth factor after division by
the flat activation. Its inner-edge value is the positive reference direction. -/
theorem exists_actual_stress_direction (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (initial : HistoryRow → ℝ → ℝ) {J K : Set ℝ} (hJ : IsOpen J) (hKJ : K ⊆ J)
    {L U : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hi : ∀ r, ContDiffOn ℝ ∞ (initial r) J)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0) {T0 : ℝ}
    (hmatch : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ K,
      ActivationStocks.logViewOne h X0 (referenceAngular L)
          (logHistory X0 initial (referenceAngular L) U) (y, η) = referenceP1 L (y, η) ∧
      ActivationStocks.logViewTwo h X0 (referenceAngular L) U
          (logHistory X0 initial (referenceAngular L) U) (y, η) = referenceP2 X0 L U (y, η)) :
    ∃ D : ActivationBounds.ScaledPoint → ℝ × ℝ,
      ContDiffOn ℝ ∞ D (ActivationBounds.scaledDomain J) ∧
      (∀ κ T η : ℝ, D ((κ, T), (0, η)) =
        (referenceAngular L (0, η) * referenceP1 L (0, η),
          referenceAngular L (0, η) * referenceP2 X0 L U (0, η))) ∧
      ∀ T : ℝ, 0 < T → ∀ κ u η : ℝ, T * u ∈ Icc (0 : ℝ) T0 → η ∈ K →
        activatedStress h X0 initial L U T κ (T * u, η) =
          (activation 1 κ u * (D ((κ, T), (u, η))).1,
            activation 1 κ u * (D ((κ, T), (u, η))).2) := by
  obtain ⟨dA, dB, hdA, hdB, hfactors⟩ :=
    ActivationStocks.exists_log_stock_factors h hX0 initial hJ hL hU hi hcoef
  let D : ActivationBounds.ScaledPoint → ℝ × ℝ := fun q =>
    reducedStress (ActivationBounds.angularValue L q)
      (ActivationBounds.rescale (referenceP1 L) q) (ActivationBounds.rescale (referenceP2 X0 L U) q)
      (damping 1 q.1.1 q.2.1) (q.1.2 * q.2.1) (dA q) (dB q) (inverseRelativeError L q)
  refine ⟨D, ?_, ?_, ?_⟩
  · obtain ⟨ha, hb⟩ := reference_coordinates_smooth hX0 hJ hL hU
    apply reducedStress_smooth
    · exact (ActivationBounds.controlledValue_smooth hJ hL).exp
    · exact ActivationBounds.rescale_smooth hJ ha
    · exact ActivationBounds.rescale_smooth hJ hb
    · exact (contDiff_const.sub ((contDiff_const.sub contDiff_fst.fst).mul
        (OutgoingSchedule.sigma_contDiff.comp (contDiff_snd.fst.div_const 1)))).contDiffOn
    · exact (contDiff_fst.snd.mul contDiff_snd.fst).contDiffOn
    · exact hdA
    · exact hdB
    · exact inverseRelativeError_smooth hJ hL
  · intro κ T η
    simp [D, reducedStress, ActivationBounds.angularValue, ActivationBounds.controlledValue,
      ActivationBounds.rescale, ActivationBounds.scaledDistance, referenceAngular]
  · intro T hT κ u η hu hη
    have hηJ := hKJ hη
    obtain ⟨hfa, hfb⟩ := hfactors T hT.ne' κ u η hηJ
    obtain ⟨hma, hmb⟩ := hmatch (T * u) hu η hη
    rw [hma] at hfa
    rw [hmb] at hfb
    have hpa : activatedStockOne h X0 initial L U T κ (T * u, η) =
        referenceP1 L (T * u, η) + T * u * activation 1 κ u * dA ((κ, T), (u, η)) := by
      dsimp only [ActivationBounds.scaledDistance] at hfa
      change activatedStockOne h X0 initial L U T κ (T * u, η) - _ = _ at hfa
      linarith
    have hpb : activatedStockTwo h X0 initial L U T κ (T * u, η) =
        referenceP2 X0 L U (T * u, η) + T * u * activation 1 κ u * dB ((κ, T), (u, η)) := by
      dsimp only [ActivationBounds.scaledDistance] at hfb
      change activatedStockTwo h X0 initial L U T κ (T * u, η) - _ = _ at hfb
      linarith
    have hir := inverse_relative_scaled_factor hT.ne' κ hJ hL u hηJ
    have hratio : referenceAngular L (T * u, η) / activatedAngular T κ L (T * u, η) =
        1 + T * u * activation 1 κ u * inverseRelativeError L ((κ, T), (u, η)) := by
      dsimp only [ActivationBounds.scaledDistance] at hir
      linarith
    have hF : ActivationBounds.angularValue L ((κ, T), (u, η)) =
        activatedAngular T κ L (T * u, η) := by
      unfold ActivationBounds.angularValue activatedAngular
      rw [ActivationBounds.controlledValue_eq hT.ne' κ hJ hL u hηJ]
    have hdamp : damping T κ (T * u) = damping 1 κ u := by
      unfold damping
      rw [ActivationBounds.activation_scaled hT.ne']
    unfold activatedStress
    rw [hpa, hpb, actualP1_eq T κ hJ hL (T * u) hηJ,
      actualP2_eq T κ hX0 hJ hU (T * u) hηJ, hdamp, hratio]
    dsimp only [D, ActivationBounds.rescale]
    rw [hF]
    exact stress_factorization _ _ _ _ _ _ _ _ _ rfl

/-- The comparison estimates are derived from genuine log histories and
the constructed reciprocal-field factor. Uniform stock estimates are
obtained internally from their proved smooth factors. -/
theorem actual_comparisons (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (initial : HistoryRow → ℝ → ℝ) {J K : Set ℝ} (hJ : IsOpen J)
    (hK : IsCompact K) (hKJ : K ⊆ J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hi : ∀ r, ContDiffOn ℝ ∞ (initial r) J)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    {T0 Mref : ℝ} (hT0 : T0 ≤ 1) (hMref : 0 ≤ Mref)
    (href : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ K,
      referenceP1 L (y, η) ≠ 0 ∧
      |referenceP2 X0 L U (y, η)| ≤ Mref ∧
      |referenceP2 X0 L U (y, η) / referenceP1 L (y, η)| ≤ Mref ∧
      |referenceP2 X0 L U (y, η) ^ 2 / referenceP1 L (y, η)| ≤ Mref)
    (hmatch : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ K,
      ActivationStocks.logViewOne h X0 (referenceAngular L)
          (logHistory X0 initial (referenceAngular L) U) (y, η) = referenceP1 L (y, η) ∧
      ActivationStocks.logViewTwo h X0 (referenceAngular L) U
          (logHistory X0 initial (referenceAngular L) U) (y, η) = referenceP2 X0 L U (y, η)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Ioo (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |activatedProjection h X0 initial L U T κ (y, η) - referenceSize X0 L U (y, η)| ≤
          C * y * activation T κ y ∧
        |shearSize T κ X0 L U (y, η) - damping T κ y * referenceSize X0 L U (y, η)| ≤
          C * y * activation T κ y ∧
        |activatedCross h X0 initial L U T κ (y, η)| ≤ C * y * activation T κ y := by
  obtain ⟨Cs, hCs, hs⟩ := ActivationStocks.log_stocks_uniform_jets h hX0 initial hJ hL hU hi hcoef hK hKJ T0 0
  obtain ⟨Cr, hCr, hr⟩ := inverse_relative_uniform_jets hJ hK hKJ hL T0 0
  let M := max Mref (max Cs Cr)
  have hM : 0 ≤ M := hMref.trans (le_max_left _ _)
  have hrefM : Mref ≤ M := le_max_left _ _
  have hsM : Cs ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hrM : Cr ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨comparisonConstant M, by unfold comparisonConstant; positivity, ?_⟩
  intro T hT κ hκ y hy η hη
  have hy0 : y ∈ Icc (0 : ℝ) T0 := ⟨hy.1, hy.2.trans hT.2⟩
  have hηJ := hKJ hη
  have hκcc : κ ∈ Icc (0 : ℝ) 1 := ⟨hκ.1.le, hκ.2.le⟩
  have hκoc : κ ∈ Ioc (0 : ℝ) 1 := ⟨hκ.1, hκ.2.le⟩
  have he0 := activation_nonneg T κ y hκ.2.le
  have he1 := activation_le_one T κ y hκcc
  have hz : 0 ≤ y * activation T κ y := mul_nonneg hy.1 he0
  have hz1 : y * activation T κ y ≤ 1 := by
    exact (mul_le_of_le_one_right hy.1 he1).trans (hy0.2.trans hT0)
  have hdamp : |damping T κ y| ≤ 1 := by
    rw [abs_of_nonneg (damping_pos T κ y hκoc).le]
    unfold damping
    linarith
  obtain ⟨ha, hb, hba, hb2⟩ := href y hy0 η hη
  obtain ⟨hm1, hm2⟩ := hmatch y hy0 η hη
  have hsval := hs T hT κ hκcc y hy η hη
  simp only [iteratedDeriv_zero, hm1, hm2] at hsval
  have hpbound : |activatedStockOne h X0 initial L U T κ (y, η) - referenceP1 L (y, η)| ≤
      M * (y * activation T κ y) := by
    exact hsval.1.trans (by nlinarith [mul_le_mul_of_nonneg_right hsM hz])
  have hqbound : |activatedStockTwo h X0 initial L U T κ (y, η) - referenceP2 X0 L U (y, η)| ≤
      M * (y * activation T κ y) := by
    exact hsval.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hsM hz])
  have hrval := hr T hT κ hκcc y hy η hη
  simp only [iteratedDeriv_zero] at hrval
  have hrbound : |referenceAngular L (y, η) / activatedAngular T κ L (y, η) - 1| ≤
      M * (y * activation T κ y) :=
    hrval.trans (by nlinarith [mul_le_mul_of_nonneg_right hrM hz])
  have hcomp := cone_comparison_from_stock_bounds hM ha hdamp hz hz1
    (hb.trans hrefM) (hba.trans hrefM) (hb2.trans hrefM) hpbound hqbound hrbound
  unfold activatedProjection activatedCross
  rw [shearSlope_eq T hκoc hX0 hJ hL hU y hηJ ha,
    shearSize_eq T hκoc hX0 hJ hL hU y hηJ ha]
  simpa only [referenceSize, mul_assoc] using hcomp

/-- A strict initial reference margin persists on one common radial collar.
The collar is obtained from actual uniform continuity on a compact set. -/
theorem compact_reference_collar {K : Set ℝ} (hK : IsCompact K)
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c) {r : Field}
    (hr : ContinuousOn r (Icc (0 : ℝ) T ×ˢ K))
    (hzero : ∀ η ∈ K, 2 + 2 * c ≤ r (0, η)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ ∀ y ∈ Icc (0 : ℝ) τ, ∀ η ∈ K,
      2 + c < r (y, η) := by
  have hu := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hr
  obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff.mp hu c hc
  refine ⟨min T (δ / 2), lt_min hT (by positivity), min_le_left _ _, ?_⟩
  intro y hy η hη
  have hyT : y ≤ T := hy.2.trans (min_le_left _ _)
  have hyd : y < δ := by have := hy.2.trans (min_le_right _ _); linarith
  have hd : dist (y, η) (0, η) < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      abs_of_nonneg hy.1, max_eq_left hy.1] using hyd
  have hclose := hδprop (y, η) ⟨⟨hy.1, hyT⟩, hη⟩ (0, η) ⟨⟨le_rfl, hT.le⟩, hη⟩ hd
  have habs : |r (y, η) - r (0, η)| < c := by simpa only [Real.dist_eq] using hclose
  have hlo := (abs_lt.mp habs).1
  linarith [hzero η hη]

/-- Compact reference data provide all fixed bounds needed by the algebraic
error transport and a genuine common initial cone collar. -/
theorem compact_reference_bounds {K : Set ℝ} (hK : IsCompact K)
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c) {A B : Field}
    (hA : ContinuousOn A (Icc (0 : ℝ) T ×ˢ K))
    (hB : ContinuousOn B (Icc (0 : ℝ) T ×ˢ K))
    (hApos : ∀ p ∈ Icc (0 : ℝ) T ×ˢ K, 0 < A p)
    (hzero : ∀ η ∈ K, 2 + 2 * c ≤ A (0, η) + B (0, η) ^ 2 / A (0, η)) :
    ∃ τ α M : ℝ, 0 < τ ∧ τ ≤ T ∧ 0 < α ∧ 1 ≤ M ∧
      ∀ y ∈ Icc (0 : ℝ) τ, ∀ η ∈ K,
        α ≤ A (y, η) ∧ 2 + c < A (y, η) + B (y, η) ^ 2 / A (y, η) ∧
        A (y, η) + B (y, η) ^ 2 / A (y, η) ≤ M ∧
        |B (y, η)| ≤ M ∧ |B (y, η) / A (y, η)| ≤ M ∧
        |B (y, η) ^ 2 / A (y, η)| ≤ M := by
  let D := Icc (0 : ℝ) T ×ˢ K
  have hD : IsCompact D := isCompact_Icc.prod hK
  have hne : ∀ p ∈ D, A p ≠ 0 := fun p hp => (hApos p hp).ne'
  have hR : ContinuousOn (fun p => A p + B p ^ 2 / A p) D := hA.add ((hB.pow 2).div hA hne)
  obtain ⟨τ, hτ, hτT, hcollar⟩ := compact_reference_collar hK hT hc hR hzero
  obtain ⟨α, hα, hαbound⟩ := UniformCone.positive_uniform_margin hD hA hApos
  let g : Field := fun p => |B p| + |B p / A p| + |B p ^ 2 / A p| + |A p + B p ^ 2 / A p|
  have hg : ContinuousOn g D :=
    ((hB.abs.add ((hB.div hA hne).abs)).add (((hB.pow 2).div hA hne).abs)).add hR.abs
  obtain ⟨M, hM⟩ := (hD.image_of_continuousOn hg).bddAbove
  refine ⟨τ, α, max 1 M, hτ, hτT, hα, le_max_left _ _, ?_⟩
  intro y hy η hη
  have hp : (y, η) ∈ D := ⟨⟨hy.1, hy.2.trans hτT⟩, hη⟩
  have hb : g (y, η) ≤ max 1 M := (hM (mem_image_of_mem g hp)).trans (le_max_right _ _)
  dsimp only [g] at hb
  refine ⟨hαbound (y, η) hp, hcollar y hy η hη, ?_, ?_, ?_, ?_⟩
  · linarith [le_abs_self (A (y, η) + B (y, η) ^ 2 / A (y, η)),
      abs_nonneg (B (y, η)), abs_nonneg (B (y, η) / A (y, η)), abs_nonneg (B (y, η) ^ 2 / A (y, η))]
  · linarith [abs_nonneg (B (y, η) / A (y, η)), abs_nonneg (B (y, η) ^ 2 / A (y, η)),
      abs_nonneg (A (y, η) + B (y, η) ^ 2 / A (y, η))]
  · linarith [abs_nonneg (B (y, η)), abs_nonneg (B (y, η) ^ 2 / A (y, η)),
      abs_nonneg (A (y, η) + B (y, η) ^ 2 / A (y, η))]
  · linarith [abs_nonneg (B (y, η)), abs_nonneg (B (y, η) / A (y, η)),
      abs_nonneg (A (y, η) + B (y, η) ^ 2 / A (y, η))]

private theorem radialPartial_eq_partialY {F : Field} {p : Point}
    (hF : ContDiffAt ℝ ∞ F p) : radialPartial F p = NaturalAxisBridge.partialY F p := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv.symm

section NaturalReference

open ReferencePath
variable (N : ReferencePath.Input)

theorem referenceP1_natural {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < rampLimit)
    {y η : ℝ} (hy : y ≤ δ) (hη : η ∈ parameterInterval) :
    referenceP1 (FromReference.refLog N δ) (y, η) =
      NaturalEntrance.p1 N.f (N.fromLog (y, η)) := by
  have hp : (y, η) ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval parameterInterval_open).carrier :=
    ⟨show y < rampLimit by linarith, hη⟩
  have href := radialPartial_hasDerivAt (logDomain parameterInterval parameterInterval_open)
    (FromReference.refLog_smooth N hδ hδlim) (p := (y, η)) ⟨mem_univ _, hη⟩
  have hnat := continuation_hasDerivAt rampLimit_pos hδ hδlim parameterInterval_open N.logF_smooth (p := (y, η)) hη
  have hd : radialPartial (FromReference.refLog N δ) (y, η) = radialPartial N.logF (y, η) := by
    simpa only [FromReference.refLog, slopeCutoff_one hδ hy, one_mul] using href.unique hnat
  rw [referenceP1, hd, N.radialPartial_logF hp]
  rw [radialPartial_eq_partialY (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds (N.fromLog_mem hp)))]
  unfold NaturalEntrance.p1
  ring

theorem referenceP2_natural {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < rampLimit)
    {y η : ℝ} (hy : y ≤ δ) (hη : η ∈ parameterInterval) :
    referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ) (y, η) =
      NaturalEntrance.p2 N.f N.U (N.fromLog (y, η)) := by
  have hp : (y, η) ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval parameterInterval_open).carrier :=
    ⟨show y < rampLimit by linarith, hη⟩
  have href := radialPartial_hasDerivAt (logDomain parameterInterval parameterInterval_open)
    (FromReference.refAxial_smooth N hδ hδlim) (p := (y, η)) ⟨mem_univ _, hη⟩
  have hnat := continuation_hasDerivAt rampLimit_pos hδ hδlim parameterInterval_open N.logU_smooth (p := (y, η)) hη
  have hd : radialPartial (FromReference.refAxial N δ) (y, η) = radialPartial N.logU (y, η) := by
    simpa only [FromReference.refAxial, slopeCutoff_one hδ hy, one_mul] using href.unique hnat
  have hf : referenceAngular (FromReference.refLog N δ) (y, η) = N.f (N.fromLog (y, η)) := by
    unfold referenceAngular FromReference.refLog
    rw [continuation_eq_natural rampLimit_pos hδ hδlim parameterInterval_open N.logF_smooth hη hy]
    exact Real.exp_log (N.fromLog_f_pos hp)
  rw [referenceP2, hd, N.radialPartial_logU hp]
  rw [radialPartial_eq_partialY (N.U_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds (N.fromLog_mem hp)))]
  dsimp only [velocity]
  rw [hf]
  dsimp only [NaturalEntrance.p2, NaturalEntrance.ns, NaturalEntrance.angularVelocity, radius, Input.fromLog]
  ring

theorem referenceP1_smooth {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (referenceP1 (FromReference.refLog N δ))
      (logDomain parameterInterval parameterInterval_open).carrier :=
  contDiffOn_const.mul (radialPartial_smooth (logDomain parameterInterval parameterInterval_open)
    (FromReference.refLog_smooth N hδ hδlim))

theorem referenceP2_smooth {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ))
      (logDomain parameterInterval parameterInterval_open).carrier := by
  have hs : ContDiff ℝ ∞ (fun p : Point => Real.sqrt (2 * radius N.endpoint p.1)) :=
    (contDiff_const.mul (contDiff_const.mul (Real.contDiff_exp.comp contDiff_fst))).sqrt
      (fun p => (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos N.endpoint_pos (Real.exp_pos p.1))).ne')
  have he : ContDiffOn ℝ ∞ (referenceAngular (FromReference.refLog N δ))
      (logDomain parameterInterval parameterInterval_open).carrier :=
    Real.contDiff_exp.comp_contDiffOn (FromReference.refLog_smooth N hδ hδlim)
  exact (contDiffOn_const.mul (radialPartial_smooth (logDomain parameterInterval parameterInterval_open)
    (FromReference.refAxial_smooth N hδ hδlim))).div (hs.contDiffOn.mul he)
    (fun p _ => (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) (mul_pos N.endpoint_pos (Real.exp_pos p.1))))
      (Real.exp_pos _)).ne')

end NaturalReference

/-- The compact reference bounds are obtained for the actual constructed
natural entrance profile, not supplied as extra estimates. The reference
cutoff width is fixed while the later activation width is allowed to shrink. -/
theorem natural_reference_bounds {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < ReferencePath.rampLimit) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let A := referenceP1 (FromReference.refLog N δ)
    let B := referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ)
    ∃ τ α M : ℝ, 0 < τ ∧ τ ≤ δ ∧ 0 < α ∧ 1 ≤ M ∧
      ∀ y ∈ Icc (0 : ℝ) τ, ∀ η ∈ Icc (-1 : ℝ) 1,
        α ≤ A (y, η) ∧ 2 + 1 / 8 < A (y, η) + B (y, η) ^ 2 / A (y, η) ∧
        A (y, η) + B (y, η) ^ 2 / A (y, η) ≤ M ∧
        |B (y, η)| ≤ M ∧ |B (y, η) / A (y, η)| ≤ M ∧ |B (y, η) ^ 2 / A (y, η)| ≤ M := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let A := referenceP1 (FromReference.refLog N δ)
  let B := referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ)
  have hsub : Icc (0 : ℝ) δ ×ˢ Icc (-1 : ℝ) 1 ⊆
      (logDomain ReferencePath.parameterInterval ReferencePath.parameterInterval_open).carrier :=
    fun p hp => ⟨mem_univ _, NaturalAxisCoefficients.original_interval_interior hp.2⟩
  apply compact_reference_bounds isCompact_Icc hδ (by norm_num : (0 : ℝ) < 1 / 8)
    ((referenceP1_smooth N hδ hδlim).continuousOn.mono hsub)
    ((referenceP2_smooth N hδ hδlim).continuousOn.mono hsub)
  · intro p hp
    rw [referenceP1_natural N hδ hδlim hp.1.2 (NaturalAxisCoefficients.original_interval_interior hp.2)]
    apply F.slope_positive
    · change (Λ * (N.fromLog p).1, p.2) ∈ NaturalEntrance.entranceSet
      have he : Real.exp p.1 < 41 / 40 := by
        have hy : p.1 < ReferencePath.rampLimit := by linarith [hp.1.2]
        simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)]
          using Real.exp_lt_exp.mpr hy
      have hid : Λ * (N.fromLog p).1 = 4 * Real.exp p.1 := N.fromLog_scaled p
      exact ⟨⟨by rw [hid]; positivity, by rw [hid]; linarith⟩, hp.2⟩
    · exact mul_pos N.endpoint_pos (Real.exp_pos p.1)
  · intro η hη
    rw [referenceP1_natural N hδ hδlim (by linarith) (NaturalAxisCoefficients.original_interval_interior hη),
      referenceP2_natural N hδ hδlim (by linarith) (NaturalAxisCoefficients.original_interval_interior hη)]
    have hm := F.cone_margin η hη
    rw [show (2 + 2 * (1 / 8) : ℝ) = 9 / 4 by norm_num]
    simpa only [NaturalEntrance.coneSize, ReferencePath.Input.fromLog, Real.exp_zero,
      mul_one, N, ReferencePath.Input.endpoint, ReferencePath.Input.ofNatural] using hm.le

theorem natural_reference_log_match {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalProfile.ProfileFamily d Λ C) (hP0 : ContDiff ℝ ∞ P0)
    (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < ReferencePath.rampLimit)
    {y η : ℝ} (hy : y ≤ δ) (hη : η ∈ Icc (-1 : ℝ) 1) :
    let N := ReferencePath.Input.ofNatural hΛ F
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    ActivationStocks.logViewOne h N.endpoint (referenceAngular L)
        (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP1 L (y, η) ∧
      ActivationStocks.logViewTwo h N.endpoint (referenceAngular L) U
        (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP2 N.endpoint L U (y, η) := by
  let N := ReferencePath.Input.ofNatural hΛ F
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hm := ActivationStocks.reference_stocks_natural F hΛ hP0 hδ hδlim hsmall y hy hη
  have hv1 := ActivationStocks.FromReference.reference_stockOne_logView N hδ hδlim h P0 hP0 y hηJ
  have hv2 := ActivationStocks.FromReference.reference_stockTwo_logView N hδ hδlim h P0 hP0 y hηJ
  have hn1 := referenceP1_natural N hδ hδlim hy hηJ
  have hn2 := referenceP2_natural N hδ hδlim hy hηJ
  exact ⟨hv1.symm.trans (hm.1.trans hn1.symm), hv2.symm.trans (hm.2.trans hn2.symm)⟩

/-- The initial activation assertion is proved for the actual natural entrance
and its actual recomputed lag histories. Both the ramp width and the first
collar fraction are chosen uniformly in `κ₀ ∈ (0,1)`. -/
theorem natural_initial_activation {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < ReferencePath.rampLimit) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    ∃ Tstar θ : ℝ, 0 < Tstar ∧ Tstar ≤ δ ∧ 0 < θ ∧ θ ≤ 1 ∧
      ∀ T ∈ Ioc (0 : ℝ) Tstar, ∀ κ ∈ Ioo (0 : ℝ) 1,
        ∀ y ∈ Ioc (0 : ℝ) T, ∀ η ∈ Icc (-1 : ℝ) 1,
          activation T κ y ≤ activatedProjection h N.endpoint I L U T κ (y, η) -
            shearSize T κ N.endpoint L U (y, η) ∧
          2 + 1 / 32 < activatedProjection h N.endpoint I L U T κ (y, η) ∧
          (shearSize T κ N.endpoint L U (y, η) - 2) *
              activatedCross h N.endpoint I L U T κ (y, η) ^ 2 <
            2 * (activatedProjection h N.endpoint I L U T κ (y, η) -
              shearSize T κ N.endpoint L U (y, η)) ^ 2 ∧
          shearSize T κ N.endpoint L U (y, η) <
            coneBound (activatedProjection h N.endpoint I L U T κ (y, η))
              (activatedCross h N.endpoint I L U T κ (y, η)) ∧
          (y ≤ θ * T → 2 + 1 / 16 < shearSize T κ N.endpoint L U (y, η)) := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let L := FromReference.refLog N δ
  let U := FromReference.refAxial N δ
  let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
  have hL := FromReference.refLog_smooth N hδ hδlim
  have hU := FromReference.refAxial_smooth N hδ hδlim
  have hi := ActivationStocks.FromReference.initial_smooth N hδ hδlim P0 hP0
  have hKJ : Icc (-1 : ℝ) 1 ⊆ ReferencePath.parameterInterval := NaturalAxisCoefficients.original_interval_interior
  have hcoef : ∀ η ∈ ReferencePath.parameterInterval, NaturalAxisData.L h η ≠ 0 := by
    intro η hη
    exact (NaturalAxisCoefficients.L_pos_on_window (NaturalAxisRange.ofSmall hsmall) ⟨hη.1.le, hη.2.le⟩).ne'
  obtain ⟨τ, α, M, hτ, hτδ, hα, hM, hb⟩ := natural_reference_bounds hΛ F hδ hδlim
  let T0 := min τ 1
  have hT0 : 0 < T0 := lt_min hτ zero_lt_one
  have hT0τ : T0 ≤ τ := min_le_left _ _
  have hT0δ : T0 ≤ δ := hT0τ.trans hτδ
  have hM0 : 0 ≤ M := by linarith
  have href : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ Icc (-1 : ℝ) 1,
      referenceP1 L (y, η) ≠ 0 ∧ |referenceP2 N.endpoint L U (y, η)| ≤ M ∧
      |referenceP2 N.endpoint L U (y, η) / referenceP1 L (y, η)| ≤ M ∧
      |referenceP2 N.endpoint L U (y, η) ^ 2 / referenceP1 L (y, η)| ≤ M := by
    intro y hy η hη
    have hx := hb y ⟨hy.1, hy.2.trans hT0τ⟩ η hη
    exact ⟨(hα.trans_le hx.1).ne', hx.2.2.2⟩
  have hm : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ Icc (-1 : ℝ) 1,
      ActivationStocks.logViewOne h N.endpoint (referenceAngular L)
          (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP1 L (y, η) ∧
      ActivationStocks.logViewTwo h N.endpoint (referenceAngular L) U
          (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP2 N.endpoint L U (y, η) := by
    intro y hy η hη
    exact natural_reference_log_match hΛ F.profile.family hP0 hsmall hδ hδlim (hy.2.trans hT0δ) hη
  obtain ⟨Cerr, hCerr, he⟩ := actual_comparisons h N.endpoint_pos I ReferencePath.parameterInterval_open
    isCompact_Icc hKJ hL hU hi hcoef (min_le_right τ 1) hM0 href hm
  have hr : ∀ y ∈ Icc (0 : ℝ) T0, ∀ η ∈ Icc (-1 : ℝ) 1,
      2 + 1 / 8 ≤ referenceSize N.endpoint L U (y, η) ∧ referenceSize N.endpoint L U (y, η) ≤ M := by
    intro y hy η hη
    have hx := hb y ⟨hy.1, hy.2.trans hT0τ⟩ η hη
    exact ⟨hx.2.1.le, hx.2.2.1⟩
  obtain ⟨Tstar, θ, hTs, hTs0, hθ, hθ1, hcone⟩ :=
    uniform_ramp_from_comparison (by norm_num : (0 : ℝ) < 1 / 8) hM0 hCerr hT0 hr he
  refine ⟨Tstar, θ, hTs, hTs0.trans hT0δ, hθ, hθ1, ?_⟩
  simpa only [show ((1 / 8 : ℝ) / 4) = 1 / 32 by norm_num,
    show ((1 / 8 : ℝ) / 2) = 1 / 16 by norm_num] using hcone

/-- The normalized stress of the actual activation extends smoothly to the
inner edge, where its first component and angular directional margin have
one positive lower bound, uniform in all activation parameters. -/
theorem natural_activation_direction {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < ReferencePath.rampLimit) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    ∃ D : ActivationBounds.ScaledPoint → ℝ × ℝ, ∃ ε : ℝ,
      ContDiffOn ℝ ∞ D (ActivationBounds.scaledDomain ReferencePath.parameterInterval) ∧ 0 < ε ∧
      (∀ κ T η : ℝ, η ∈ Icc (-1 : ℝ) 1 →
        ε ≤ (D ((κ, T), (0, η))).1 ∧
        ε ≤ (D ((κ, T), (0, η))).1 +
          (referenceP2 N.endpoint L U (0, η) / referenceP1 L (0, η)) *
            (D ((κ, T), (0, η))).2 - 2 * referenceAngular L (0, η)) ∧
      ∀ T : ℝ, 0 < T → ∀ κ u η : ℝ, T * u ∈ Icc (0 : ℝ) δ → η ∈ Icc (-1 : ℝ) 1 →
        activatedStress h N.endpoint I L U T κ (T * u, η) =
          (activation 1 κ u * (D ((κ, T), (u, η))).1,
            activation 1 κ u * (D ((κ, T), (u, η))).2) := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let L := FromReference.refLog N δ
  let U := FromReference.refAxial N δ
  let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
  let K := Icc (-1 : ℝ) 1
  have hL := FromReference.refLog_smooth N hδ hδlim
  have hU := FromReference.refAxial_smooth N hδ hδlim
  have hi := ActivationStocks.FromReference.initial_smooth N hδ hδlim P0 hP0
  have hKJ : K ⊆ ReferencePath.parameterInterval := NaturalAxisCoefficients.original_interval_interior
  have hcoef : ∀ η ∈ ReferencePath.parameterInterval, NaturalAxisData.L h η ≠ 0 := by
    intro η hη
    exact (NaturalAxisCoefficients.L_pos_on_window (NaturalAxisRange.ofSmall hsmall) ⟨hη.1.le, hη.2.le⟩).ne'
  have hm : ∀ y ∈ Icc (0 : ℝ) δ, ∀ η ∈ K,
      ActivationStocks.logViewOne h N.endpoint (referenceAngular L)
          (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP1 L (y, η) ∧
      ActivationStocks.logViewTwo h N.endpoint (referenceAngular L) U
          (logHistory N.endpoint I (referenceAngular L) U) (y, η) = referenceP2 N.endpoint L U (y, η) := by
    intro y hy η hη
    exact natural_reference_log_match hΛ F.profile.family hP0 hsmall hδ hδlim hy.2 hη
  obtain ⟨D, hD, hedge, hfactor⟩ := exists_actual_stress_direction h N.endpoint_pos I
    ReferencePath.parameterInterval_open hKJ hL hU hi hcoef hm
  obtain ⟨τ, α, M, hτ, _, hα, _, hb⟩ := natural_reference_bounds hΛ F hδ hδlim
  have hmap : Set.MapsTo (fun η : ℝ => (0, η)) K
      (logDomain ReferencePath.parameterInterval ReferencePath.parameterInterval_open).carrier :=
    fun η hη => ⟨mem_univ _, hKJ hη⟩
  have hA : ContinuousOn (fun η => referenceP1 L (0, η)) K :=
    (referenceP1_smooth N hδ hδlim).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hB : ContinuousOn (fun η => referenceP2 N.endpoint L U (0, η)) K :=
    (referenceP2_smooth N hδ hδlim).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hF : ContinuousOn (fun η => referenceAngular L (0, η)) K :=
    hL.exp.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hApos : ∀ η ∈ K, 0 < referenceP1 L (0, η) := by
    intro η hη
    exact hα.trans_le (hb 0 ⟨le_rfl, hτ.le⟩ η hη).1
  let first : ℝ → ℝ := fun η => referenceAngular L (0, η) * referenceP1 L (0, η)
  let margin : ℝ → ℝ := fun η => referenceAngular L (0, η) *
    (referenceP1 L (0, η) + referenceP2 N.endpoint L U (0, η) ^ 2 / referenceP1 L (0, η) - 2)
  have hfirst : ContinuousOn first K := hF.mul hA
  have hmargin : ContinuousOn margin K := hF.mul
    ((hA.add ((hB.pow 2).div hA (fun η hη => (hApos η hη).ne'))).sub continuousOn_const)
  obtain ⟨ε1, hε1, hbound1⟩ := UniformCone.positive_uniform_margin isCompact_Icc hfirst
    (fun η hη => mul_pos (Real.exp_pos _) (hApos η hη))
  obtain ⟨ε2, hε2, hbound2⟩ := UniformCone.positive_uniform_margin isCompact_Icc hmargin (by
    intro η hη
    apply mul_pos (Real.exp_pos _)
    have hr := (hb 0 ⟨le_rfl, hτ.le⟩ η hη).2.1
    linarith)
  refine ⟨D, min ε1 ε2, hD, lt_min hε1 hε2, ?_, hfactor⟩
  intro κ T η hη
  rw [hedge]
  refine ⟨(min_le_left _ _).trans (hbound1 η hη), ?_⟩
  have hid : referenceAngular L (0, η) * referenceP1 L (0, η) +
      (referenceP2 N.endpoint L U (0, η) / referenceP1 L (0, η)) *
        (referenceAngular L (0, η) * referenceP2 N.endpoint L U (0, η)) -
          2 * referenceAngular L (0, η) = margin η := by
    dsimp only [margin]
    ring
  exact (min_le_right _ _).trans (hid ▸ hbound2 η hη)

end NavierStokes.ActivationCone

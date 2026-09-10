import NavierStokes.GenericRealization
import NavierStokes.DirectAngularDiagonal
import NavierStokes.MixedPeriodicAssembly

noncomputable section

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement
open scoped Topology ContDiff BigOperators

/-- A component which vanishes on its coordinate line has zero corresponding
diagonal Jacobian entry. This argument is valid on the axis itself. -/
theorem diagonal_entry_zero_of_line {F : Space → Space} {x : Space}
    (hF : DifferentiableAt ℝ F x) (i : Fin 3)
    (hz : ∀ r : ℝ, F (x + r • coordinateVector i) i = 0) :
    (fderiv ℝ F x (coordinateVector i)) i = 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • coordinateVector i)
      (coordinateVector i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add x using 1
    simp
  have hFx : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • coordinateVector i) := by
    simpa only [zero_smul, add_zero] using hF.hasFDerivAt
  have hcomp := hFx.comp_hasDerivAt (0 : ℝ) hline
  have hproj := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp
  have hd := hproj.deriv
  change deriv (fun r : ℝ => F (x + r • coordinateVector i) i) 0 =
    (fderiv ℝ F x (coordinateVector i)) i at hd
  have heq : (fun r : ℝ => F (x + r • coordinateVector i) i) = (fun _ => (0 : ℝ)) := funext hz
  rw [heq] at hd
  simpa using hd.symm

/-- Smooth Cartesian angular fields are divergence-free on the axis, even
when no neighborhood of that axis is removed from their support. -/
theorem angular_divergence_axis (b : DirectAngularDiagonal.Coefficient) {w : SpaceTime}
    (hB : DifferentiableAt ℝ (fun x : Space => DirectAngularDiagonal.angularField b (w.1, x)) w.2)
    (h0 : w.2 0 = 0) (h1 : w.2 1 = 0) :
    spatialDivergence (DirectAngularDiagonal.angularField b) w.1 w.2 = 0 := by
  have hentry : ∀ i : Fin 3,
      (fderiv ℝ (fun x : Space => DirectAngularDiagonal.angularField b (w.1, x)) w.2
        (coordinateVector i)) i = 0 := by
    intro i
    apply diagonal_entry_zero_of_line hB i
    intro r
    fin_cases i <;> simp [DirectAngularDiagonal.angularField, coordinateVector,
      h0, h1, PiLp.add_apply, PiLp.smul_apply]
  change (∑ i : Fin 3, _) = 0
  exact Finset.sum_eq_zero (fun i _ => hentry i)

/-- General smooth angular representatives need no annular support assumption.
Off the axis, the ordinary cylindrical coefficient calculation applies; at
the axis the preceding coordinate-line argument supplies the missing value. -/
theorem angular_divergence (b : DirectAngularDiagonal.Coefficient) {w : SpaceTime}
    (hB : DifferentiableAt ℝ (fun x : Space => DirectAngularDiagonal.angularField b (w.1, x)) w.2)
    (hb : 0 < DirectAngularDiagonal.radius w →
      DifferentiableAt ℝ (DirectAngularDiagonal.rate b)
        (AxisymmetricFields.profilePoint w.1 w.2)) :
    spatialDivergence (DirectAngularDiagonal.angularField b) w.1 w.2 = 0 := by
  by_cases hr : 0 < DirectAngularDiagonal.radius w
  · rw [DirectAngularDiagonal.angularField_eq_rotationField]
    exact DirectAngularDiagonal.divergence_rotationField (hb hr)
  · have hs : w.2 0 ^ 2 + w.2 1 ^ 2 = 0 := by
      have hz := le_antisymm (le_of_not_gt hr) (DirectAngularDiagonal.radius_nonneg w)
      change Real.sqrt (w.2 0 ^ 2 + w.2 1 ^ 2) = 0 at hz
      nlinarith [Real.sq_sqrt (show 0 ≤ w.2 0 ^ 2 + w.2 1 ^ 2 by positivity)]
    apply angular_divergence_axis b hB <;> nlinarith [sq_nonneg (w.2 0), sq_nonneg (w.2 1)]

/-- The elementary product rule for a direct solenoidal field tangent to
the scale level sets. This includes the angular fields and `q(z,t)` of the
manuscript, without any requirement that the field vanish near the axis. -/
theorem divergence_cut_direct {q : SpaceTime → ℝ} {B : VelocityField} {w : SpaceTime}
    (hq : DifferentiableAt ℝ (fun x : Space => q (w.1, x)) w.2)
    (hB : DifferentiableAt ℝ (fun x : Space => B (w.1, x)) w.2)
    (hdiv : spatialDivergence B w.1 w.2 = 0)
    (htan : ∑ i : Fin 3, fderiv ℝ (fun x : Space => q (w.1, x)) w.2
      (coordinateVector i) * B w i = 0) (a : ℝ) :
    spatialDivergence (fun z => SmoothCutoffs.scaledCutoff a (q z) • B z) w.1 w.2 = 0 := by
  let χ := SmoothCutoffs.scaledCutoff a
  have hχ : DifferentiableAt ℝ χ (q w) :=
    ((SmoothCutoffs.scaledCutoff_contDiff a).differentiable (by simp)).differentiableAt
  have hc := hχ.hasDerivAt.comp_hasFDerivAt w.2 hq.hasFDerivAt
  change HasFDerivAt (fun x : Space => χ (q (w.1, x)))
    (deriv χ (q w) • fderiv ℝ (fun x : Space => q (w.1, x)) w.2) w.2 at hc
  have hc' : DifferentiableAt ℝ (fun x : Space => χ (q (w.1, x))) w.2 := hc.differentiableAt
  unfold spatialDivergence spatialDerivative
  rw [fderiv_fun_smul hc' hB, hc.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change χ (q w) * spatialDivergence B w.1 w.2 + _ = 0
  rw [hdiv, mul_zero, zero_add]
  have ht : ∑ i : Fin 3, deriv χ (q w) *
      (fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B w i) = 0 := by
    rw [← Finset.mul_sum, htan, mul_zero]
  simpa only [mul_assoc] using ht

/-- Tangency follows immediately when the scale depends only on the axial
coordinate and the direct field has zero axial component. -/
theorem tangent_of_axial_scale {q : SpaceTime → ℝ} {B : VelocityField} {w : SpaceTime}
    (h0 : fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector 0) = 0)
    (h1 : fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector 1) = 0)
    (hB : B w 2 = 0) :
    ∑ i : Fin 3, fderiv ℝ (fun x : Space => q (w.1, x)) w.2
      (coordinateVector i) * B w i = 0 := by
  rw [Fin.sum_univ_three, h0, h1, hB]
  ring

/-- An arbitrary locally finite direct diagonal remains solenoidal when its
uncut terms are solenoidal and tangent to the scale level sets. -/
theorem directSum_divergence {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hpos : ∀ w ∈ U, 0 < q w)
    (hdiv : ∀ j w, w ∈ U → spatialDivergence (B j) w.1 w.2 = 0)
    (htan : ∀ j w, w ∈ U → ∑ i : Fin 3,
      fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0)
    {w : SpaceTime} (hw : w ∈ U) :
    spatialDivergence (SolenoidalDiagonal.potentialSum a q B) w.1 w.2 = 0 := by
  have hqat := hq.contDiffAt (hU.mem_nhds hw)
  have hBat := fun j => (hB j).contDiffAt (hU.mem_nhds hw)
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha
    hqat.continuousAt (hpos w hw) B
  rw [DirectAngularDiagonal.divergence_congr hN]
  change spatialDivergence (fun y => ∑ j ∈ Finset.range N,
    SolenoidalDiagonal.cutStage a q B j y) w.1 w.2 = 0
  rw [DirectAngularDiagonal.divergence_finset_sum]
  · apply Finset.sum_eq_zero
    intro j _
    exact divergence_cut_direct
      ((hqat.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
      (((hBat j).comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
      (hdiv j w hw) (htan j w hw) (a j)
  · intro j _
    exact ((SolenoidalDiagonal.cutStage_contDiffAt hqat hBat j).comp w.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)

/-- Literal curl-after-cutoff realization, with a separate uncut base. -/
def velocity (a : ℕ → ℝ) (q : SpaceTime → ℝ) (u0 : VelocityField)
    (A B : ℕ → VelocityField) : VelocityField :=
  fun w => u0 w + SolenoidalDiagonal.velocitySum a q A w +
    SolenoidalDiagonal.potentialSum a q B w

theorem velocity_smooth {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U) : ContDiffOn ℝ ∞ (velocity a q u0 A B) U :=
  (hu0.add (SolenoidalDiagonal.velocitySum_contDiffOn ha hU hpos hq hA)).add
    (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hpos hq hB)

theorem velocity_divergence {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hdiv0 : ∀ w ∈ U, spatialDivergence u0 w.1 w.2 = 0)
    (hdivB : ∀ j w, w ∈ U → spatialDivergence (B j) w.1 w.2 = 0)
    (htan : ∀ j w, w ∈ U → ∑ i : Fin 3,
      fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0)
    {w : SpaceTime} (hw : w ∈ U) : spatialDivergence (velocity a q u0 A B) w.1 w.2 = 0 := by
  have h0 := ((hu0.contDiffAt (hU.mem_nhds hw)).comp w.2
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hAc := SolenoidalDiagonal.velocitySum_contDiffOn ha hU hpos hq hA
  have hAc' := ((hAc.contDiffAt (hU.mem_nhds hw)).comp w.2
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hBc := SolenoidalDiagonal.potentialSum_contDiffOn ha hU hpos hq hB
  have hBc' := ((hBc.contDiffAt (hU.mem_nhds hw)).comp w.2
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  unfold velocity
  rw [MixedPeriodicAssembly.spatialDivergence_add (h0.add hAc') hBc',
    MixedPeriodicAssembly.spatialDivergence_add h0 hAc', hdiv0 w hw,
    SolenoidalDiagonal.divergence_velocitySum_on ha hU hpos hq hA w hw,
    directSum_divergence ha hU hq hB hpos hdivB htan hw]
  simp

/-- The manuscript's sum starts at stage one; the base is left uncut. -/
def positiveVelocity (a : ℕ → ℝ) (q : SpaceTime → ℝ) (u0 : VelocityField)
    (A B : ℕ → VelocityField) : VelocityField :=
  velocity a q u0 (CutStageEstimates.positiveStages A) (CutStageEstimates.positiveStages B)

theorem positiveVelocity_divergence {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hu0 : ContDiffOn ℝ ∞ u0 U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hdiv0 : ∀ w ∈ U, spatialDivergence u0 w.1 w.2 = 0)
    (hdivB : ∀ j, 1 ≤ j → ∀ w ∈ U, spatialDivergence (B j) w.1 w.2 = 0)
    (htan : ∀ j, 1 ≤ j → ∀ w ∈ U, ∑ i : Fin 3,
      fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0)
    {w : SpaceTime} (hw : w ∈ U) :
    spatialDivergence (positiveVelocity a q u0 A B) w.1 w.2 = 0 := by
  apply velocity_divergence ha hU hq hpos hu0
    (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB) hdiv0
  · intro j x hx
    cases j with
    | zero => simp [CutStageEstimates.positiveStages_zero, spatialDivergence, spatialDerivative]
    | succ j =>
        rw [CutStageEstimates.positiveStages_of_pos (Nat.succ_pos j)]
        exact hdivB (j + 1) (Nat.succ_pos j) x hx
  · intro j x hx
    cases j with
    | zero => simp [CutStageEstimates.positiveStages_zero]
    | succ j =>
        rw [CutStageEstimates.positiveStages_of_pos (Nat.succ_pos j)]
        exact htan (j + 1) (Nat.succ_pos j) x hx
  · exact hw

/-- Curl commutes with the outer zero germ. Thus the complete velocity
correction, including derivatives of the cutoff, extends smoothly by zero. -/
theorem positiveVelocity_outer_germ {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : SpaceTime → ℝ} {w : SpaceTime}
    (hq : ContinuousAt q w) (houter : 1 / a 0 < q w)
    (u0 : VelocityField) (A B : ℕ → VelocityField) :
    positiveVelocity a q u0 A B =ᶠ[𝓝 w] u0 := by
  have hAz := GenericRealizationBounds.correction_eventually_zero ha hapos hq houter
    (CutStageEstimates.positiveStages A)
  have hBz := GenericRealizationBounds.correction_eventually_zero ha hapos hq houter
    (CutStageEstimates.positiveStages B)
  have hcurl := SolenoidalDiagonal.spatialCurl_eventuallyEq hAz
  filter_upwards [hcurl, hBz] with y hyA hyB
  change u0 y + SpatialCurl.spatialCurl
    (SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A)) y +
    SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages B) y = u0 y
  rw [hyA, hyB]
  simp [SpatialCurl.spatialCurl, SpatialCurl.curl]

end NavierStokes.GenericSolenoidalRealization

import NavierStokes.R3.CompactEnergy

/-!
# Compact whole-space energy balance at arbitrary viscosity

The dissipation is retained explicitly, so integrating the identity also
controls the total dissipation up to a possible singular time.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

/-- The exact compact-support energy identity with the viscosity retained. -/
theorem energy_balance_viscosity {ν : ℝ} {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    energyRate u t = -2 * ν * dissipation u t +
      2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ := by
  let g : VelocityField := fun z => f z + (ν - 1) • spatialLaplacian u z.1 z.2
  have hg : Continuous (fun x : Space => g (t, x)) :=
    hf.add ((spatialLaplacian_contDiff hu).continuous.const_smul (ν - 1))
  have hNSg : ∀ x, navierStokesResidual u p t x = g (t, x) := by
    intro x
    dsimp only [g]
    rw [← hNS x]
    unfold ProblemStatement.navierStokesResidual navierStokesResidual
    rw [sub_smul, one_smul]
    abel
  have hbalance := energy_balance hu hp hg hcu hdiv hNSg
  have hiF := integrable_inner_left hu.continuous hf hcu
  have hiL := integrable_inner_left hu.continuous (spatialLaplacian_contDiff hu).continuous hcu
  have hwork : (∫ x, ⟪u (t, x), g (t, x)⟫_ℝ) =
      (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) - (ν - 1) * dissipation u t := by
    simp only [g, inner_add_right, inner_smul_right]
    rw [integral_add hiF (hiL.const_mul (ν - 1)), integral_const_mul,
      integral_laplacian_energy hu hcu]
    simp only [dissipation]
    ring
  rw [hwork] at hbalance
  rw [hbalance]
  ring

/-- Differentiation of the energy and integration by parts at viscosity `ν`. -/
theorem hasDerivAt_energy_balance_viscosity {ν a b t : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    HasDerivAt (l2Sq u)
      (-2 * ν * dissipation u t + 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) t := by
  have h := energy_hasDerivAt hK hu hsupp ht
  rw [energy_balance_viscosity (spatial_smooth hu ⟨ht.1.le, ht.2.le⟩)
    (spatial_smooth hp ⟨ht.1.le, ht.2.le⟩) hf
    (slice_compact hK (hsupp t ⟨ht.1.le, ht.2.le⟩)) hdiv hNS] at h
  exact h

/-- Force work varies continuously on a closed smooth time slab. -/
theorem forceWork_continuousOn {a b : ℝ} {u f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContinuousOn u (slab a b))
    (hf : ContinuousOn f (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K) :
    ContinuousOn (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) (Icc a b) := by
  apply CompactTimeIntegral.continuousOn_integral (F := fun z => ⟪u z, f z⟫_ℝ) hK (hu.inner hf)
  intro t ht x hx
  rw [zero_outside (hsupp t ht) hx, inner_zero_left]

/-- Spatial partial derivatives are jointly continuous even at slab endpoints. -/
theorem spatialPartial_continuousOn_slab {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (i : Fin 3) :
    ContinuousOn (fun z : SpaceTime => spatialPartial i (fun y => u (z.1, y)) z.2)
      (slab a b) := by
  have hs : UniqueDiffOn ℝ (slab a b) := (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have horder : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)
  have hc := (hu.fderivWithin hs horder).continuousOn.clm_apply
    (show ContinuousOn (fun _ : SpaceTime => ((0 : ℝ), coordinateVector i)) (slab a b)
      from continuousOn_const)
  apply hc.congr
  intro z hz
  change spatialDerivative u z.1 z.2 (coordinateVector i) = _
  rw [spatialDerivative_eq_within_comp hu hz.1 z.2]
  rfl

/-- The spatially integrated dissipation is continuous on every nondegenerate
closed time slab with smooth velocity and a fixed compact spatial support. -/
theorem dissipation_continuousOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K) :
    ContinuousOn (dissipation u) (Icc a b) := by
  apply continuousOn_finsetSum
  intro i _
  apply CompactTimeIntegral.continuousOn_integral hK
    ((spatialPartial_continuousOn_slab hab hu i).norm.pow 2)
  intro t ht x hx
  have hnot : x ∉ tsupport (fun y => u (t, y)) := fun h => hx (hsupp t ht h)
  simp [spatialPartial, fderiv_of_notMem_tsupport ℝ hnot]

end NavierStokesR3.CompactEnergy

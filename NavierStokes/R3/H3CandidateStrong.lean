import NavierStokes.R3.L2TimeDerivative
import NavierStokes.R3.H3CompactCurve
import NavierStokes.R3.H3StrongSolution

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (temporalDerivative advection spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth time_differentiable_at_interior)

private theorem time_derivative {a b t : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (ht : t ∈ Ioo a b) (x : Space) :
    HasDerivAt (fun r => u (r, x)) (temporalDerivative u t x) t :=
  (time_differentiable_at_interior hu ht x).hasDerivAt

private theorem time_derivative_continuous {a b : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) :
    ContinuousOn (fun z => temporalDerivative u z.1 z.2) (Ioo a b ×ˢ univ) :=
  CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn (hu.of_le (by simp))

private theorem time_derivative_zero {a b t : ℝ} {u : VelocityField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b) {x : Space} (hx : x ∉ K) : temporalDerivative u t x = 0 := by
  exact CompactTimeIntegral.derivative_eq_zero_outside
    (G := fun z => temporalDerivative u z.1 z.2)
    (fun r hr y hy => CompactEnergy.zero_outside (hsupp r (Ioo_subset_Icc_self hr)) hy)
    (fun r hr y => time_derivative hu hr y) ht hx

theorem temporalDerivative_memLp_of_compact {a b t : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b) : MemLp (fun x => temporalDerivative u t x) 2 volume := by
  have hc := CompactTimeIntegral.continuous_slice (time_derivative_continuous hu) ht
  have hs : tsupport (fun x => temporalDerivative u t x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (time_derivative_zero hu hsupp ht hn)
  exact hc.memLp_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport _) hs)

/-- The exact ordinary time derivative of a compact smooth velocity is also
the derivative of its L²-valued time curve. -/
theorem hasDerivAt_velocityLp_of_compact {a b t : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b) (hc : H3Curve u (Icc a b)) :
    HasDerivAt hc.velocityLp
      ((temporalDerivative_memLp_of_compact hK hu hsupp ht).toLp
        (fun x => temporalDerivative u t x)) t := by
  let a' : ℝ := (a + t) / 2
  let b' : ℝ := (t + b) / 2
  have hsmall : Icc a' b' ⊆ Ioo a b := by
    intro r hr
    dsimp [a', b'] at hr
    constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
  have ht' : t ∈ Ioo a' b' := by
    dsimp [a', b']
    constructor <;> linarith [ht.1, ht.2]
  apply hasDerivAt_L2_of_compact_support hK
    (hu.continuousOn.mono (Set.prod_mono (hsmall.trans Ioo_subset_Icc_self) (Subset.refl _)))
    ((time_derivative_continuous hu).mono (Set.prod_mono hsmall (Subset.refl _)))
    (fun r hr x hx => CompactEnergy.zero_outside
      (hsupp r (Ioo_subset_Icc_self (hsmall hr))) hx)
    (fun r hr x hx => time_derivative_zero hu hsupp (hsmall hr) hx)
    (fun r hr x => time_derivative hu (hsmall hr) x) ht'
  · intro r hr
    rw [hc.velocityLp_eq (Ioo_subset_Icc_self (hsmall hr))]
    exact MemLp.coeFn_toLp _
  · exact MemLp.coeFn_toLp _

theorem weakAdvection_eq_advection (u : VelocityField) (t : ℝ) (x : Space) :
    weakAdvection (fun x => u (t, x))
      (fun i x => H3Compact.partialField i u (t, x)) x = advection u t x := by
  unfold advection
  conv_rhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates (u (t, x))]
  simp only [map_sum, map_smul]
  rfl

/-- All requirements of the ordinary classical H³ class follow from the
actual compact smooth solution on a shorter slab. -/
def strongSolution_of_compact_slab {ν a b : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hab : a < b) (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (hdiv : ∀ t ∈ Ioo a b, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo a b, ∀ x, navierStokesResidual ν u p t x = f (t, x)) :
    StrongSolutionOnIcc ν f a b u p where
  time_lt := hab
  curve := h3Curve_of_compact_slab hab hK hu hsupp
  timeDerivative := fun z => temporalDerivative u z.1 z.2
  timeDerivative_memLp := fun _ ht => temporalDerivative_memLp_of_compact hK hu hsupp ht
  hasDerivAt_velocity := fun _ ht => hasDerivAt_velocityLp_of_compact hK hu hsupp ht _
  pressure_C1 := fun _ ht => (spatial_smooth hp (Ioo_subset_Icc_self ht)).of_le (by simp)
  divergence_free := fun t ht => Filter.Eventually.of_forall (hdiv t ht)
  navier_stokes := fun t ht => Filter.Eventually.of_forall (fun x => by
    change temporalDerivative u t x + weakAdvection (fun x => u (t, x))
      (fun i x => H3Compact.partialField i u (t, x)) x -
      ν • NavierStokes.ProblemStatement.spatialLaplacian u t x +
      NavierStokes.ProblemStatement.pressureGradient p t x = _
    rw [weakAdvection_eq_advection]
    exact hNS t ht x)

/-- The actual candidate belongs to the ordinary classical H³ class on the
whole half-open interval [0,1). -/
def candidate_classicalH3Solution {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K) :
    ClassicalH3Solution ν f (fun _ => 0) 1 u p where
  lifespan_pos := zero_lt_one
  initial_velocity := h.zero_initial_velocity
  on_shorter_interval := fun _S hS => strongSolution_of_compact_slab hS.1 h.support_compact
    (h.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hS.2⟩, hz.2⟩))
    (h.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hS.2⟩, hz.2⟩))
    (fun t ht => h.velocity_support t ⟨ht.1, ht.2.trans_lt hS.2⟩)
    (fun t ht => h.divergence_free t ⟨ht.1.le, ht.2.trans hS.2⟩)
    (fun t ht => h.navier_stokes t ⟨ht.1, ht.2.trans hS.2⟩)

end NavierStokesR3.H3Comparison

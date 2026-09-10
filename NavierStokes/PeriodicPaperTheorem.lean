import NavierStokes.PeriodicPaperSupport
import NavierStokes.PeriodicPaperScalingSupport
import NavierStokes.R3.ParabolicScaling
import NavierStokes.R3.Theorem
import NavierStokes.PeriodizePDE
import NavierStokes.PeriodicViscosity
import NavierStokes.CandidateConsequences

/-!
# The full periodic corollary of the paper

The torus is represented by spatially periodic lifts to R³. The support
clauses intersect topological support with the closed fundamental cube:
they do not assert compact support of a nonzero periodic lift on all of R³.
-/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set
open scoped ContDiff

/-- The same velocity, pressure, and force satisfy every assertion of the
periodic corollary before its singular time, which is exactly one. -/
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiff ℝ ∞ f
  velocity_periodic : UnitSpatialPeriodsOn (Ico 0 1) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
  force_periodic : UnitSpatialPeriodsOn (Ici 0) f
  support_compact : IsCompact K
  support_interior : K ⊆ fundamentalInterior
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ∩ fundamentalCube ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ∩ fundamentalCube ⊆ K
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  force_zero_nonpos : ∀ t ≤ (0 : ℝ), ∀ x : Space, f (t, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

/-- A global smooth periodic competitor for precisely the prescribed force
and zero initial datum. No energy or pressure normalization is required. -/
structure GlobalSmoothSolution (ν : ℝ) (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth : ContDiffOn ℝ ∞ velocity futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ pressure futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) velocity
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) pressure
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  divergence_free : ∀ t ∈ Ici (0 : ℝ), ∀ x : Space,
    spatialDivergence velocity t x = 0
  navier_stokes : ∀ t ∈ Ioi (0 : ℝ), ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)

/-- Every periodic candidate excludes a global smooth periodic competitor. -/
theorem CandidateProperties.no_global_solution {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (hν : 0 < ν) : ¬ Nonempty (GlobalSmoothSolution ν f) := by
  rintro ⟨v⟩
  exact PeriodicViscosity.excludes_global_solution hν
    h.velocity_smooth h.pressure_smooth h.velocity_periodic h.pressure_periodic
    h.zero_initial_velocity h.divergence_free h.navier_stokes h.speed_unbounded
    v.velocity_smooth v.pressure_smooth v.velocity_periodic v.pressure_periodic
    v.zero_initial_velocity v.divergence_free v.navier_stokes

/-- Every order of the ordinary spacetime derivative of the prescribed force
has arbitrary polynomial decay, as asserted in the periodic corollary proof. -/
theorem CandidateProperties.force_derivative_decay {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (m : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-N) := by
  obtain ⟨C, hC, hbound⟩ := CandidateConsequences.futureJet_decay
    h.force_smooth.contDiffOn h.force_periodic h.force_time_support m N hN
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← CandidateConsequences.futureJet_eq_full ht x m h.force_smooth.contDiffAt]
  exact hbound t ht x

/-- Periodize a compact whole-space candidate after its supports have been
compressed into the central quarter cube. The arbitrary post-one extensions
are discarded before forming the lattice sum. -/
theorem of_compact_candidate {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hK : K ⊆ fundamentalInterior)
    (hu : ∀ t < (1 : ℝ), ∀ x : Space, u (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hp : ∀ t < (1 : ℝ), ∀ x : Space, p (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hf : SupportedInCube (1 / 4) f) :
    CandidateProperties ν (periodize (beforeOne u)) (periodize (beforeOne p))
      (periodize f) K := by
  have hsu := beforeOne_supported hu
  have hsp := beforeOne_supported hp
  have hr : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  refine {
    velocity_smooth := contDiffOn_periodize hsu (beforeOne_smooth h.velocity_smooth)
    pressure_smooth := contDiffOn_periodize hsp (beforeOne_smooth h.pressure_smooth)
    force_smooth := contDiff_periodize hf h.force_smooth
    velocity_periodic := unitSpatialPeriodsOn_periodize _ _
    pressure_periodic := unitSpatialPeriodsOn_periodize _ _
    force_periodic := unitSpatialPeriodsOn_periodize _ _
    support_compact := h.support_compact
    support_interior := hK
    velocity_support := ?_
    pressure_support := ?_
    zero_initial_velocity := ?_
    force_time_support := compactFutureTimeSupport_periodize
      (compactFutureTimeSupport_of_hasCompactSupport h.force_support.1)
    force_zero_nonpos := ?_
    divergence_free := ?_
    navier_stokes := ?_
    speed_unbounded := speedUnbounded_periodize hsu hr
      (speedUnbounded_beforeOne h.speed_unbounded)
  }
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsu hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.velocity_support t ht
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsp hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.pressure_support t ht
  · intro x
    apply periodize_eq_zero_of_timeSlice
    intro y
    rw [beforeOne_eq u (by norm_num : (0 : ℝ) < 1)]
    exact h.zero_initial_velocity y
  · intro t ht x
    exact periodize_eq_zero_of_timeSlice (h.force_support.eq_zero_of_nonpos ht) x
  · apply divergence_free_periodize hsu hr
    intro t ht x
    rw [spatialDivergence_congr (beforeOne_eventuallyEq u (z := (t, x)) ht.2)]
    exact h.divergence_free t ht x
  · apply navier_stokes_periodize hsu hsp hf hr
    intro t ht x
    rw [residual_viscosity_congr ν (beforeOne_eventuallyEq u (z := (t, x)) ht.2)
      (beforeOne_eventuallyEq p (z := (t, x)) ht.2)]
    exact h.navier_stokes t ht x

/-- The full quantified periodic corollary, including support in the interior
of the fundamental cube and absence of a global smooth periodic solution. -/
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalSmoothSolution ν f)

/-- The full periodic corollary is unconditional for every positive
viscosity. The affine parabolic clock preserves singular time exactly one. -/
theorem periodic_corollary : breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, _, hrest⟩ :=
    NavierStokesR3.theorem_1_1_with_initial_rest ν hν
  obtain ⟨l, hl, hK, hu, hp, hf⟩ := exists_compression_scale hc
  have hcompressed := NavierStokesR3.ParabolicScaling.compressedCandidate hc hrest hl
  have hperiodic := of_compact_candidate hcompressed hK hu hp hf
  exact ⟨_, _, _, _, hperiodic, hperiodic.no_global_solution hν⟩

end NavierStokes.PeriodicPaper

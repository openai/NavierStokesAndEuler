import NavierStokes.R3.ProblemStatement
import NavierStokes.ComparatorR3Bridge
import NavierStokes.CompactSpatialForceDecay

/-!
# The full whole-space candidate implies the comparator statement

This bridge retains the viscosity and the prescribed force. Compact spacetime
support proves the force's required derivative decay, and a comparator solution
gives exactly a global solution in the whole-space paper statement.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3

open ProblemStatement NavierStokes.ComparatorBridge

theorem forceConditionDecay_of_compact {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    NavierStokes.Comparator.ForceConditionDecay (toComparator f) := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hs.isCompact.image continuous_snd
  have hspace : NavierStokes.CompactSpatialForceDecay.SupportedIn K f := by
    intro t ht x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hx ⟨(t, x), hz, rfl⟩
  obtain ⟨M, hM⟩ := hs.isCompact.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (Prod.fst : SpaceTime → ℝ) (tsupport f))
  have htime : NavierStokes.ProblemStatement.CompactFutureTimeSupport f := by
    refine ⟨max M 0 + 1, by positivity, ?_⟩
    intro t ht x
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    have hb := hM (t, x) hz
    have hmt := le_abs_self t
    have hmax := le_max_left M 0
    simp only [Real.norm_eq_abs] at hb
    linarith
  exact NavierStokes.CompactSpatialForceDecay.forceConditionDecay hK
    hf.contDiffOn hspace htime

/-- Translate a comparator solution without changing viscosity or time. -/
def globalSolutionOfComparator {ν : ℝ} {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν
      (fun _ => 0) (toComparator f) v p) : GlobalFiniteEnergySolution ν f where
  velocity := fromComparator v
  pressure := fromComparator p
  velocity_smooth := fromComparator_smooth h.velocity_smooth
  pressure_smooth := fromComparator_smooth h.pressure_smooth
  zero_initial_velocity := h.initial_condition
  divergence_free := by
    intro t ht x
    rw [divergence_eq]
    exact h.div_free x t ht
  navier_stokes := by
    intro t ht x
    exact comparator_equation_Rn h ht x
  energy_bounded := by
    obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
    intro t ht
    constructor
    · simpa only [SquareIntegrableAtTime, fromComparator, norm_norm] using!
        (memLp_two_iff_integrable_sq_norm (h.integrable t ht).1).mp (h.integrable t ht)
    · change (1 / 2 : ℝ) * (∫ x : Space, ‖v x t‖ ^ 2) ≤ max 0 (E / 2)
      have hb := (hE t ht).le
      have hm := le_max_right 0 (E / 2)
      linarith

/-- The paper's complete conclusion gives option (C) with the same force. -/
theorem comparator_of_breakdown {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K)
    (hglobal : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  refine ⟨fun _ => 0, toComparator f, zero_initial_condition_decay,
    forceConditionDecay_of_compact h.force_smooth h.force_support.1, ?_⟩
  rintro ⟨v, q, hv⟩
  exact hglobal ⟨globalSolutionOfComparator hv⟩

end NavierStokesR3

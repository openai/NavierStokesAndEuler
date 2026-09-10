import NavierStokes.R3FiniteEnergyComparison
import NavierStokes.R3ActualCandidate
import NavierStokes.R3.Theorem
import NavierStokes.R3.ComparatorBridge

/-!
# The full whole-space theorem implies option (C)

The unconditional whole-space theorem constructs one compactly supported flow
with a uniform energy bound up to time one for every positive viscosity. Its
same force and zero initial data satisfy the exact comparator conditions.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff

theorem option_C_of_compact_candidate
    {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : R3CompactCandidate.Properties u p f) (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨K, hK, hs⟩ := h.force_support
  have hFd := CompactSpatialForceDecay.forceConditionDecay hK
    (rescale_smooth h.force_smooth (ν ^ 2) hν.le)
    (CompactSpatialForceDecay.rescale_supported hs (ν ^ 2) hν.le)
    (rescale_support h.force_time_support (ν ^ 2) hν)
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f),
    zero_initial_condition_decay, hFd, ?_⟩
  rintro ⟨v, q, hv⟩
  exact compact_candidate_excludes_global_solution h (normalized_solution_Rn hν hv)

/-- Option (C) with exactly the comparator's quantifiers. -/
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨u, p, f, K, h, hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact NavierStokesR3.comparator_of_breakdown h hglobal

end NavierStokes.ComparatorBridge

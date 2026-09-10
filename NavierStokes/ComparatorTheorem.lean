import NavierStokes.ComparatorBridge
import NavierStokes.ActualCandidateAssembly
import NavierStokes.CandidateConsequences
import NavierStokes.PeriodicPaperComparator

/-!
# The full periodic corollary implies option (D)

For every positive viscosity, the full periodic corollary supplies a solution
that blows up exactly at time one. Its same force and zero datum satisfy every
condition in the comparator, including the force derivative decay bounds.

No result here uses any of the comparator's unproved statements.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff

/-- Any witness of the original candidate statement implies option (D), for
every positive viscosity, with all comparator hypotheses discharged. -/
theorem option_D_of_candidate {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  have hFs : ContDiffOn ℝ ∞ (rescaledForce ν f) futureDomain :=
    rescale_smooth h.force_smooth (ν ^ 2) hν.le
  have hFp : UnitSpatialPeriodsOn (Ici 0) (rescaledForce ν f) :=
    rescale_periodic h.force_periodic (ν ^ 2) hν.le
  have hFt : CompactFutureTimeSupport (rescaledForce ν f) :=
    rescale_support h.force_time_support (ν ^ 2) hν
  have hFd := CandidateConsequences.futureJet_decay hFs hFp hFt
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f), zero_initial_condition,
    forceConditionPeriodic_of_decay hFs hFp hFd, ?_⟩
  rintro ⟨v, q, hv⟩
  have hn := normalized_solution hν hv
  exact MaximalLifespan.candidate_excludes_global_solution h
    hn.velocity_smooth hn.pressure_smooth hn.velocity_periodic hn.pressure_periodic
    hn.initial_velocity hn.divergence_free hn.navier_stokes

/-- Option (D), with exactly the comparator's quantifiers, from the project's
closed candidate construction. -/
theorem navier_stokes_breakdown_periodic (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  obtain ⟨u, p, f, K, h, hglobal⟩ := PeriodicPaper.periodic_corollary ν hν
  exact option_D_of_paper_candidate h hglobal

end NavierStokes.ComparatorBridge

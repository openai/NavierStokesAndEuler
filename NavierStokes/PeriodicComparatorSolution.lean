import NavierStokes.ComparatorBridge
import NavierStokes.PeriodicPaperTheorem

/-!
# The periodic comparator in the paper's coordinates

A smooth comparator solution gives a global smooth periodic solution for the
same viscosity and force. Only the order of the spacetime arguments changes.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open ProblemStatement Set

/-- Change coordinates in a periodic comparator solution without changing its
viscosity, force, time variable, or zero initial datum. Smoothness on the closed
future domain is preserved, including its initial-time boundary. -/
def periodicPaperSolution_of_comparator {ν : ℝ} {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν (fun _ => 0)
      (toComparator f) v p) : PeriodicPaper.GlobalSmoothSolution ν f where
  velocity := fromComparator v
  pressure := fromComparator p
  velocity_smooth := fromComparator_smooth h.velocity_smooth
  pressure_smooth := fromComparator_smooth h.pressure_smooth
  velocity_periodic := by
    intro t ht x i
    exact h.isOnePeriodic_velocity t ht x i
  pressure_periodic := by
    intro t ht x i
    exact h.isOnePeriodic_pressure t ht x i
  zero_initial_velocity := h.initial_condition
  divergence_free := by
    intro t ht x
    rw [divergence_eq]
    exact h.div_free x t ht
  navier_stokes := by
    intro t ht x
    exact comparator_equation h ht x

end NavierStokes.ComparatorBridge

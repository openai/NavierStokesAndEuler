import NavierStokes.PeriodicLocalization
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A nearest integer lattice point

Every spatial point lies in a translate of the closed fundamental cube.
-/

noncomputable section

namespace NavierStokes.PeriodicLocalization

open ProblemStatement

/-- Rounding each coordinate places a point in the closed fundamental cube. -/
theorem exists_lattice_near (x : Space) :
    ∃ n : Lattice, ∀ i : Fin 3, |(x - lattice n) i| ≤ 1 / 2 := by
  refine ⟨fun i => ⌊x i + 1 / 2⌋, ?_⟩
  intro i
  change |x i - (⌊x i + 1 / 2⌋ : ℝ)| ≤ 1 / 2
  have hlo := Int.floor_le (x i + 1 / 2)
  have hhi := Int.lt_floor_add_one (x i + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

end NavierStokes.PeriodicLocalization

import NavierStokes.PeriodicSobolev
import NavierStokes.R3.ProblemStatement

/-! # Derivative H³ norms on Euclidean three-space

All integrals in this file use Lebesgue measure on the whole of `ℝ³`.
The positive multiplicities of the eight mixed derivatives agree with the
existing periodic derivative norm and define an equivalent H³ norm.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

def squareEnergy (f : Space → Space) : ℝ := ∫ x, ‖f x‖ ^ 2

def mixedEnergy (f : Space → Space) : ℝ :=
  squareEnergy f +
  squareEnergy (spatialPartial 0 f) +
  squareEnergy (spatialPartial 1 f) +
  squareEnergy (spatialPartial 2 f) +
  squareEnergy (spatialPartial 1 (spatialPartial 0 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 0 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 1 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 1 (spatialPartial 0 f)))

/-- Every ordered coordinate derivative of order at most three is included. -/
def derivativeH3Energy (f : Space → Space) : ℝ :=
  mixedEnergy f +
    (∑ i : Fin 3, ∑ j : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j f))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j (spatialPartial k f))))

def derivativeH3Norm (f : Space → Space) : ℝ := Real.sqrt (derivativeH3Energy f)

/-- Genuine square integrability, to exclude the totalized-integral convention
for a nonintegrable derivative. -/
def HasFiniteH3 (f : Space → Space) : Prop :=
  Integrable (fun x => ‖f x‖ ^ 2) ∧
    (∀ i, Integrable (fun x => ‖spatialPartial i f x‖ ^ 2)) ∧
    (∀ i j, Integrable (fun x => ‖spatialPartial i (spatialPartial j f) x‖ ^ 2)) ∧
    (∀ i j k, Integrable
      (fun x => ‖spatialPartial i (spatialPartial j (spatialPartial k f)) x‖ ^ 2))

theorem squareEnergy_nonneg (f : Space → Space) : 0 ≤ squareEnergy f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem mixedEnergy_nonneg (f : Space → Space) : 0 ≤ mixedEnergy f := by
  unfold mixedEnergy
  repeat' apply add_nonneg
  all_goals exact squareEnergy_nonneg _

theorem mixedEnergy_le_derivativeH3Energy (f : Space → Space) :
    mixedEnergy f ≤ derivativeH3Energy f := by
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j f)) := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _))
  have h3 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j (spatialPartial k f))) := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _)))
  unfold derivativeH3Energy
  linarith

theorem derivativeH3Energy_nonneg (f : Space → Space) : 0 ≤ derivativeH3Energy f :=
  (mixedEnergy_nonneg f).trans (mixedEnergy_le_derivativeH3Energy f)

theorem derivativeH3Norm_nonneg (f : Space → Space) : 0 ≤ derivativeH3Norm f :=
  Real.sqrt_nonneg _

end NavierStokesR3.H3Embedding

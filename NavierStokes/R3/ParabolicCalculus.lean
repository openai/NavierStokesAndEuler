import NavierStokes.R3.ParabolicDefinitions
import NavierStokes.ResidualRegularity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

theorem pull_temporalDerivative (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, l • x)) (clock l t)) :
    temporalDerivative (pull a l u) t x =
      (a * l ^ 2) • temporalDerivative u (clock l t) (l • x) := by
  have hc : HasDerivAt (clock l) (l ^ 2) t := by
    convert ((((hasDerivAt_id t).sub_const 1).const_mul (l ^ 2)).add_const 1) using 1
    all_goals first | rfl | simp
  have hd := (hu.hasDerivAt.scomp t hc).const_smul a
  change deriv (fun s => a • u (clock l s, l • x)) t =
    (a * l ^ 2) • deriv (fun s => u (s, l • x)) (clock l t)
  simpa only [Function.comp_def, Pi.smul_def, smul_smul] using hd.deriv

theorem pull_spatialDerivative (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDerivative (pull a l u) t x = (a * l) • spatialDerivative u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_spatialDerivative a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_divergence (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (pull a l u) t x = (a * l) * spatialDivergence u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_divergence a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_advection (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    advection (pull a l u) t x = (a ^ 2 * l) • advection u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_advection a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_laplacian (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (pull a l u) t x = (a * l ^ 2) • spatialLaplacian u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_laplacian a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_gradient (a l : ℝ) (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (pull a l p) t x = (a * l) • pressureGradient p (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_gradient a l
    (fun z => p (clock l z.1, z.2)) t x

theorem pull_residual (ν l : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, l • x)) (clock l t)) :
    ProblemStatement.navierStokesResidual ν (pull l l u) (pull (l ^ 2) l p) t x =
      l ^ 3 • ProblemStatement.navierStokesResidual ν u p (clock l t) (l • x) := by
  have h1 : l * l ^ 2 = l ^ 3 := by ring
  have h2 : l ^ 2 * l = l ^ 3 := by ring
  have h3 : ν * l ^ 3 = l ^ 3 * ν := mul_comm _ _
  simp only [ProblemStatement.navierStokesResidual, pull_temporalDerivative _ _ _ _ _ hu,
    pull_advection, pull_laplacian, pull_gradient, smul_add, smul_sub, smul_smul, h1, h2, h3]

theorem residual_congr (ν : ℝ) {u v : VelocityField} {p q : PressureField} {z : SpaceTime}
    (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    ProblemStatement.navierStokesResidual ν u p z.1 z.2 =
      ProblemStatement.navierStokesResidual ν v q z.1 z.2 := by
  unfold ProblemStatement.navierStokesResidual
  rw [NavierStokes.ResidualRegularity.temporalDerivative_congr hu,
    NavierStokes.ResidualRegularity.advection_congr hu,
    NavierStokes.ResidualRegularity.spatialLaplacian_congr hu,
    NavierStokes.ResidualRegularity.pressureGradient_congr hp]

theorem zeroBefore_residual {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {t : ℝ} (ht : t < 1) (x : Space) :
    ProblemStatement.navierStokesResidual ν (zeroBefore u) (zeroBefore p) t x = f (t, x) := by
  by_cases ht0 : 0 < t
  · rw [residual_congr ν (z := (t, x))
      (zeroBefore_eventually_eq u ht0) (zeroBefore_eventually_eq p ht0)]
    exact hc.navier_stokes t ⟨ht0, ht⟩ x
  · rw [residual_congr ν (z := (t, x))
      (zeroBefore_eventually_zero (fun s hs y => (hrest s hs y).1) (le_of_not_gt ht0))
      (zeroBefore_eventually_zero (fun s hs y => (hrest s hs y).2) (le_of_not_gt ht0))]
    rw [hc.force_support.eq_zero_of_nonpos (le_of_not_gt ht0)]
    simp [ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialLaplacian, spatialDerivative, pressureGradient]

end NavierStokesR3.ParabolicScaling

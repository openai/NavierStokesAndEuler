import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3.ViscosityScaling

/-!
# Whole-space comparison at every positive viscosity

Spatial normalization transports both solutions in the comparison theorem.
Time and the closed comparison interval are unchanged.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.WholeSpaceUniqueness

open ProblemStatement ViscosityScaling
open NavierStokes.ProblemStatement (spatialDivergence)

/-- The compact smooth candidate is unique on every shorter closed interval
among smooth solutions with one finite energy bound on that interval. -/
theorem candidate_unique_on_Icc_viscosity {ν : ℝ} (hν : 0 < ν)
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) {T : ℝ} (hT : T < 1)
    {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual ν v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  let a : ℝ := (Real.sqrt ν)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hν)
  have hcoef : a ^ 2 * ν = 1 := by
    dsimp [a]
    have hs : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hν).ne'
    calc
      (Real.sqrt ν)⁻¹ ^ 2 * ν = (Real.sqrt ν)⁻¹ ^ 2 * (Real.sqrt ν) ^ 2 :=
        congrArg ((Real.sqrt ν)⁻¹ ^ 2 * ·) (Real.sq_sqrt hν.le).symm
      _ = 1 := by field_simp
  have hc : CandidateProperties 1 (rescale a a⁻¹ u) (rescale (a ^ 2) a⁻¹ p)
      (rescale a a⁻¹ f) ((fun x : Space => a • x) '' K) := by
    simpa only [hcoef] using rescale_candidate h ha
  have he := candidate_unique_on_Icc hc hT
    (rescale_smooth_on hv a a⁻¹) (rescale_smooth_on hq (a ^ 2) a⁻¹)
    (hev.spatial_smul a a⁻¹ (inv_ne_zero ha.ne'))
    (fun t ht x => by rw [rescale_divergence, hdv t ht, mul_zero])
    (fun t ht x => by
      rw [← hcoef, rescale_residual ν a ha.ne', hNSv t ht]
      rfl)
    (fun x => by simp only [rescale, hvzero, smul_zero])
  intro t ht x
  have hx := he t ht (a • x)
  simpa only [rescale, smul_smul, inv_mul_cancel₀ ha.ne', one_smul,
    smul_right_inj ha.ne'] using hx

end NavierStokesR3.WholeSpaceUniqueness

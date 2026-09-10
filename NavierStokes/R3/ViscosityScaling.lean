import NavierStokes.R3.ProblemStatement
import NavierStokes.R3.SpatialEnergyScaling
import NavierStokes.R3.SpatialSupportScaling
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Spatial changes of viscosity preserving the singular time

Only the spatial coordinate changes.  Consequently the initial time, singular
time, and strict positive-time support of the force are preserved.
-/

noncomputable section

namespace NavierStokesR3.ViscosityScaling

open NavierStokes.ProblemStatement Set
open scoped ContDiff

/-- Spatial coordinate and amplitude change, with time left fixed. -/
def rescale {V : Type*} [SMul ℝ V] (a b : ℝ) (g : SpaceTime → V) : SpaceTime → V :=
  fun z => a • g (z.1, b • z.2)

theorem rescale_smooth_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {times : Set ℝ} {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g (times ×ˢ univ))
    (a b : ℝ) : ContDiffOn ℝ ∞ (rescale a b g) (times ×ˢ univ) := by
  exact (hg.comp (contDiff_fst.prodMk (contDiff_snd.const_smul b)).contDiffOn
    (fun z hz => ⟨hz.1, mem_univ _⟩)).const_smul a

theorem rescale_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    ContDiff ℝ ∞ (rescale a b g) := by
  exact (hg.comp (contDiff_fst.prodMk (contDiff_snd.const_smul b))).const_smul a

theorem rescale_temporalDerivative (a b : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    temporalDerivative (rescale a b u) t x = a • temporalDerivative u t (b • x) := by
  unfold temporalDerivative rescale
  simp only [← Pi.smul_def, fderiv_const_smul_field]
  rfl

theorem rescale_spatialDerivative (a b : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDerivative (rescale a b u) t x = (a * b) • spatialDerivative u t (b • x) := by
  unfold spatialDerivative rescale
  simp only [← Pi.smul_def, fderiv_const_smul_field, Pi.smul_apply]
  rw [fderiv_comp_smul b (f := fun y : Space => u (t, y))]
  simp only [smul_smul]

theorem rescale_divergence (a b : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (rescale a b u) t x = (a * b) * spatialDivergence u t (b • x) := by
  simp [spatialDivergence, rescale_spatialDerivative, Finset.mul_sum]

theorem rescale_advection (a b : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    advection (rescale a b u) t x = (a ^ 2 * b) • advection u t (b • x) := by
  simp only [advection, rescale_spatialDerivative, rescale, smul_apply, map_smul,
    smul_smul]
  congr 1
  ring

theorem rescale_gradient (a b : ℝ) (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (rescale a b p) t x = (a * b) • pressureGradient p t (b • x) := by
  unfold pressureGradient rescale
  simp only [← Pi.smul_def, fderiv_const_smul_field, Pi.smul_apply]
  rw [fderiv_comp_smul b (f := fun y : Space => p (t, y))]
  simp [smul_smul, Finset.smul_sum]

theorem rescale_laplacian (a b : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (rescale a b u) t x = (a * b ^ 2) • spatialLaplacian u t (b • x) := by
  simp only [spatialLaplacian, rescale_spatialDerivative, smul_apply]
  simp only [← Pi.smul_def, fderiv_const_smul_field, Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_comp_smul b (f := fun y : Space => spatialDerivative u t y (coordinateVector i))]
  simp only [smul_apply, smul_smul]
  congr 1
  ring

/-- Multiplying lengths and velocities by `a` multiplies viscosity by `a²`. -/
theorem rescale_residual (μ a : ℝ) (ha : a ≠ 0) (u : VelocityField)
    (p : PressureField) (t : ℝ) (x : Space) :
    ProblemStatement.navierStokesResidual (a ^ 2 * μ)
      (rescale a a⁻¹ u) (rescale (a ^ 2) a⁻¹ p) t x =
      a • ProblemStatement.navierStokesResidual μ u p t (a⁻¹ • x) := by
  have h1 : a ^ 2 * a⁻¹ = a := by field_simp
  have h2 : (a ^ 2 * μ) * (a * a⁻¹ ^ 2) = a * μ := by field_simp
  simp only [ProblemStatement.navierStokesResidual, rescale_temporalDerivative,
    rescale_advection, rescale_laplacian, rescale_gradient, smul_add, smul_sub,
    smul_smul, h1, h2]

theorem rescale_speed_unbounded {u : VelocityField} (hu : SpeedUnboundedAtOne u)
    {a : ℝ} (ha : 0 < a) : SpeedUnboundedAtOne (rescale a a⁻¹ u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hu (M / a) (div_pos hM ha) δ hδ
  refine ⟨t, a • x, ht, hnear, ?_⟩
  simpa [rescale, ha.ne', norm_smul, Real.norm_of_nonneg ha.le, mul_comm] using
    (div_lt_iff₀ ha).mp hlarge

/-- Every property of the candidate is preserved, including one energy bound
for the entire unchanged time interval and a single shared spatial support. -/
theorem rescale_candidate {μ : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : ProblemStatement.CandidateProperties μ u p f K)
    {a : ℝ} (ha : 0 < a) :
    ProblemStatement.CandidateProperties (a ^ 2 * μ)
      (rescale a a⁻¹ u) (rescale (a ^ 2) a⁻¹ p) (rescale a a⁻¹ f)
      ((fun x : Space => a • x) '' K) := by
  refine {
    velocity_smooth := rescale_smooth_on h.velocity_smooth _ _
    pressure_smooth := rescale_smooth_on h.pressure_smooth _ _
    support_compact := h.support_compact.image (continuous_id.const_smul a)
    velocity_support := ?_
    pressure_support := ?_
    force_smooth := rescale_smooth h.force_smooth _ _
    force_support := h.force_support.spatialScale a a⁻¹ (inv_ne_zero ha.ne')
    zero_initial_velocity := ?_
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := h.energy_bounded.spatial_smul a a⁻¹ (inv_ne_zero ha.ne')
    speed_unbounded := rescale_speed_unbounded h.speed_unbounded ha
  }
  · intro t ht
    simpa only [rescale, inv_inv] using
      ProblemStatement.tsupport_spatialScale_subset (h.velocity_support t ht)
        a a⁻¹ (inv_ne_zero ha.ne')
  · intro t ht
    simpa only [rescale, inv_inv] using
      ProblemStatement.tsupport_spatialScale_subset (h.pressure_support t ht)
        (a ^ 2) a⁻¹ (inv_ne_zero ha.ne')
  · intro x
    simp only [rescale, h.zero_initial_velocity, smul_zero]
  · intro t ht x
    rw [rescale_divergence, h.divergence_free t ht, mul_zero]
  · intro t ht x
    rw [rescale_residual μ a ha.ne', h.navier_stokes t ht]
    rfl

/-- A global competitor also transports under the same spatial dilation;
no spatial-support condition is imposed on the competitor. -/
def rescale_global_solution {μ : ℝ} {f : VelocityField}
    (h : ProblemStatement.GlobalFiniteEnergySolution μ f) (a : ℝ) (ha : a ≠ 0) :
    ProblemStatement.GlobalFiniteEnergySolution (a ^ 2 * μ) (rescale a a⁻¹ f) := by
  refine {
    velocity := rescale a a⁻¹ h.velocity
    pressure := rescale (a ^ 2) a⁻¹ h.pressure
    velocity_smooth := rescale_smooth_on h.velocity_smooth _ _
    pressure_smooth := rescale_smooth_on h.pressure_smooth _ _
    zero_initial_velocity := ?_
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := h.energy_bounded.spatial_smul a a⁻¹ (inv_ne_zero ha)
  }
  · intro x
    simp only [rescale, h.zero_initial_velocity, smul_zero]
  · intro t ht x
    rw [rescale_divergence, h.divergence_free t ht, mul_zero]
  · intro t ht x
    rw [rescale_residual μ a ha, h.navier_stokes t ht]
    rfl

/-- The velocity/force dilation appropriate for a positive target viscosity. -/
def scaledVelocity (ν : ℝ) (u : VelocityField) : VelocityField :=
  rescale (Real.sqrt ν) (Real.sqrt ν)⁻¹ u

/-- Pressure amplitude is the target viscosity. -/
def scaledPressure (ν : ℝ) (p : PressureField) : PressureField :=
  rescale ν (Real.sqrt ν)⁻¹ p

/-- The transformed candidate has singular time exactly one at every positive
viscosity, and its force remains compactly supported in strictly positive time. -/
theorem candidate_at_viscosity {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : ProblemStatement.CandidateProperties 1 u p f K)
    {ν : ℝ} (hν : 0 < ν) :
    ProblemStatement.CandidateProperties ν (scaledVelocity ν u) (scaledPressure ν p)
      (scaledVelocity ν f) ((fun x : Space => Real.sqrt ν • x) '' K) := by
  simpa only [scaledVelocity, scaledPressure, Real.sq_sqrt hν.le, mul_one] using
    rescale_candidate h (Real.sqrt_pos.mpr hν)

/-- A hypothetical global solution at viscosity `ν` for the transformed force
would give a global viscosity-one solution for the original force. -/
def normalized_global_solution {ν : ℝ} (hν : 0 < ν) {f : VelocityField}
    (h : ProblemStatement.GlobalFiniteEnergySolution ν (scaledVelocity ν f)) :
    ProblemStatement.GlobalFiniteEnergySolution 1 f := by
  have hs : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hν).ne'
  have hcoef : (Real.sqrt ν)⁻¹ ^ 2 * ν = 1 := by
    calc
      (Real.sqrt ν)⁻¹ ^ 2 * ν = (Real.sqrt ν)⁻¹ ^ 2 * (Real.sqrt ν) ^ 2 :=
        congrArg ((Real.sqrt ν)⁻¹ ^ 2 * ·) (Real.sq_sqrt hν.le).symm
      _ = 1 := by field_simp
  have hforce : rescale (Real.sqrt ν)⁻¹ ((Real.sqrt ν)⁻¹)⁻¹ (scaledVelocity ν f) = f := by
    funext z
    simp [scaledVelocity, rescale, smul_smul, hs]
  simpa only [hcoef, hforce] using
    rescale_global_solution h (Real.sqrt ν)⁻¹ (inv_ne_zero hs)

end NavierStokesR3.ViscosityScaling

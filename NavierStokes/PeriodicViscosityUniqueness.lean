import NavierStokes.PeriodicUniqueness
import NavierStokes.ComparatorBridge
import NavierStokes.R3.ProblemStatement

/-!
# Periodic classical uniqueness for every positive viscosity

An inverse change of time and amplitude reduces the two solutions to the
already proved viscosity-one uniqueness theorem. Their spatial periods and
initial time agree throughout the reduction.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.PeriodicViscosityUniqueness

open ProblemStatement PeriodicUniqueness ComparatorBridge

theorem normalized_time_mem_Icc {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Icc (ν * a) (ν * b)) : ν⁻¹ * t ∈ Icc a b := by
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_le_mul_of_nonneg_left ht.1 (inv_pos.mpr hν).le
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_le_mul_of_nonneg_left ht.2 (inv_pos.mpr hν).le

theorem normalized_time_mem_Ioo {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Ioo (ν * a) (ν * b)) : ν⁻¹ * t ∈ Ioo a b := by
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_lt_mul_of_pos_left ht.1 (inv_pos.mpr hν)
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hν)

theorem normalize_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ν a b : ℝ} (hν : 0 < ν) {g : SpaceTime → V}
    (hg : ContDiffOn ℝ ∞ g (slab a b)) (amplitude : ℝ) :
    ContDiffOn ℝ ∞ (rescale amplitude ν⁻¹ g) (slab (ν * a) (ν * b)) := by
  apply (hg.comp ((contDiff_fst.const_smul ν⁻¹).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨normalized_time_mem_Icc hν hz.1, mem_univ _⟩)).const_smul amplitude

theorem normalize_periodic {V : Type*} [SMul ℝ V] {ν a b : ℝ}
    (hν : 0 < ν) {g : SpaceTime → V} (hg : UnitSpatialPeriodsOn (Icc a b) g)
    (amplitude : ℝ) :
    UnitSpatialPeriodsOn (Icc (ν * a) (ν * b)) (rescale amplitude ν⁻¹ g) := by
  intro t ht x i
  exact congrArg (fun y => amplitude • y) (hg _ (normalized_time_mem_Icc hν ht) x i)

theorem normalize_residual {ν : ℝ} (hν : 0 < ν)
    (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, x)) (ν⁻¹ * t)) :
    navierStokesResidual (rescale ν⁻¹ ν⁻¹ u) (rescale (ν⁻¹ ^ 2) ν⁻¹ p) t x =
      ν⁻¹ ^ 2 • NavierStokesR3.ProblemStatement.navierStokesResidual ν u p (ν⁻¹ * t) x := by
  have hcoef : ν⁻¹ * ν⁻¹ * ν = ν⁻¹ := by field_simp
  rw [navierStokesResidual, rescale_temporalDerivative _ _ _ _ _ hu,
    rescale_advection, rescale_laplacian, rescale_gradient]
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    smul_add, smul_sub, smul_smul, hcoef, pow_two]

/-- Two smooth periodic solutions with the same force and initial datum agree
on a closed time interval, at every positive viscosity. -/
theorem classical_uniqueness_on_Icc {ν a b : ℝ} (hν : 0 < ν)
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hv : ContDiffOn ℝ ∞ v (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hq : ContDiffOn ℝ ∞ q (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u)
    (hpv : UnitSpatialPeriodsOn (Icc a b) v)
    (hpp : UnitSpatialPeriodsOn (Icc a b) p)
    (hpq : UnitSpatialPeriodsOn (Icc a b) q)
    (hdu : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSu : ∀ t ∈ Ioo a b, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hNSv : ∀ t ∈ Ioo a b, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x = f (t, x))
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) :
    ∀ t ∈ Icc a b, ∀ x : Space, u (t, x) = v (t, x) := by
  have heq := PeriodicUniqueness.classical_uniqueness_on_Icc
    (u := rescale ν⁻¹ ν⁻¹ u) (v := rescale ν⁻¹ ν⁻¹ v)
    (p := rescale (ν⁻¹ ^ 2) ν⁻¹ p) (q := rescale (ν⁻¹ ^ 2) ν⁻¹ q)
    (f := rescale (ν⁻¹ ^ 2) ν⁻¹ f)
    (normalize_smooth hν hu _) (normalize_smooth hν hv _)
    (normalize_smooth hν hp _) (normalize_smooth hν hq _)
    (normalize_periodic hν hpu _) (normalize_periodic hν hpv _)
    (normalize_periodic hν hpp _) (normalize_periodic hν hpq _) ?_ ?_ ?_ ?_ ?_
  · intro t ht x
    have hscaled := heq (ν * t)
      ⟨mul_le_mul_of_nonneg_left ht.1 hν.le, mul_le_mul_of_nonneg_left ht.2 hν.le⟩ x
    have h := congrArg (fun z : Space => ν • z) hscaled
    simpa [rescale, smul_smul, ← mul_assoc, hν.ne'] using h
  · intro t ht x
    rw [rescale_divergence, hdu _ (normalized_time_mem_Ioo hν ht), mul_zero]
  · intro t ht x
    rw [rescale_divergence, hdv _ (normalized_time_mem_Ioo hν ht), mul_zero]
  · intro t ht x
    rw [normalize_residual hν u p t x
      (time_differentiable_at_interior hu (normalized_time_mem_Ioo hν ht) x),
      hNSu _ (normalized_time_mem_Ioo hν ht)]
    rfl
  · intro t ht x
    rw [normalize_residual hν v q t x
      (time_differentiable_at_interior hv (normalized_time_mem_Ioo hν ht) x),
      hNSv _ (normalized_time_mem_Ioo hν ht)]
    rfl
  · intro x
    simp only [rescale, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul, hinitial]

end NavierStokes.PeriodicViscosityUniqueness

import NavierStokes.R3.ViscousEnergyBalance
import NavierStokes.R3.SpatialCauchySchwarz
import NavierStokes.R3.SharpEnergyBound
import NavierStokes.R3.ForceL2Norm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite integrated dissipation up to the singular time

The time integrability statement is explicit: a totalized real integral is not
used as a substitute for finiteness of the dissipation. The energy balance is
first integrated on shorter closed time intervals, then an exhaustion proves
integrability on the entire half-open interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness

/-- The exact energy identity integrated over any shorter time interval. -/
theorem integrated_energy_balance {ν T : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (hT : 0 < T)
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T)) (hf : Continuous f)
    (hsupp : ∀ r ∈ Icc (0 : ℝ) T, tsupport (fun x => u (r, x)) ⊆ K)
    (hinitial : ∀ x : Space, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) =
      2 * ∫ t in (0 : ℝ)..T, ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ := by
  have hd : IntervalIntegrable (dissipation u) volume 0 T := (dissipation_continuousOn hT hK hu hsupp).intervalIntegrable_of_Icc hT.le
  have hw : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T := (forceWork_continuousOn hK hu.continuousOn hf.continuousOn hsupp).intervalIntegrable_of_Icc hT.le
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (l2Sq_continuousOn hK hu hsupp)
    (fun t ht => hasDerivAt_energy_balance_viscosity hK hu hp
      (hf.comp (continuous_const.prodMk continuous_id)) hsupp ht (hdiv t ht) (hNS t ht))
    ((hd.const_mul (-2 * ν)).add (hw.const_mul 2))
  rw [intervalIntegral.integral_add (hd.const_mul (-2 * ν)) (hw.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb
  have hzero : l2Sq u 0 = 0 := by simp [l2Sq, hinitial]
  rw [hzero] at hb
  linarith

/-- Young's inequality, before discarding the viscous dissipation. -/
theorem force_work_le {u f : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hfi : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2)) :
    2 * (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤ l2Sq u t + l2Sq f t := by
  have hui := integrable_norm_sq hu hcu
  have hip := integrable_inner_left hu hf hcu
  rw [← integral_const_mul]
  unfold l2Sq
  rw [← integral_add hui hfi]
  apply integral_mono (hip.const_mul 2) (hui.add hfi)
  intro x
  have hi := (le_abs_self ⟪u (t, x), f (t, x)⟫_ℝ).trans
    (abs_real_inner_le_norm (u (t, x)) (f (t, x)))
  dsimp only [Pi.add_apply] at *
  nlinarith [sq_nonneg (‖u (t, x)‖ - ‖f (t, x)‖)]

/-- The dissipation of a paper candidate is integrable in time on the whole
interval before blowup. This is the finite total dissipation conclusion of
Lemma 10.4, in addition to the uniform kinetic-energy bound. -/
theorem candidate_integrable_dissipation {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    IntegrableOn (dissipation u) (Ico (0 : ℝ) 1) := by
  obtain ⟨E, hE, henergy⟩ := hc.energy_bounded
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  have hlocal (T : ℝ) (hT : T ∈ Ioo (0 : ℝ) 1) :
      IntegrableOn (dissipation u) (Ioc (0 : ℝ) T) ∧
      (∫ t in Ioc (0 : ℝ) T, ‖dissipation u t‖) ≤ (2 * E + C) / (2 * ν) := by
    have hsub : slab 0 T ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
    have hu := hc.velocity_smooth.mono hsub
    have hp := hc.pressure_smooth.mono hsub
    have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
      intro t ht
      exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
    have hdcont := dissipation_continuousOn hT.1 hc.support_compact hu hsupp
    have hd : IntervalIntegrable (dissipation u) volume 0 T := hdcont.intervalIntegrable_of_Icc hT.1.le
    refine ⟨hd.1, ?_⟩
    have hwork : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T := (forceWork_continuousOn hc.support_compact hu.continuousOn
      hc.force_smooth.continuous.continuousOn hsupp).intervalIntegrable_of_Icc hT.1.le
    have hbal := integrated_energy_balance hT.1 hc.support_compact hu hp
      hc.force_smooth.continuous hsupp hc.zero_initial_velocity
      (fun t ht => hc.divergence_free t ⟨ht.1.le, ht.2.trans hT.2⟩)
      (fun t ht => hc.navier_stokes t ⟨ht.1, ht.2.trans hT.2⟩)
    have hworkbound : 2 * (∫ t in (0 : ℝ)..T, ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
        (2 * E + C) * T := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in (0 : ℝ)..T, 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
            ∫ t in (0 : ℝ)..T, (2 * E + C) := by
          apply intervalIntegral.integral_mono_on hT.1.le (hwork.const_mul 2)
            intervalIntegrable_const
          intro t ht
          have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT.2⟩
          have hfT := hforce t ⟨ht.1, ht1.2.le⟩
          have huT := henergy t ht1
          have hyoung := force_work_le (spatial_smooth hu ht).continuous
            (hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id))
            (slice_compact hc.support_compact (hsupp t ht)) hfT.1
          change ProblemStatement.SquareIntegrableAtTime u t ∧ (1 / 2 : ℝ) * l2Sq u t ≤ E at huT
          change Integrable (fun x => ‖f (t, x)‖ ^ 2) ∧ l2Sq f t ≤ C at hfT
          linarith [huT.2, hfT.2]
        _ = (2 * E + C) * T := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
    have hnonneg : 0 ≤ l2Sq u T := integral_nonneg (fun _ => sq_nonneg _)
    have hd_bound : (∫ t in (0 : ℝ)..T, dissipation u t) ≤ (2 * E + C) / (2 * ν) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).2
      have hsize : (2 * E + C) * T ≤ 2 * E + C := by
        exact mul_le_of_le_one_right (by positivity) hT.2.le
      nlinarith
    simpa only [Real.norm_of_nonneg (dissipation_nonneg u _),
      intervalIntegral.integral_of_le hT.1.le] using hd_bound
  let b : Ioo (0 : ℝ) 1 → ℝ := fun t => t.1
  have hb : Tendsto b (comap b (𝓝[<] (1 : ℝ))) (𝓝 1) := by
    exact tendsto_comap.trans nhdsWithin_le_nhds
  have : NeBot (comap b (𝓝[<] (1 : ℝ))) := by
    apply (inferInstance : NeBot (𝓝[<] (1 : ℝ))).comap_of_range_mem
    rw [show Set.range b = Ioo (0 : ℝ) 1 from Subtype.range_coe_subtype]
    exact Ioo_mem_nhdsLT zero_lt_one
  have hwhole : IntegrableOn (dissipation u) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
      (l := comap b (𝓝[<] (1 : ℝ))) (b := b)
      (fun t => (hlocal t.1 t.2).1) hb
      (Filter.Eventually.of_forall (fun t => (hlocal t.1 t.2).2))
  exact (integrableOn_Ico_iff_integrableOn_Ioo).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo).mp hwhole)

/-- The velocity's L² norm is at most the accumulated L² norm of its force. -/
theorem candidate_l2Norm_le_cumulativeForceNorm {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) :
    l2Norm u T ≤ cumulativeForceNorm f T := by
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
  have hu := hc.velocity_smooth.mono hsub
  have hp := hc.pressure_smooth.mono hsub
  have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
    intro t ht
    exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  apply SharpEnergyBound.sqrt_energy_le_integral hT.1
    (l2Sq_continuousOn hc.support_compact hu hsupp)
    (fun t _ => integral_nonneg (fun _ => sq_nonneg _))
    (by simp [l2Sq, hc.zero_initial_velocity])
    (l2Norm_continuous hc.force_smooth.continuous hc.force_support.1).continuousOn
    (fun t _ => l2Norm_nonneg f t)
    (fun t ht => energy_hasDerivAt hc.support_compact hu hsupp ht)
  intro t ht
  have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT.2⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have huT := spatial_smooth hu htT
  have hpT := spatial_smooth hp htT
  have hcompact := slice_compact hc.support_compact (hsupp t htT)
  have hfT : Continuous (fun x : Space => f (t, x)) := hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hwork := work_le_sqrt_l2Sq huT.continuous hfT hcompact
    (hforce t ⟨ht1.1.le, ht1.2.le⟩).1
  rw [energy_balance_viscosity huT hpT hfT hcompact
    (hc.divergence_free t ⟨ht1.1.le, ht1.2⟩) (hc.navier_stokes t ht1)]
  dsimp only [l2Norm]
  have hd := dissipation_nonneg u t
  have hνd : 0 ≤ ν * dissipation u t := mul_nonneg hν.le hd
  nlinarith

/-- A single explicit kinetic-energy bound for the entire half-open interval.
Square integrability is included, and the right-hand side is independent of `T`. -/
theorem candidate_uniform_kineticEnergy_le {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    ∀ T ∈ Ico (0 : ℝ) 1,
      ProblemStatement.SquareIntegrableAtTime u T ∧
      ProblemStatement.kineticEnergy u T ≤ (1 / 2 : ℝ) * (cumulativeForceNorm f 1) ^ 2 := by
  intro T hT
  obtain ⟨E, hE, hb⟩ := hc.energy_bounded
  refine ⟨(hb T hT).1, ?_⟩
  have hnorm := (candidate_l2Norm_le_cumulativeForceNorm hν hc hT).trans
    (cumulativeForceNorm_monotone hc.force_smooth.continuous hc.force_support.1 hT.2.le)
  have hsq := (sq_le_sq₀ (l2Norm_nonneg u T)
    (cumulativeForceNorm_nonneg f zero_le_one)).2 hnorm
  have hnonneg : 0 ≤ l2Sq u T := integral_nonneg (fun _ => sq_nonneg _)
  rw [l2Norm, Real.sq_sqrt hnonneg] at hsq
  change (1 / 2 : ℝ) * l2Sq u T ≤ (1 / 2 : ℝ) * (cumulativeForceNorm f 1) ^ 2
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- The sharp energy and accumulated dissipation inequality from Lemma 10.4,
with the viscosity restored. Both norms use ordinary spatial volume. -/
theorem candidate_energy_dissipation_le {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) :
    l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤
      (cumulativeForceNorm f T) ^ 2 := by
  rcases hT.1.eq_or_lt with hzero | hpos
  · subst T
    simp [l2Sq, hc.zero_initial_velocity]
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
  have hu := hc.velocity_smooth.mono hsub
  have hp := hc.pressure_smooth.mono hsub
  have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
    intro t ht
    exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
  have hbal := integrated_energy_balance hpos hc.support_compact hu hp
    hc.force_smooth.continuous hsupp hc.zero_initial_velocity
    (fun t ht => hc.divergence_free t ⟨ht.1.le, ht.2.trans hT.2⟩)
    (fun t ht => hc.navier_stokes t ⟨ht.1, ht.2.trans hT.2⟩)
  rw [hbal, ← integral_l2Norm_cumulative_eq_sq hc.force_smooth.continuous hc.force_support.1,
    ← intervalIntegral.integral_const_mul]
  have hwork : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T :=
    (forceWork_continuousOn hc.support_compact hu.continuousOn
      hc.force_smooth.continuous.continuousOn hsupp).intervalIntegrable_of_Icc hT.1
  have hq := l2Norm_continuous hc.force_smooth.continuous hc.force_support.1
  have hF := cumulativeForceNorm_continuous hc.force_smooth.continuous hc.force_support.1
  apply intervalIntegral.integral_mono_on hT.1 (hwork.const_mul 2)
    (((continuous_const.mul hq).mul hF).intervalIntegrable 0 T)
  intro t ht
  have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT.2⟩
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  have hcs := work_le_sqrt_l2Sq (spatial_smooth hu ht).continuous
    (hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id))
    (slice_compact hc.support_compact (hsupp t ht)) (hforce t ⟨ht.1, ht1.2.le⟩).1
  have hb := mul_le_mul_of_nonneg_right
    (candidate_l2Norm_le_cumulativeForceNorm hν hc ht1) (l2Norm_nonneg f t)
  change (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤ l2Norm u t * l2Norm f t at hcs
  dsimp only [Pi.mul_apply]
  nlinarith

/-- Passing to the singular endpoint retains the sharp bound on the total
viscous dissipation. Integrability has already been proved independently. -/
theorem candidate_total_dissipation_le {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    2 * ν * (∫ t in Ico (0 : ℝ) 1, dissipation u t) ≤
      (cumulativeForceNorm f 1) ^ 2 := by
  have hint := candidate_integrable_dissipation hν hc
  have hicc : IntegrableOn (dissipation u) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ico).mpr hint
  have hcont : ContinuousOn
      (fun T => 2 * ν * ∫ t in (0 : ℝ)..T, dissipation u t) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      (intervalIntegral.continuousOn_primitive_interval hicc).const_mul (2 * ν)
  have hF := (cumulativeForceNorm_continuous hc.force_smooth.continuous hc.force_support.1).pow 2
  have hbound (T : ℝ) (hT : T ∈ Ico (0 : ℝ) 1) :
      2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤ (cumulativeForceNorm f T) ^ 2 := by
    have h := candidate_energy_dissipation_le hν hc hT
    have hE : 0 ≤ l2Sq u T := integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have hlimit := le_on_closure hbound
    (by simpa only [closure_Ico (zero_ne_one : (0 : ℝ) ≠ 1)] using hcont)
    hF.continuousOn
    (show (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) by
      rw [closure_Ico zero_ne_one]
      exact ⟨zero_le_one, le_rfl⟩)
  simpa only [integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one] using hlimit

/-- The complete energy conclusions of Lemma 10.4 for one paper candidate:
finite accumulated force norm, genuine total dissipation integrability, the
sharp inequality on every shorter interval, and its total-dissipation bound. -/
theorem candidate_energy_estimates {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    IntervalIntegrable (l2Norm f) volume 0 1 ∧
    IntegrableOn (dissipation u) (Ico (0 : ℝ) 1) ∧
    (∀ T ∈ Ico (0 : ℝ) 1,
      l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤
        (cumulativeForceNorm f T) ^ 2) ∧
    2 * ν * (∫ t in Ico (0 : ℝ) 1, dissipation u t) ≤
      (cumulativeForceNorm f 1) ^ 2 :=
  ⟨l2Norm_intervalIntegrable hc.force_smooth.continuous hc.force_support.1 0 1,
    candidate_integrable_dissipation hν hc,
    fun _ hT => candidate_energy_dissipation_le hν hc hT,
    candidate_total_dissipation_le hν hc⟩

end NavierStokesR3.CompactEnergy

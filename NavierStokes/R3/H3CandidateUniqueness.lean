import NavierStokes.R3.H3WeakStrong
import NavierStokes.R3.H3CandidateStrong
import NavierStokes.R3.H3PressureOrthogonality
import NavierStokes.R3.CompactComparisonBounds

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- The arbitrary pressure potential itself needs no integrability or
normalization: the equation supplies the square-integrable gradient. -/
theorem integral_inner_pressureGradient_zero {w : Space → Space}
    {dw : Fin 3 → Space → Space} (hw : H1Approximation w dw)
    (hdiv : ∀ᵐ x ∂volume, ∑ i : Fin 3, dw i x i = 0)
    {p : PressureField} {t : ℝ} (hp : ContDiff ℝ 1 (fun x => p (t, x)))
    (hg : MemLp (fun x => pressureGradient p t x) 2 volume) :
    (∫ x, ⟪w x, pressureGradient p t x⟫_ℝ) = 0 := by
  have hcomponent (i : Fin 3) (x : Space) :
      pressureGradient p t x i = spatialPartial i (fun y => p (t, y)) x := by
    change (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
      (∑ j : Fin 3, spatialPartial j (fun y => p (t, y)) x • coordinateVector j) = _
    simp [map_sum, coordinateVector]
  have hgp (i : Fin 3) : MemLp (spatialPartial i (fun y => p (t, y))) 2 volume := by
    have hh := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' hg
    change MemLp (fun x => pressureGradient p t x i) 2 volume at hh
    simpa only [hcomponent] using hh
  have hh := H3PressureOrthogonality.pressure_pairing_zero hw hdiv hp hgp
  convert hh using 1
  apply integral_congr_ae
  filter_upwards with x
  simp [pressureGradient, spatialPartial, coordinateVector, inner_sum, inner_smul_right,
    EuclideanSpace.inner_single_right, mul_comm]

/-- Weak–strong uniqueness with arbitrary classical pressure potentials.
The pressure cancellation and all energy terms are derived from the stated
H³ solution class and the actual equation. -/
theorem strong_unique {ν T : ℝ} (hν : 0 ≤ ν)
    {f u v : VelocityField} {p q : PressureField}
    (hu : StrongSolutionOnIcc ν f 0 T u p) (hv : StrongSolutionOnIcc ν f 0 T v q)
    (hf : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (fun x => f (t, x)) 2 volume)
    (A : ℝ → Space → Space →L[ℝ] Space) {G : ℝ} (hG : 0 ≤ G)
    (hAm : ∀ t ∈ Ioo (0 : ℝ) T, AEStronglyMeasurable (A t) volume)
    (hAb : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, ‖A t x‖ ≤ G)
    (hAe : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᵐ x ∂volume, ∀ z : Space,
      A t x z = ∑ i : Fin 3, z i • hu.curve.first i (t, x))
    (hinitial : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  have hpu t ht := hu.pressureGradient_memLp ht (hf t ht)
  have hpv t ht := hv.pressureGradient_memLp ht (hf t ht)
  apply strong_unique_of_pressure_pairing hν hu hv A hG hAm hAb hAe
    (fun t ht => (hpu t ht).sub (hpv t ht)) _ hinitial
  intro t ht
  let hw := (hu.curve.approximation t (Ioo_subset_Icc_self ht)).sub
    (hv.curve.approximation t (Ioo_subset_Icc_self ht))
  have hd : ∀ᵐ x ∂volume,
      ∑ i : Fin 3, (hu.curve.first i (t, x) - hv.curve.first i (t, x)) i = 0 := by
    filter_upwards [hu.divergence_free t ht, hv.divergence_free t ht] with x hux hvx
    simp only [weakDivergence] at hux hvx
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib, hux, hvx, sub_self]
  have hup := integral_inner_pressureGradient_zero hw.toH1Approximation hd
    (hu.pressure_C1 t ht) (hpu t ht)
  have hvp := integral_inner_pressureGradient_zero hw.toH1Approximation hd
    (hv.pressure_C1 t ht) (hpv t ht)
  have hi := integral_sub (integrable_inner_of_memLp hw.memLp (hpu t ht))
    (integrable_inner_of_memLp hw.memLp (hpv t ht))
  simp only [Pi.sub_apply] at hi hup hvp
  simp_rw [inner_sub_right]
  rw [hi, hup, hvp, sub_self]

theorem candidate_force_memLp {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K) (t : ℝ) :
    MemLp (fun x => f (t, x)) 2 volume := by
  have hc : HasCompactSupport (fun x => f (t, x)) := by
    apply HasCompactSupport.intro (h.force_support.1.isCompact.image continuous_snd)
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hz => hx ⟨(t, x), hz, rfl⟩
  exact (h.force_smooth.continuous.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport hc

/-- Every ordinary H³ strong solution with the paper's forcing and zero
initial velocity agrees with the constructed candidate on a shorter slab. -/
theorem candidate_unique_on_Icc_h3 {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (hν : 0 < ν)
    (h : CandidateProperties ν u p f K) {T : ℝ} (hT : T < 1)
    {v : VelocityField} {q : PressureField} (hv : StrongSolutionOnIcc ν f 0 T v q)
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  let hu := (candidate_classicalH3Solution h).on_shorter_interval T ⟨hv.time_lt, hT⟩
  have hus : ContDiffOn ℝ ∞ u (slab 0 T) :=
    h.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩)
  obtain ⟨G, hG, hGb⟩ := CompactComparisonBounds.exists_gradient_bound hv.time_lt hus
    h.support_compact (fun t ht => h.velocity_support t ⟨ht.1, ht.2.trans_lt hT⟩)
  apply strong_unique hν.le hu hv (fun t _ => candidate_force_memLp h t) (spatialDerivative u) hG
  · intro t ht
    exact ((spatial_smooth hus (Ioo_subset_Icc_self ht)).continuous_fderiv (by simp)).aestronglyMeasurable
  · exact fun t ht => hGb t (Ioo_subset_Icc_self ht)
  · intro t _
    filter_upwards with x z
    change spatialDerivative u t x z =
      ∑ i : Fin 3, z i • H3Compact.partialField i u (t, x)
    unfold spatialDerivative
    conv_lhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates z]
    simp only [map_sum, map_smul]
    rfl
  · intro x
    rw [h.zero_initial_velocity, hvzero]

end NavierStokesR3.H3Comparison

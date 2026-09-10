import NavierStokes.WholeDomainPhysicalCompact
import NavierStokes.SlowBaseEndpoint

/-! # Parabolic normalization of the entire exterior heat region -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum

def parabolicLinear (a : ℝ) (ha : 0 < a) : SpaceTime ≃L[ℝ] SpaceTime where
  toFun w := (a⁻¹ * w.1, (Real.sqrt a)⁻¹ • w.2)
  invFun w := (a * w.1, Real.sqrt a • w.2)
  left_inv w := by
    ext <;> simp [ha.ne', (Real.sqrt_pos.mpr ha).ne', smul_smul]
  right_inv w := by
    ext <;> simp [ha.ne', (Real.sqrt_pos.mpr ha).ne', smul_smul]
  map_add' u w := by ext <;> simp [mul_add, smul_add]
  map_smul' c w := by ext <;> simp [smul_smul, mul_assoc, mul_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def rescaleOffset (a z : ℝ) : SpaceTime :=
  (1 - a⁻¹, -((Real.sqrt a)⁻¹ * z) • coordinateVector 2)

def rescale (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) : SpaceTime :=
  parabolicLinear a ha w + rescaleOffset a z

@[simp] theorem rescale_time (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    (rescale a ha z w).1 = 1 - (1 - w.1) / a := by
  change a⁻¹ * w.1 + (1-a⁻¹) = _
  ring

@[simp] theorem rescale_space (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    (rescale a ha z w).2 = (Real.sqrt a)⁻¹ • (w.2 - z • coordinateVector 2) := by
  change (Real.sqrt a)⁻¹ • w.2 + -((Real.sqrt a)⁻¹ * z) • coordinateVector 2 = _
  simp [smul_smul, sub_eq_add_neg]

theorem rescale_past (a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime} (hw : w.1 < 1) :
    (rescale a ha z w).1 < 1 := by
  rw [rescale_time]
  linarith [div_pos (sub_pos.mpr hw) ha]

theorem rescale_radialEnergy (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    AxisymmetricFields.radialEnergy (rescale a ha z w).2 =
      AxisymmetricFields.radialEnergy w.2 / a := by
  rw [rescale_space]
  simp only [AxisymmetricFields.radialEnergy, PiLp.smul_apply, PiLp.sub_apply,
    coordinateVector, PiLp.single_apply, Fin.isValue,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ite_false, smul_eq_mul, mul_zero, sub_zero]
  rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt ha.le]
  ring

theorem rescale_axial_zero (a : ℝ) (ha : 0 < a) (w : SpaceTime) :
    (rescale a ha (w.2 2) w).2 2 = 0 := by
  rw [rescale_space]
  simp [coordinateVector]

theorem parabolicLinear_norm_le {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hqa : q ≤ a) (hq1 : q ≤ 1) :
    ‖(parabolicLinear a ha).toContinuousLinearMap‖ ≤ q⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hq.le)
  intro w
  change ‖(a⁻¹ * w.1, (Real.sqrt a)⁻¹ • w.2)‖ ≤ q⁻¹ * ‖w‖
  rw [Prod.norm_def, max_le_iff, norm_mul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr ha.le),
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  have hai : a⁻¹ ≤ q⁻¹ := inv_le_inv₀ ha hq |>.mpr hqa
  have hsq : q ≤ Real.sqrt a := by
    apply (Real.le_sqrt hq.le ha.le).mpr
    nlinarith [sq_nonneg q]
  have hri : (Real.sqrt a)⁻¹ ≤ q⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr ha) hq).mpr hsq
  constructor
  · exact mul_le_mul hai (norm_fst_le w) (norm_nonneg _) (inv_nonneg.mpr hq.le)
  · exact mul_le_mul hri (norm_snd_le w) (norm_nonneg _) (inv_nonneg.mpr hq.le)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact affine changes of variables lose only the norm of their linear
part, once for each derivative. This does not require global smoothness. -/
theorem norm_iteratedFDeriv_affine_le (L : SpaceTime ≃L[ℝ] SpaceTime)
    (c : SpaceTime) (f : SpaceTime → V) (w : SpaceTime) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (L y + c)) w‖ ≤
      ‖iteratedFDeriv ℝ m f (L w + c)‖ * ‖L.toContinuousLinearMap‖ ^ m := by
  have he := L.iteratedFDerivWithin_comp_right (fun y => f (y+c))
    uniqueDiffOn_univ (mem_univ (L w)) m
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  change iteratedFDeriv ℝ m (fun y => f (L y+c)) w = _ at he
  rw [he, iteratedFDeriv_comp_add_right]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq (by simp)

def normalizedAnnulus (r : ℝ) : Set SpaceTime :=
  {w | w.1 ∈ Icc 0 1 ∧ w.2 2 = 0 ∧ AxisymmetricFields.radialEnergy w.2 ∈ Icc r 1}

theorem normalizedAnnulus_compact (r : ℝ) : IsCompact (normalizedAnnulus r) := by
  have hclosed : IsClosed (normalizedAnnulus r) := by
    apply IsClosed.inter
    · exact isClosed_Icc.preimage continuous_fst
    · apply IsClosed.inter
      · exact isClosed_eq ((EuclideanSpace.proj 2).continuous.comp continuous_snd) continuous_const
      · exact isClosed_Icc.preimage
          ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)
  apply (isCompact_closedBall (0 : SpaceTime) 3).of_isClosed_subset hclosed
  intro w hw
  have hs := EuclideanSpace.real_norm_sq_eq w.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change ‖w.2‖ ^ 2 = w.2 0 ^ 2 + (w.2 1 ^ 2 + w.2 2 ^ 2) at hs
  have hrad := hw.2.2.2
  dsimp only [AxisymmetricFields.radialEnergy] at hrad
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩
  · have hz := hw.2.1
    nlinarith [sq_nonneg ‖w.2‖]

theorem normalize_mem_annulus {h R : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hR : 0 < R) {w : SpaceTime} (hw : w.1 < 1)
    (hX : R < (SlowBorelBase.cartesianChart h w).2.1) :
    let a := max (physicalQ h w) (AxisymmetricFields.radialEnergy w.2)
    rescale a (lt_of_lt_of_le (physicalQ_pos hh hh1 hw) (le_max_left _ _)) (w.2 2) w ∈
      normalizedAnnulus (min R 1) := by
  intro a
  have hq := physicalQ_pos hh hh1 hw
  have ha : 0 < a := hq.trans_le (le_max_left _ _)
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := by
    change R < AxisymmetricFields.radialEnergy w.2 / physicalQ h w at hX
    exact (mul_pos hR hq).trans ((lt_div_iff₀ hq).mp hX)
  have hτ : 1-w.1 ≤ physicalQ h w := by
    have he := SimilarityCoordinates.coordinateQ_spec (by linarith : 0 < 2*h)
      (by linarith : 2*h < 1) (p := (1-w.1,w.2 2)) (sub_pos.mpr hw)
    have hn := mul_nonneg (sq_nonneg (w.2 2)) (Real.rpow_nonneg he.1.le (2*h))
    change 0 ≤ (w.2 2)^2 * physicalQ h w ^ (2*h) at hn
    have heq := he.2
    change physicalQ h w - (w.2 2)^2 * physicalQ h w ^ (2*h) = 1-w.1 at heq
    linarith
  refine ⟨?_, rescale_axial_zero a ha w, ?_⟩
  · rw [rescale_time]
    exact ⟨by linarith [(div_le_one ha).mpr (hτ.trans (le_max_left _ _))],
      by linarith [div_nonneg (sub_nonneg.mpr hw.le) ha.le]⟩
  · rw [rescale_radialEnergy]
    constructor
    · by_cases hqs : physicalQ h w ≤ AxisymmetricFields.radialEnergy w.2
      · rw [show a = AxisymmetricFields.radialEnergy w.2 from max_eq_right hqs,
          div_self hs.ne']
        exact min_le_right _ _
      · rw [show a = physicalQ h w from max_eq_left (le_of_not_ge hqs)]
        exact (min_le_left _ _).trans hX.le
    · exact (div_le_one ha).mpr (le_max_right _ _)

end NavierStokes.WholeDomainHeatBounds

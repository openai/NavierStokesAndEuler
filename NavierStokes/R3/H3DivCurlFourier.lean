import NavierStokes.R3.WeakFourierUniqueness
import Mathlib.Analysis.Fourier.LpSpace

/-! # Orthogonality of square integrable divergence-free and curl-free fields -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace NavierStokesR3.H3DivCurlFourier

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Space)
abbrev ComplexDistribution := TemperedDistribution Space ℂ

def coordinate (i : Fin 3) (ξ : Space) : ℂ := ξ i

theorem coordinate_eq_inner (i : Fin 3) :
    coordinate i = fun ξ : Space => (inner ℝ ξ (coordinateVector i) : ℂ) := by
  funext ξ
  simp [coordinate, coordinateVector, EuclideanSpace.inner_single_right]

theorem coordinate_temperate (i : Fin 3) : (coordinate i).HasTemperateGrowth := by
  rw [coordinate_eq_inner]
  fun_prop

theorem coordinate_continuous (i : Fin 3) : Continuous (coordinate i) := by
  rw [coordinate_eq_inner]
  fun_prop

def multiplier (i : Fin 3) (f : ComplexL2) : ComplexDistribution :=
  TemperedDistribution.smulLeftCLM ℂ (coordinate i) (Lp.toTemperedDistribution f)

theorem multiplier_apply (i : Fin 3) (f : ComplexL2) (ψ : Comparison.ComplexTest) :
    multiplier i f ψ = ∫ ξ : Space, coordinate i ξ * f ξ * ψ ξ := by
  simp only [multiplier, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (coordinate_temperate i)]
  simp only [smul_eq_mul]
  ring

theorem integrable_coordinate_test (i : Fin 3) (f : ComplexL2)
    (ψ : Comparison.ComplexTest) :
    Integrable (fun ξ : Space => coordinate i ξ * f ξ * ψ ξ) := by
  have ht := (SchwartzMap.smulLeftCLM ℂ (coordinate i) ψ).memLp (p := 2) (μ := volume)
  have hi := ht.integrable_mul (Lp.memLp f)
  convert hi using 1
  ext ξ
  simp only [Pi.mul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (coordinate_temperate i)]
  simp only [smul_eq_mul]
  ring

theorem locallyIntegrable_coordinate (i : Fin 3) (f : ComplexL2) :
    LocallyIntegrable (fun ξ : Space => coordinate i ξ * f ξ) volume := by
  have h := ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hm := h.mul_continuousOn (coordinate_continuous i).continuousOn
    isClosed_univ.isLocallyClosed
  simpa only [mul_comm] using locallyIntegrableOn_univ.mp hm

theorem ae_sum_coordinate_eq_zero (f : Fin 3 → ComplexL2)
    (hf : (∑ i : Fin 3, multiplier i (f i)) = 0) :
    ∀ᵐ ξ : Space ∂volume, ∑ i : Fin 3, coordinate i ξ * f i ξ = 0 := by
  apply WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
  · exact locallyIntegrable_finsetSum _ (fun i _ => locallyIntegrable_coordinate i (f i))
  intro ψ
  have h := congrArg (fun T : ComplexDistribution => T ψ) hf
  change (∑ i : Fin 3, multiplier i (f i) ψ) = 0 at h
  simp only [multiplier_apply] at h
  rw [show (fun ξ : Space => (∑ i : Fin 3, coordinate i ξ * f i ξ) * ψ ξ) =
    (fun ξ : Space => ∑ i : Fin 3, coordinate i ξ * f i ξ * ψ ξ) by
      funext ξ; rw [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ => integrable_coordinate_test i (f i) ψ)]
  exact h

theorem ae_coordinate_eq (i j : Fin 3) (f g : ComplexL2)
    (hf : multiplier i f = multiplier j g) :
    ∀ᵐ ξ : Space ∂volume, coordinate i ξ * f ξ = coordinate j ξ * g ξ := by
  have hz : (fun ξ : Space => coordinate i ξ * f ξ - coordinate j ξ * g ξ)
      =ᵐ[volume] 0 := by
    apply WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
    · exact (locallyIntegrable_coordinate i f).sub (locallyIntegrable_coordinate j g)
    intro ψ
    have h := congrArg (fun T : ComplexDistribution => T ψ) hf
    rw [multiplier_apply, multiplier_apply] at h
    simp_rw [sub_mul]
    rw [integral_sub (integrable_coordinate_test i f ψ)
      (integrable_coordinate_test j g ψ), h, sub_self]
  filter_upwards [hz] with ξ hξ
  exact sub_eq_zero.mp hξ

theorem coordinate_conj (i : Fin 3) (ξ : Space) : star (coordinate i ξ) = coordinate i ξ := by
  simp [coordinate]

theorem inner_eq_zero_of_coordinate_relations (ξ : Space) (hξ : ξ ≠ 0)
    (w g : Fin 3 → ℂ)
    (hw : ∑ i : Fin 3, coordinate i ξ * w i = 0)
    (hg : ∀ i j, coordinate i ξ * g j = coordinate j ξ * g i) :
    ∑ i : Fin 3, star (w i) * g i = 0 := by
  have he : ∃ k : Fin 3, coordinate k ξ ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hξ
    ext k
    simpa [coordinate] using hn k
  obtain ⟨k, hk⟩ := he
  have hwc : ∑ i : Fin 3, coordinate i ξ * star (w i) = 0 := by
    have h := congrArg star hw
    simpa only [star_sum, star_mul, coordinate_conj, star_zero, mul_comm] using h
  apply (mul_eq_zero.mp (show coordinate k ξ *
      (∑ i : Fin 3, star (w i) * g i) = 0 from ?_)).resolve_left hk
  calc
    coordinate k ξ * (∑ i : Fin 3, star (w i) * g i) =
        ∑ i : Fin 3, star (w i) * (coordinate k ξ * g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin 3, star (w i) * (coordinate i ξ * g k) := by
      congr 1
      funext i
      rw [hg k i]
    _ = (∑ i : Fin 3, coordinate i ξ * star (w i)) * g k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hwc, zero_mul]

theorem fourier_coordinate_derivative (i : Fin 3) (f : ComplexL2) :
    𝓕 (LineDeriv.lineDerivOp (coordinateVector i) (Lp.toTemperedDistribution f)) =
      (2 * (Real.pi : ℂ) * Complex.I) • multiplier i (𝓕 f) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq]
  rw [multiplier, coordinate_eq_inner]

theorem fourier_constant_ne_zero : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem fourier_divergence (W : Fin 3 → ComplexL2)
    (hW : (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (W i))) = 0) :
    ∀ᵐ ξ : Space ∂volume, ∑ i : Fin 3, coordinate i ξ * (𝓕 (W i)) ξ = 0 := by
  apply ae_sum_coordinate_eq_zero
  have h := congrArg (FourierTransform.fourierCLM ℂ ComplexDistribution) hW
  change 𝓕 (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (W i))) = 𝓕 (0 : ComplexDistribution) at h
  rw [FourierTransform.fourier_sum, FourierTransform.fourier_zero] at h
  simp_rw [fourier_coordinate_derivative] at h
  rw [← Finset.smul_sum] at h
  exact (smul_eq_zero.mp h).resolve_left fourier_constant_ne_zero

theorem fourier_curl (G : Fin 3 → ComplexL2)
    (hG : ∀ i j : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (G j)) = LineDeriv.lineDerivOp (coordinateVector j)
        (Lp.toTemperedDistribution (G i))) :
    ∀ i j : Fin 3, ∀ᵐ ξ : Space ∂volume,
      coordinate i ξ * (𝓕 (G j)) ξ = coordinate j ξ * (𝓕 (G i)) ξ := by
  intro i j
  apply ae_coordinate_eq
  have h := congrArg (FourierTransform.fourierCLM ℂ ComplexDistribution) (hG i j)
  change 𝓕 (LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (G j))) =
    𝓕 (LineDeriv.lineDerivOp (coordinateVector j)
      (Lp.toTemperedDistribution (G i))) at h
  rw [fourier_coordinate_derivative, fourier_coordinate_derivative] at h
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp (show (2 * (Real.pi : ℂ) * Complex.I) •
    (multiplier i (𝓕 (G j)) - multiplier j (𝓕 (G i))) = 0 from ?_)).resolve_left
    fourier_constant_ne_zero
  rw [smul_sub, h, sub_self]

theorem sum_inner_eq_integral (W G : Fin 3 → ComplexL2) :
    (∑ i : Fin 3, inner ℂ (W i) (G i)) =
      ∫ ξ : Space, ∑ i : Fin 3, star (W i ξ) * G i ξ := by
  simp only [L2.inner_def, RCLike.inner_apply]
  rw [integral_finsetSum]
  · congr 1
    funext i
    apply integral_congr_ae
    filter_upwards [] with ξ
    change G i ξ * star (W i ξ) = star (W i ξ) * G i ξ
    exact mul_comm _ _
  · intro i _
    exact ((Lp.memLp (W i)).star).integrable_mul (Lp.memLp (G i))

theorem fourier_inner_ae_zero (W G : Fin 3 → ComplexL2)
    (hW : (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (W i))) = 0)
    (hG : ∀ i j : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (G j)) = LineDeriv.lineDerivOp (coordinateVector j)
        (Lp.toTemperedDistribution (G i))) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ i : Fin 3, star ((𝓕 (W i)) ξ) * (𝓕 (G i)) ξ = 0 := by
  have hd := fourier_divergence W hW
  have hc : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      coordinate i ξ * (𝓕 (G j)) ξ = coordinate j ξ * (𝓕 (G i)) ξ := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact fourier_curl G hG i
  have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by simp [ae_iff]
  filter_upwards [hd, hc, hne] with ξ hdξ hcξ hξ
  exact inner_eq_zero_of_coordinate_relations ξ hξ _ _ hdξ hcξ

/-- Plancherel orthogonality needs only the distributional divergence and curl
equations and square integrability of the two fields. -/
theorem inner_eq_zero_of_divergence_eq_zero_curl_eq_zero (W G : Fin 3 → ComplexL2)
    (hW : (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (W i))) = 0)
    (hG : ∀ i j : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (G j)) = LineDeriv.lineDerivOp (coordinateVector j)
        (Lp.toTemperedDistribution (G i))) :
    ∑ i : Fin 3, inner ℂ (W i) (G i) = 0 := by
  have hF : (∑ i : Fin 3, inner ℂ (W i) (G i)) =
      ∑ i : Fin 3, inner ℂ (𝓕 (W i)) (𝓕 (G i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (Lp.inner_fourier_eq (W i) (G i)).symm
  rw [hF, sum_inner_eq_integral]
  exact integral_eq_zero_of_ae (fourier_inner_ae_zero W G hW hG)

end NavierStokesR3.H3DivCurlFourier

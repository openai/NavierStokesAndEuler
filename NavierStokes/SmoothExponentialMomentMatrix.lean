import NavierStokes.SmoothPowerMomentMatrix
import NavierStokes.ExponentialMomentMatrix

/-!
# Smooth parameter families of exponential bump moments

This is the logarithmic-coordinate clause of `outgoing:moment-rank`. Exponents,
bumps and support intervals may vary with the parameter. The actual integrated
matrix and its nonsingular inverse are smooth, with all fixed inverse jets
bounded on compact parameter sets.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Interval BigOperators Matrix.Norms.Elementwise

namespace NavierStokes.SmoothExponentialMomentMatrix

/-- Primitive data on an open parameter domain. Logarithmic-coordinate support
intervals may lie anywhere on the real line. -/
structure Family (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (U : Set E) where
  exponent : E → Fin n → ℝ
  lower : E → Fin n → ℝ
  upper : E → Fin n → ℝ
  bump : E → Fin n → ℝ → ℝ
  exponent_smooth : ∀ i, ContDiffOn ℝ ∞ (fun p => exponent p i) U
  lower_continuous : ∀ j, ContinuousOn (fun p => lower p j) U
  upper_continuous : ∀ j, ContinuousOn (fun p => upper p j) U
  bump_smooth : ∀ j, ContDiffOn ℝ ∞ (fun z : E × ℝ => bump z.1 j z.2) (U ×ˢ univ)
  exponent_injective : ∀ p ∈ U, Injective (exponent p)
  separated : ∀ p ∈ U, ∀ i j, i < j → upper p i < lower p j
  bump_nonnegative : ∀ p ∈ U, ∀ j t, 0 ≤ bump p j t
  bump_nonzero : ∀ p ∈ U, ∀ j, ∃ t, bump p j t ≠ 0
  bump_support : ∀ p ∈ U, ∀ j, support (bump p j) ⊆ Icc (lower p j) (upper p j)

namespace Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {U : Set E} (D : Family E n U)

/-- Actual integrated exponential weights against the given bump profiles. -/
def matrix (p : E) : Matrix (Fin n) (Fin n) ℝ :=
  ExponentialMomentMatrix.expBumpMomentMatrix (D.exponent p) (D.bump p)

theorem integrand_contDiffOn (i j : Fin n) :
    ContDiffOn ℝ ∞
      (fun z : E × ℝ => Real.exp (D.exponent z.1 i * z.2) * D.bump z.1 j z.2)
      (U ×ˢ univ) := by
  have he : ContDiffOn ℝ ∞ (fun z : E × ℝ => D.exponent z.1 i) (U ×ˢ univ) :=
    (D.exponent_smooth i).comp contDiffOn_fst (fun z hz => hz.1)
  exact (he.mul contDiffOn_snd).exp.mul (D.bump_smooth j)

theorem matrix_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ D.matrix U := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply SmoothPowerMomentMatrix.integral_contDiffOn_of_moving_support U hU _
    (D.integrand_contDiffOn i j) (fun p => D.lower p j) (fun p => D.upper p j)
    (D.lower_continuous j) (D.upper_continuous j)
  intro p hp t ht
  apply D.bump_support p hp j
  intro hb
  exact ht (by dsimp only; rw [hb, mul_zero])

theorem matrix_det_ne_zero (p : E) (hp : p ∈ U) : (D.matrix p).det ≠ 0 := by
  apply ExponentialMomentMatrix.expBumpMomentMatrix_det_ne_zero
    (D.exponent p) (D.lower p) (D.upper p) (D.bump p)
    (D.exponent_injective p hp) (D.separated p hp)
  · intro j
    exact contDiffOn_univ.mp ((D.bump_smooth j).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun t _ => ⟨hp, mem_univ t⟩)) |>.continuous
  · exact D.bump_nonnegative p hp
  · exact D.bump_nonzero p hp
  · exact D.bump_support p hp

theorem matrix_inverse_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun p => (D.matrix p)⁻¹) U :=
  SmoothPowerMomentMatrix.inverse_contDiffOn D.matrix
    (D.matrix_contDiffOn hU) D.matrix_det_ne_zero

/-- Every full parameter jet of the actual inverse has a uniform compact bound. -/
theorem compact_inverse_jet_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  have hj : ContinuousOn (iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹)) U := by
    intro p hp
    exact (((D.matrix_inverse_contDiffOn hU).contDiffAt (hU.mem_nhds hp)).iteratedFDeriv_right
      (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hj.mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

/-- One common constant controls all inverse derivatives up to a fixed order. -/
theorem compact_inverse_jets_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  choose C hC hbound using fun k : Fin (m + 1) =>
    D.compact_inverse_jet_bound hU K hK hKU k.val
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro k hk p hp
  exact (hbound ⟨k, by omega⟩ p hp).trans
    (Finset.single_le_sum (fun t _ => hC t)
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (m + 1))))

end Family
end NavierStokes.SmoothExponentialMomentMatrix

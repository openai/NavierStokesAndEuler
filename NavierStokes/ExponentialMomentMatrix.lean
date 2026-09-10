import NavierStokes.PowerMomentMatrix

/-!
# Exponential moments on separated intervals

The logarithmic-coordinate clause of `outgoing:moment-rank` concerns actual
integrals against positive bumps. The intervals may lie anywhere on the real
line. The proof uses the existing Rolle induction for exponential sums.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NavierStokes.ExponentialMomentMatrix

open PowerMomentMatrix

/-- Exponential moments against finite positive measures on real intervals. -/
def expIntervalMomentMatrix {n : ℕ} (a l u : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t in Set.Icc (l j) (u j), Real.exp (a i * t) ∂μ j

theorem integral_expSum {n : ℕ} (a c : Fin n → ℝ) (l u : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ t in Set.Icc l u, expSum a c t ∂μ) =
      ∑ i, c i * ∫ t in Set.Icc l u, Real.exp (a i * t) ∂μ := by
  unfold expSum
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i _
    apply ContinuousOn.integrableOn_Icc
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn

/-- Distinct exponents and strictly separated positive masses give an
invertible integrated matrix. No sign restriction is imposed on the interval
endpoints in the logarithmic coordinate. -/
theorem expIntervalMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ha : Function.Injective a) (hsep : ∀ i j, i < j → u i < l j)
    (hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0) :
    (expIntervalMomentMatrix a l u μ).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro c d hcd
  dsimp only at hcd
  have hzero : (expIntervalMomentMatrix a l u μ).vecMul (c - d) = 0 := by
    rw [Matrix.sub_vecMul, hcd, sub_self]
  have hroots : ∀ j, ∃ t ∈ Set.Icc (l j) (u j), expSum a (c - d) t = 0 := by
    intro j
    apply exists_zero_of_setIntegral_eq_zero (μ j) (l j) (u j) _ (hmass j)
    · exact (continuous_iff_continuousAt.mpr
        (fun t => (expSum_hasDerivAt a (c - d) t).continuousAt)).continuousOn
    · rw [integral_expSum]
      exact congrFun hzero j
  choose x hx hroot using hroots
  have hxmono : StrictMono x := by
    intro i j hij
    exact lt_of_le_of_lt (hx i).2 (lt_of_lt_of_le (hsep i j hij) (hx j).1)
  exact sub_eq_zero.mp (expSum_coefficients_zero n a (c - d) x ha hxmono hroot)

/-- The actual Lebesgue moment matrix for exponential weights and bumps. -/
def expBumpMomentMatrix {n : ℕ} (a : Fin n → ℝ) (β : Fin n → ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ t, Real.exp (a i * t) * β j t

/-- The logarithmic-coordinate moment-rank assertion for arbitrary distinct
real exponents and separated nonnegative nonzero bumps. Continuity suffices;
the manuscript's smooth bump hypotheses are stronger than required. -/
theorem expBumpMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ) (ha : Function.Injective a)
    (hsep : ∀ i j, i < j → u i < l j)
    (hcont : ∀ j, Continuous (β j)) (hnonneg : ∀ j t, 0 ≤ β j t)
    (hnonzero : ∀ j, ∃ t, β j t ≠ 0)
    (hsupp : ∀ j, Function.support (β j) ⊆ Set.Icc (l j) (u j)) :
    (expBumpMomentMatrix a β).det ≠ 0 := by
  have hcompact : ∀ j, HasCompactSupport (β j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hsupp j)
  have hintegrable : ∀ j, Integrable (β j) := fun j =>
    (hcont j).integrable_of_hasCompactSupport (hcompact j)
  have hout : ∀ j t, t ∉ Set.Icc (l j) (u j) → β j t = 0 := by
    intro j t ht
    by_contra h
    exact ht (hsupp j h)
  let μ : Fin n → Measure ℝ := fun j => volume.withDensity (fun t => ENNReal.ofReal (β j t))
  let : ∀ j, IsFiniteMeasure (μ j) := fun j =>
    isFiniteMeasure_withDensity_ofReal (hintegrable j).2
  have hdensity : ∀ j (f : ℝ → ℝ),
      (∫ t in Set.Icc (l j) (u j), f t ∂μ j) =
        ∫ t in Set.Icc (l j) (u j), β j t * f t := by
    intro j f
    dsimp [μ]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (hcont j).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top) f measurableSet_Icc]
    simp only [ENNReal.toReal_ofReal (hnonneg j _), smul_eq_mul]
  have hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0 := by
    intro j hzero
    have hr : (μ j).restrict (Set.Icc (l j) (u j)) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    have heq := hdensity j (fun _ => (1 : ℝ))
    rw [hr, integral_zero_measure] at heq
    simp only [mul_one] at heq
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hout j)] at heq
    obtain ⟨t, ht⟩ := hnonzero j
    have hpos : 0 < ∫ t, β j t := (hcont j).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hcompact j) (hnonneg j) ht
    linarith
  have hmatrix : expBumpMomentMatrix a β = expIntervalMomentMatrix a l u μ := by
    ext i j
    change (∫ t, Real.exp (a i * t) * β j t) =
      ∫ t in Set.Icc (l j) (u j), Real.exp (a i * t) ∂μ j
    rw [hdensity]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [hout j t ht, zero_mul])]
    congr 1
    ext t
    exact mul_comm _ _
  rw [hmatrix]
  exact expIntervalMomentMatrix_det_ne_zero a l u μ ha hsep hmass

end NavierStokes.ExponentialMomentMatrix

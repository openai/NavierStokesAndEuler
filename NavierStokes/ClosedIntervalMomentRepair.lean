import NavierStokes.ClosedIntervalCkOperators
import NavierStokes.MomentRepairPicard
import NavierStokes.QuadraticLinearization
import NavierStokes.SmoothQuadraticBranch

noncomputable section

namespace NavierStokes.ClosedIntervalMomentRepair

open Set Filter ClosedIntervalCk
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The printed smooth matrix, bilinear coefficient, and moment discrepancy. -/
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  B : ℝ → E →L[ℝ] E
  A : ℝ → E →L[ℝ] E →L[ℝ] E
  d : ℝ → E
  hB : ContDiffOn ℝ ∞ B I
  hA : ContDiffOn ℝ ∞ A I
  hd : ContDiffOn ℝ ∞ d I
  invertible : ∀ x ∈ I, (B x).IsInvertible

namespace Data

variable (D : Data E)

def matrix (k : ℕ) : CK (E := E) k ≃L[ℝ] CK (E := E) k :=
  coefficientEquiv k D.B (D.hB.of_le (by simp)) D.invertible

def bilinearMap (k : ℕ) : CK (E := E) k →L[ℝ] CK (E := E) k →L[ℝ] CK (E := E) k :=
  quadraticOperator k D.A (D.hA.of_le (by simp))

def debt (k : ℕ) : CK (E := E) k := ofContDiffOn D.d (D.hd.of_le (by simp))

/-- The exact norm of multiplication by the inverse matrix on `C^k`. -/
def inverseNorm (k : ℕ) : ℝ := ‖(D.matrix k).symm.toContinuousLinearMap‖

/-- The exact norm of the actual bilinear coefficient operator on `C^k`. -/
def quadraticNorm (k : ℕ) : ℝ := ‖D.bilinearMap k‖

def debtNorm (k : ℕ) : ℝ := ‖D.debt k‖

def Small (k : ℕ) : Prop := 8 * D.inverseNorm k ^ 2 * D.quadraticNorm k * D.debtNorm k ≤ 1

/-- The C⁰ constants coincide with the pointwise suprema printed in the appendix. -/
theorem inverseNorm_zero : D.inverseNorm 0 = ⨆ x : I, ‖(D.B x).inverse‖ :=
  norm_coefficientOperator_zero (fun x => (D.B x).inverse)
    (inverse_coefficient_smooth D.B (D.hB.of_le (by simp)) D.invertible)

theorem quadraticNorm_zero : D.quadraticNorm 0 = ⨆ x : I, ‖D.A x‖ :=
  norm_quadraticOperator_zero D.A (D.hA.of_le (by simp))

theorem debtNorm_zero : D.debtNorm 0 = ⨆ x : I, ‖D.d x‖ := by
  rw [debtNorm, norm_zero_eq_value]
  exact (value 0 (D.debt 0)).norm_eq_iSup_norm

@[simp] theorem matrix_value (k : ℕ) (f : CK (E := E) k) (x : I) :
    value k (D.matrix k f) x = D.B x (value k f x) :=
  coefficientOperator_value k D.B _ f x

@[simp] theorem bilinearMap_value (k : ℕ) (f g : CK (E := E) k) (x : I) :
    value k (D.bilinearMap k f g) x = D.A x (value k f x) (value k g x) :=
  quadraticOperator_value k D.A _ f g x

@[simp] theorem debt_value (k : ℕ) (x : I) : value k (D.debt k) x = D.d x := rfl

theorem matrix_compatible (k : ℕ) (f : CK (E := E) k) :
    lower (Nat.zero_le k) (D.matrix k f) = D.matrix 0 (lower (Nat.zero_le k) f) := by
  apply value_injective 0
  ext x
  simp only [lower_apply, lowerValue_value, matrix_value]

theorem bilinearMap_compatible (k : ℕ) (f g : CK (E := E) k) :
    lower (Nat.zero_le k) (D.bilinearMap k f g) =
      D.bilinearMap 0 (lower (Nat.zero_le k) f) (lower (Nat.zero_le k) g) := by
  apply value_injective 0
  ext x
  simp only [lower_apply, lowerValue_value, bilinearMap_value]

theorem debt_compatible (k : ℕ) : lower (Nat.zero_le k) (D.debt k) = D.debt 0 := by
  apply value_injective 0
  ext x
  simp only [lower_apply, lowerValue_value, debt_value]

/-- One zero-started continuous branch, selected before any stronger norm test. -/
theorem exists_continuous_branch (hsmall : D.Small 0) :
    ∃ c₀ : CK (E := E) 0,
      ‖c₀‖ ≤ 2 * D.inverseNorm 0 * D.debtNorm 0 ∧
      D.matrix 0 c₀ + D.bilinearMap 0 c₀ c₀ = D.debt 0 ∧
      Tendsto (fun n : ℕ =>
        (MomentRepair.correctionIteration (D.matrix 0) (fun c => D.bilinearMap 0 c c) (D.debt 0))^[n] 0)
        atTop (𝓝 c₀) ∧
      ∀ k : ℕ, D.Small k → ∃ cₖ : CK (E := E) k,
        lower (Nat.zero_le k) cₖ = c₀ ∧
        ‖cₖ‖ ≤ 2 * D.inverseNorm k * D.debtNorm k := by
  obtain ⟨c₀, hc₀, he₀, ht₀⟩ := MomentRepairPicardConvergence.exists_small_solution_with_iterates
    (D.matrix 0) (D.bilinearMap 0) (D.debt 0) hsmall
  refine ⟨c₀, hc₀, he₀, ht₀, ?_⟩
  intro k hk
  obtain ⟨cₖ, he, hnorm, _⟩ := MomentRepairPicard.existing_branch_has_stronger_lift
    (lower (Nat.zero_le k)) (D.matrix 0) (D.matrix k)
    (D.bilinearMap 0) (D.bilinearMap k) (D.debt 0) (D.debt k)
    (D.matrix_compatible k) (D.bilinearMap_compatible k) (D.debt_compatible k) ht₀ hk
  exact ⟨cₖ, he, hnorm⟩

theorem pointwise_equation (c₀ : CK (E := E) 0)
    (heq : D.matrix 0 c₀ + D.bilinearMap 0 c₀ c₀ = D.debt 0) :
    ∀ x ∈ I, D.B x (extend (value 0 c₀) x) +
      D.A x (extend (value 0 c₀) x) (extend (value 0 c₀) x) = D.d x := by
  intro x hx
  have he := congrArg (fun f : CK (E := E) 0 => value 0 f ⟨x,hx⟩) heq
  simpa only [map_add, ContinuousMap.add_apply, matrix_value, bilinearMap_value, debt_value,
    extend_of_mem _ hx] using he

theorem pointwise_inverse_bound (x : I) : ‖(D.B x).inverse‖ ≤ D.inverseNorm 0 := by
  exact norm_coefficient_le (fun x => (D.B x).inverse)
    (inverse_coefficient_smooth D.B (D.hB.of_le (by simp)) D.invertible) x

theorem pointwise_bilinear_bound (x : I) : ‖D.A x‖ ≤ D.quadraticNorm 0 :=
  norm_quadratic_coefficient_le D.A (D.hA.of_le (by simp)) x

/-- The C⁰ contraction condition alone gives all one-sided derivatives.
No higher-order smallness assumptions are used for smoothness. -/
theorem continuous_branch_smooth (hsmall : D.Small 0) (c₀ : CK (E := E) 0)
    (hbound : ‖c₀‖ ≤ 2 * D.inverseNorm 0 * D.debtNorm 0)
    (heq : D.matrix 0 c₀ + D.bilinearMap 0 c₀ c₀ = D.debt 0) :
    ContDiffOn ℝ ∞ (extend (value 0 c₀)) I := by
  apply SmoothQuadraticBranch.continuous_quadratic_branch_contDiffOn
    D.B D.A D.d (extend (value 0 c₀)) D.hB D.hA D.hd
    (extend_continuous _).continuousOn (D.pointwise_equation c₀ heq)
  intro x hx
  obtain ⟨e, he⟩ := D.invertible x hx
  have hb : ‖e.symm.toContinuousLinearMap‖ ≤ D.inverseNorm 0 := by
    have hb := D.pointwise_inverse_bound ⟨x,hx⟩
    rwa [← he, ContinuousLinearMap.inverse_equiv] at hb
  have hc : ‖extend (value 0 c₀) x‖ ≤ 2 * D.inverseNorm 0 * D.debtNorm 0 := by
    rw [extend_of_mem _ hx]
    exact ((value 0 c₀).norm_coe_le_norm ⟨x,hx⟩).trans ((norm_value_le c₀).trans hbound)
  rw [← he]
  exact QuadraticLinearization.isInvertible e (D.A x) (extend (value 0 c₀) x)
    (D.inverseNorm 0) (D.quadraticNorm 0) (D.debtNorm 0)
    (norm_nonneg (D.matrix 0).symm.toContinuousLinearMap)
    (norm_nonneg (D.bilinearMap 0)) hb
    (D.pointwise_bilinear_bound ⟨x,hx⟩) hc hsmall

/-- The full quadratic correction assertion: smoothness follows from C⁰
smallness; every additional finite-order estimate applies to this same branch.
Uniqueness is among continuous functions in the printed C⁰ ball. -/
theorem exists_smooth_same_branch (hsmall : D.Small 0) :
    ∃ c : ℝ → E, ∃ hc : ContDiffOn ℝ ∞ c I,
      ‖ofContDiffOn c (hc.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))‖ ≤
        2 * D.inverseNorm 0 * D.debtNorm 0 ∧
      (∀ x ∈ I, D.B x (c x) + D.A x (c x) (c x) = D.d x) ∧
      (∀ k : ℕ, D.Small k →
        ‖ofContDiffOn c (hc.of_le (by simp : (k : ℕ∞ω) ≤ ∞))‖ ≤
          2 * D.inverseNorm k * D.debtNorm k) ∧
      (∀ e : ℝ → E, ∀ he : ContinuousOn e I,
        ‖ofContDiffOn e (contDiffOn_zero.mpr he)‖ ≤ 2 * D.inverseNorm 0 * D.debtNorm 0 →
        (∀ x ∈ I, D.B x (e x) + D.A x (e x) (e x) = D.d x) → EqOn e c I) ∧
      Tendsto (fun n : ℕ =>
        (MomentRepair.correctionIteration (D.matrix 0) (fun f => D.bilinearMap 0 f f) (D.debt 0))^[n] 0)
        atTop (𝓝 (ofContDiffOn c (hc.of_le (by simp : (0 : ℕ∞ω) ≤ ∞)))) := by
  obtain ⟨c₀, hbound, heq, ht, hlift⟩ := D.exists_continuous_branch hsmall
  let c := extend (value 0 c₀)
  have hc : ContDiffOn ℝ ∞ c I := D.continuous_branch_smooth hsmall c₀ hbound heq
  have hembed : ofContDiffOn c (hc.of_le (by simp : (0 : ℕ∞ω) ≤ ∞)) = c₀ := by
    apply value_injective 0
    ext x
    exact extend_apply _ x
  refine ⟨c, hc, ?_, D.pointwise_equation c₀ heq, ?_, ?_, ?_⟩
  · rwa [hembed]
  · intro k hk
    obtain ⟨cₖ, heₖ, hbₖ⟩ := hlift k hk
    have hembedk : ofContDiffOn c (hc.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) = cₖ := by
      apply value_injective k
      ext x
      have hv := congrArg (fun f : CK (E := E) 0 => value 0 f x) heₖ
      simp only [lower_apply, lowerValue_value] at hv
      change extend (value 0 c₀) x = value k cₖ x
      rw [extend_apply, hv]
    rwa [hembedk]
  · intro e he heb hee
    let e₀ : CK (E := E) 0 := ofContDiffOn e (contDiffOn_zero.mpr he)
    have heeq : D.matrix 0 e₀ + D.bilinearMap 0 e₀ e₀ = D.debt 0 := by
      apply value_injective 0
      ext x
      simp only [map_add, ContinuousMap.add_apply, matrix_value, bilinearMap_value, debt_value]
      exact hee x x.property
    have hs : 4 * ‖(D.matrix 0).symm.toContinuousLinearMap‖ * ‖D.bilinearMap 0‖ *
        (2 * D.inverseNorm 0 * D.debtNorm 0) ≤ 1 := by
      change 4 * D.inverseNorm 0 * D.quadraticNorm 0 *
        (2 * D.inverseNorm 0 * D.debtNorm 0) ≤ 1
      calc
        _ = 8 * D.inverseNorm 0 ^ 2 * D.quadraticNorm 0 * D.debtNorm 0 := by ring
        _ ≤ 1 := hsmall
    obtain ⟨u, hu, huniq⟩ := SmoothMomentRepair.exists_unique_quadratic_correction
      (D.matrix 0) (D.bilinearMap 0) (D.debt 0)
      (2 * D.inverseNorm 0 * D.debtNorm 0) (by unfold inverseNorm debtNorm; positivity) hs le_rfl
    have hec : e₀ = c₀ := (huniq e₀ ⟨heb, heeq⟩).trans (huniq c₀ ⟨hbound, heq⟩).symm
    intro x hx
    have hv := congrArg (fun f : CK (E := E) 0 => value 0 f ⟨x,hx⟩) hec
    change e x = extend (value 0 c₀) x
    rw [extend_of_mem _ hx]
    exact hv
  · rwa [hembed]

/-- In the linear case the exact solution needs no smallness condition. -/
theorem linear_solution (hA : ∀ x ∈ I, D.A x = 0) :
    ∃ hc : ContDiffOn ℝ ∞ (fun x => (D.B x).inverse (D.d x)) I,
      (∀ x ∈ I, D.B x ((D.B x).inverse (D.d x)) +
        D.A x ((D.B x).inverse (D.d x)) ((D.B x).inverse (D.d x)) = D.d x) ∧
      ∀ k : ℕ, ‖ofContDiffOn (fun x => (D.B x).inverse (D.d x))
        (hc.of_le (by simp : (k : ℕ∞ω) ≤ ∞))‖ ≤ D.inverseNorm k * D.debtNorm k := by
  have hi : ContDiffOn ℝ ∞ (fun x => (D.B x).inverse) I := by
    intro x hx
    exact ((D.invertible x hx).contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt x
      (D.hB x hx)
  refine ⟨hi.clm_apply D.hd, ?_, ?_⟩
  · intro x hx
    simp only [hA x hx, zero_apply, add_zero]
    exact (D.invertible x hx).self_apply_inverse _
  intro k
  have he : ofContDiffOn (fun x => (D.B x).inverse (D.d x))
      ((hi.clm_apply D.hd).of_le (by simp : (k : ℕ∞ω) ≤ ∞)) = (D.matrix k).symm (D.debt k) := by
    apply value_injective k
    ext x
    change (D.B x).inverse (D.d x) =
      value k (coefficientOperator k (fun x => (D.B x).inverse) _ (D.debt k)) x
    rw [coefficientOperator_value, debt_value]
  rw [he]
  exact (D.matrix k).symm.toContinuousLinearMap.le_opNorm (D.debt k)

end Data
end NavierStokes.ClosedIntervalMomentRepair

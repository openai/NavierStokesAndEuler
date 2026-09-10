import NavierStokes.ClosedIntervalCk
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Nat.Choose.Sum

noncomputable section

namespace NavierStokes.ClosedIntervalCk

open Set
open scoped Topology ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A bounded bilinear map acts on actual finite differentiability spaces pointwise. -/
def postBilinear {k : ℕ} (A : E →L[ℝ] F →L[ℝ] G) (u : CK (E := E) k) (v : CK (E := F) k) :
    CK (E := G) k :=
  ofContDiffOn (fun η => A (extend (value k u) η) (extend (value k v) η))
    ((A.contDiff.comp_contDiffOn (contDiffOn u)).clm_apply (contDiffOn v))

@[simp] theorem postBilinear_value {k : ℕ} (A : E →L[ℝ] F →L[ℝ] G)
    (u : CK (E := E) k) (v : CK (E := F) k) (x : I) :
    value k (postBilinear A u v) x = A (value k u x) (value k v x) := by
  change A (extend (value k u) x) (extend (value k v) x) = _
  rw [extend_apply, extend_apply]

theorem norm_postBilinear_le {k : ℕ} (A : E →L[ℝ] F →L[ℝ] G)
    (u : CK (E := E) k) (v : CK (E := F) k) :
    ‖postBilinear A u v‖ ≤ ‖A‖*(2:ℝ)^k*‖u‖*‖v‖ := by
  apply (norm_ofContDiffOn_le_iff _ _ (by positivity)).mpr
  intro n hn x
  have hb := A.norm_iteratedFDerivWithin_le_of_bilinear (contDiffOn u) (contDiffOn v)
    uniqueDiff x.property (by exact_mod_cast hn : (n : ℕ∞ω) ≤ k)
  simp only [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hb
  have hu (i : ℕ) (hi : i ≤ k) := (norm_le_iff u (norm_nonneg u)).mp le_rfl i hi x
  have hv (i : ℕ) (hi : i ≤ k) := (norm_le_iff v (norm_nonneg v)).mp le_rfl i hi x
  refine hb.trans ?_
  have hs : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      ‖iteratedDerivWithin i (extend (value k u)) I x‖ *
      ‖iteratedDerivWithin (n-i) (extend (value k v)) I x‖) ≤ (2:ℝ)^k*‖u‖*‖v‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖u‖*‖v‖ := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hu i (hin.trans hn)) (Nat.cast_nonneg _))
          (hv (n-i) ((Nat.sub_le _ _).trans hn)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = (2:ℝ)^n*‖u‖*‖v‖ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose n
      _ ≤ (2:ℝ)^k*‖u‖*‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hn) (norm_nonneg _)) (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg A)).trans_eq (by ring)

def bilinearLinear (k : ℕ) (A : E →L[ℝ] F →L[ℝ] G) :
    CK (E := E) k →ₗ[ℝ] CK (E := F) k →ₗ[ℝ] CK (E := G) k where
  toFun u := {
    toFun := postBilinear A u
    map_add' v w := by
      apply value_injective k
      ext x
      simp only [postBilinear_value, map_add, ContinuousMap.add_apply]
    map_smul' c v := by
      apply value_injective k
      ext x
      simp only [postBilinear_value, map_smul, ContinuousMap.smul_apply, RingHom.id_apply] }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply value_injective k
    ext x
    change value k (postBilinear A (u+v) w) x = value k (postBilinear A u w + postBilinear A v w) x
    simp only [postBilinear_value, map_add, ContinuousMap.add_apply, add_apply]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply value_injective k
    ext x
    change value k (postBilinear A (c • u) v) x = value k (c • postBilinear A u v) x
    simp only [postBilinear_value, map_smul, ContinuousMap.smul_apply, smul_apply]



def bilinear (k : ℕ) (A : E →L[ℝ] F →L[ℝ] G) :
    CK (E := E) k →L[ℝ] CK (E := F) k →L[ℝ] CK (E := G) k :=
  LinearMap.mkContinuous₂ (E := CK (E := E) k) (F := CK (E := F) k)
    (G := CK (E := G) k) (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (bilinearLinear k A) (‖A‖*(2:ℝ)^k)
    (fun u v => norm_postBilinear_le A u v)

@[simp] theorem bilinear_apply (k : ℕ) (A : E →L[ℝ] F →L[ℝ] G)
    (u : CK (E := E) k) (v : CK (E := F) k) : bilinear k A u v = postBilinear A u v := rfl

/-- Multiplication by an actual matrix-valued coefficient on `C^k`. -/
def coefficientOperator (k : ℕ) (B : ℝ → E →L[ℝ] F) (hB : ContDiffOn ℝ k B I) :
    CK (E := E) k →L[ℝ] CK (E := F) k :=
  bilinear k (ContinuousLinearMap.apply ℝ F).flip (ofContDiffOn B hB)

@[simp] theorem coefficientOperator_value (k : ℕ) (B : ℝ → E →L[ℝ] F)
    (hB : ContDiffOn ℝ k B I) (f : CK (E := E) k) (x : I) :
    value k (coefficientOperator k B hB f) x = B x (value k f x) := by
  rw [coefficientOperator, bilinear_apply, postBilinear_value, ofContDiffOn_value]
  rfl

/-- The actual bilinear coefficient family acts on the same `C^k` space. -/
def quadraticOperator (k : ℕ) (A : ℝ → E →L[ℝ] F →L[ℝ] G)
    (hA : ContDiffOn ℝ k A I) : CK (E := E) k →L[ℝ] CK (E := F) k →L[ℝ] CK (E := G) k :=
  (bilinear k (ContinuousLinearMap.apply ℝ G).flip).comp (coefficientOperator k A hA)

@[simp] theorem quadraticOperator_value (k : ℕ) (A : ℝ → E →L[ℝ] F →L[ℝ] G)
    (hA : ContDiffOn ℝ k A I) (f : CK (E := E) k) (g : CK (E := F) k) (x : I) :
    value k (quadraticOperator k A hA f g) x = A x (value k f x) (value k g x) := by
  change value k (bilinear k (ContinuousLinearMap.apply ℝ G).flip (coefficientOperator k A hA f) g) x = _
  rw [bilinear_apply, postBilinear_value, coefficientOperator_value]
  rfl

theorem inverse_coefficient_smooth {k : ℕ} (B : ℝ → E →L[ℝ] E)
    (hB : ContDiffOn ℝ k B I) (hinv : ∀ x ∈ I, (B x).IsInvertible) :
    ContDiffOn ℝ k (fun x => (B x).inverse) I := by
  intro x hx
  exact ((hinv x hx).contDiffAt_map_inverse (𝕜 := ℝ) (n := k)).comp_contDiffWithinAt x (hB x hx)

/-- An invertible matrix family gives the genuine multiplication equivalence on `C^k`. -/
def coefficientEquiv (k : ℕ) (B : ℝ → E →L[ℝ] E)
    (hB : ContDiffOn ℝ k B I) (hinv : ∀ x ∈ I, (B x).IsInvertible) :
    CK (E := E) k ≃L[ℝ] CK (E := E) k := by
  let hBi := inverse_coefficient_smooth B hB hinv
  refine ContinuousLinearEquiv.equivOfInverse (coefficientOperator k B hB)
    (coefficientOperator k (fun x => (B x).inverse) hBi) ?_ ?_
  · intro f
    apply value_injective k
    apply ContinuousMap.ext
    intro x
    rw [coefficientOperator_value, coefficientOperator_value]
    obtain ⟨e,he⟩ := hinv x x.property
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.symm_apply_apply _
  · intro f
    apply value_injective k
    apply ContinuousMap.ext
    intro x
    rw [coefficientOperator_value, coefficientOperator_value]
    obtain ⟨e,he⟩ := hinv x x.property
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply _

@[simp] theorem coefficientEquiv_apply (k : ℕ) (B : ℝ → E →L[ℝ] E)
    (hB : ContDiffOn ℝ k B I) (hinv : ∀ x ∈ I, (B x).IsInvertible) (f : CK (E := E) k) :
    coefficientEquiv k B hB hinv f = coefficientOperator k B hB f := rfl

@[simp] theorem coefficientEquiv_symm_apply (k : ℕ) (B : ℝ → E →L[ℝ] E)
    (hB : ContDiffOn ℝ k B I) (hinv : ∀ x ∈ I, (B x).IsInvertible) (f : CK (E := E) k) :
    (coefficientEquiv k B hB hinv).symm f =
      coefficientOperator k (fun x => (B x).inverse) (inverse_coefficient_smooth B hB hinv) f := rfl

@[simp] theorem lower_coefficientOperator {k l : ℕ} (h : l ≤ k)
    (B : ℝ → E →L[ℝ] F) (hB : ContDiffOn ℝ k B I) (f : CK (E := E) k) :
    lower h (coefficientOperator k B hB f) =
      coefficientOperator l B (hB.of_le (by exact_mod_cast h)) (lower h f) := by
  apply value_injective l
  apply ContinuousMap.ext
  intro x
  simp only [lower_apply, lowerValue_value, coefficientOperator_value]

@[simp] theorem lower_quadraticOperator {k l : ℕ} (h : l ≤ k)
    (A : ℝ → E →L[ℝ] F →L[ℝ] G) (hA : ContDiffOn ℝ k A I)
    (f : CK (E := E) k) (g : CK (E := F) k) :
    lower h (quadraticOperator k A hA f g) =
      quadraticOperator l A (hA.of_le (by exact_mod_cast h)) (lower h f) (lower h g) := by
  apply value_injective l
  apply ContinuousMap.ext
  intro x
  simp only [lower_apply, lowerValue_value, quadraticOperator_value]

/-- Constant functions identify the order-zero operator norm with the pointwise one. -/
def constant (k : ℕ) (a : E) : CK (E := E) k :=
  ofContDiffOn (fun _ => a) contDiffOn_const

@[simp] theorem constant_value (k : ℕ) (a : E) (x : I) : value k (constant k a) x = a := rfl

theorem norm_constant_zero (a : E) : ‖constant 0 a‖ = ‖a‖ := by
  apply le_antisymm
  · apply (norm_ofContDiffOn_le_iff _ _ (norm_nonneg a)).mpr
    intro n hn x
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    exact le_rfl
  · have he := ((value 0 (constant 0 a)).norm_coe_le_norm leftEndpoint).trans
      (norm_value_le (constant 0 a))
    exact he

theorem norm_coefficient_le (B : ℝ → E →L[ℝ] F) (hB : ContDiffOn ℝ 0 B I) (x : I) :
    ‖B x‖ ≤ ‖coefficientOperator (E := E) (F := F) 0 B hB‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have he := ((value 0 (coefficientOperator 0 B hB (constant 0 a))).norm_coe_le_norm x).trans
    (norm_value_le _)
  rw [coefficientOperator_value 0 B hB (constant 0 a) x, constant_value] at he
  exact he.trans (by simpa only [norm_constant_zero] using
    (coefficientOperator 0 B hB).le_opNorm (constant 0 a))

theorem norm_quadratic_coefficient_le (A : ℝ → E →L[ℝ] F →L[ℝ] G)
    (hA : ContDiffOn ℝ 0 A I) (x : I) :
    ‖A x‖ ≤ ‖quadraticOperator (E := E) (F := F) (G := G) 0 A hA‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (A x) (norm_nonneg (quadraticOperator 0 A hA))
  intro a
  apply ContinuousLinearMap.opNorm_le_bound (A x a) (by positivity)
  intro b
  have he := ((value 0 (quadraticOperator 0 A hA (constant 0 a) (constant 0 b))).norm_coe_le_norm x).trans
    (norm_value_le _)
  rw [quadraticOperator_value 0 A hA (constant 0 a) (constant 0 b) x,
    constant_value, constant_value] at he
  exact he.trans (by simpa only [norm_constant_zero] using
    (quadraticOperator 0 A hA).le_opNorm₂ (constant 0 a) (constant 0 b))

theorem norm_coefficientOperator_zero_le (B : ℝ → E →L[ℝ] F)
    (hB : ContDiffOn ℝ 0 B I) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ I, ‖B x‖ ≤ M) :
    ‖coefficientOperator 0 B hB‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound (coefficientOperator 0 B hB) hM
  intro f
  rw [norm_zero_eq_value]
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg _))).mpr
  intro x
  rw [coefficientOperator_value 0 B hB f x]
  exact ((B x).le_opNorm (value 0 f x)).trans
    (mul_le_mul (hbound x x.property)
      (((value 0 f).norm_coe_le_norm x).trans (norm_value_le f)) (norm_nonneg _) hM)

theorem norm_quadraticOperator_zero_le (A : ℝ → E →L[ℝ] F →L[ℝ] G)
    (hA : ContDiffOn ℝ 0 A I) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ I, ‖A x‖ ≤ M) :
    ‖quadraticOperator 0 A hA‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound (quadraticOperator 0 A hA) hM
  intro f
  apply ContinuousLinearMap.opNorm_le_bound (quadraticOperator 0 A hA f)
    (mul_nonneg hM (norm_nonneg _))
  intro g
  rw [norm_zero_eq_value]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  rw [quadraticOperator_value 0 A hA f g x]
  exact ((A x).le_opNorm₂ (value 0 f x) (value 0 g x)).trans
    (mul_le_mul (mul_le_mul (hbound x x.property)
      (((value 0 f).norm_coe_le_norm x).trans (norm_value_le f)) (norm_nonneg _) hM)
      (((value 0 g).norm_coe_le_norm x).trans (norm_value_le g)) (norm_nonneg _)
      (mul_nonneg hM (norm_nonneg _)))

/-- The order-zero multiplication norm is exactly the supremum of the
pointwise matrix norms, as in `outgoing:steering`. -/
theorem norm_coefficientOperator_zero (B : ℝ → E →L[ℝ] F) (hB : ContDiffOn ℝ 0 B I) :
    ‖coefficientOperator 0 B hB‖ = ⨆ x : I, ‖B x‖ := by
  let b : Path (E →L[ℝ] F) := value 0 (ofContDiffOn B hB)
  have he : ‖b‖ = ⨆ x : I, ‖B x‖ := b.norm_eq_iSup_norm
  rw [← he]
  apply le_antisymm
  · apply norm_coefficientOperator_zero_le B hB (norm_nonneg b)
    intro x hx
    exact b.norm_coe_le_norm ⟨x,hx⟩
  · apply (ContinuousMap.norm_le b (norm_nonneg _)).mpr
    intro x
    exact norm_coefficient_le B hB x

/-- The order-zero bilinear norm is exactly its pointwise supremum. -/
theorem norm_quadraticOperator_zero (A : ℝ → E →L[ℝ] F →L[ℝ] G) (hA : ContDiffOn ℝ 0 A I) :
    ‖quadraticOperator 0 A hA‖ = ⨆ x : I, ‖A x‖ := by
  let a : Path (E →L[ℝ] F →L[ℝ] G) := value 0 (ofContDiffOn A hA)
  have he : ‖a‖ = ⨆ x : I, ‖A x‖ := a.norm_eq_iSup_norm
  rw [← he]
  apply le_antisymm
  · apply norm_quadraticOperator_zero_le A hA (norm_nonneg a)
    intro x hx
    exact a.norm_coe_le_norm ⟨x,hx⟩
  · apply (ContinuousMap.norm_le a (norm_nonneg (quadraticOperator 0 A hA))).mpr
    intro x
    exact norm_quadratic_coefficient_le A hA x

end NavierStokes.ClosedIntervalCk

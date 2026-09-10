import NavierStokes.PhysicalGraphBounds

noncomputable section
namespace NavierStokes.SharpPhaseJetAlgebra
open scoped ContDiff BigOperators
open NavierStokes.PhysicalGraphBounds

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Leibniz sum preserves a cost per derivative. -/
theorem product_geometric_on {V : Type*} [NormedRing V] [NormedAlgebra ℝ V]
    {f g : E → V} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U) (k : ℕ) {A B D : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A * D ^ i)
    (hgb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B * D ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ k * A * B * D ^ k := by
  have hb := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx (nat_le_infty k)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hb
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * D ^ i) * (B * D ^ (k - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hik) (Nat.cast_nonneg _))
        (hgb (k-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (A * B * D ^ k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show (k.choose i : ℝ) * (A * D ^ i) * (B * D ^ (k-i)) =
        (k.choose i : ℝ) * (A * B * (D ^ i * D ^ (k-i))) by ring,
        ← pow_add, Nat.add_sub_of_le hik]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)) = (2 : ℝ)^k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hc]
      ring

theorem product_geometric {V : Type*} [NormedRing V] [NormedAlgebra ℝ V]
    {f g : E → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (k : ℕ) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A * D ^ i)
    (hgb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B * D ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ k * A * B * D ^ k :=
  product_geometric_on isOpen_univ hf.contDiffOn hg.contDiffOn (Set.mem_univ x)
    k hA hB hD hfb hgb

/-- A uniform outer jet bound composed with geometrically bounded inner jets. -/
theorem composition_geometric {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : F → G}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (m : ℕ)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ B)
    (hfb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (m.factorial : ℝ) * B * D ^ k := by
  intro k hkm
  have h := norm_iteratedFDeriv_comp_le hg hf (nat_le_infty k) x
    (fun i hi => hgb i (hi.trans hkm))
    (fun i hi hik => hfb i hi (hik.trans hkm))
  apply h.trans
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hkm
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hB) (pow_nonneg hD _)



theorem composition_geometric_on {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : F → G} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    {x : E} (hx : x ∈ U) (m : ℕ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ B)
    (hfb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (m.factorial : ℝ) * B * D ^ k := by
  intro k hkm
  have hb := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf (nat_le_infty k)
    uniqueDiffOn_univ hU.uniqueDiffOn (Set.mapsTo_univ _ _) hx
    (C := B) (D := D)
    (fun i hi => by simpa only [iteratedFDerivWithin_univ] using hgb i (hi.trans hkm))
    (fun i hi hik => by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      exact hfb i hi (hik.trans hkm))
  rw [iteratedFDerivWithin_of_isOpen k hU hx] at hb
  apply hb.trans
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hkm
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hB) (pow_nonneg hD _)

end NavierStokes.SharpPhaseJetAlgebra

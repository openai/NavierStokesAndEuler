import NavierStokes.LocalPhysicalCopyBounds
import NavierStokes.SharpPhaseJetAlgebra

noncomputable section
namespace NavierStokes.SharpGeometricModeJets
open Set Function Filter LocalPhysicalCopyBounds
open scoped ContDiff Topology BigOperators

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem smul_geometric {f : E → ℂ} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (k : ℕ)
    {A B D : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A*D^i)
    (hgb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B*D^i) :
    ‖iteratedFDeriv ℝ k (fun y => f y • g y) x‖ ≤ (2:ℝ)^k*A*B*D^k := by
  apply (norm_iteratedFDeriv_smul_le hf hg x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*(A*D^i)*(B*D^(k-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hik) (Nat.cast_nonneg _))
        (hgb (k-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (∑ i ∈ Finset.range (k+1), (k.choose i:ℝ))*(A*B*D^k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show (k.choose i:ℝ)*(A*D^i)*(B*D^(k-i)) =
        (k.choose i:ℝ)*(A*B*(D^i*D^(k-i))) by ring,
        ← pow_add, Nat.add_sub_of_le hik]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)) = (2:ℝ)^k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hc]
      ring

theorem modulated [FiniteDimensional ℝ E]
    {a : E → F} {Φ : E → ℝ} {x : E}
    (ha : SmoothNear a x) (hΦ : SmoothNear Φ x) (m : ℕ)
    {A B D M c : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hD : 0 ≤ D)
    (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hab : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A*D^i)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B*D^i) :
    ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character c (Φ y) • a y) x‖ ≤
      ((2:ℝ)^m*(m.factorial:ℝ)*M^m*B^m)*A*D^m := by
  obtain ⟨a',ha',hea⟩ := ha.exists_global_germ
  obtain ⟨Φ',hΦ',heΦ⟩ := hΦ.exists_global_germ
  have hprod : (fun y => PhysicalGraphBounds.character c (Φ y) • a y) =ᶠ[𝓝 x]
      (fun y => PhysicalGraphBounds.character c (Φ' y) • a' y) := by
    filter_upwards [hea,heΦ] with y hay hφy
    rw [hay,hφy]
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hprod m]
  have hBB := zero_le_one.trans hB
  have hMM := zero_le_one.trans hM
  have hb := SharpPhaseJetAlgebra.composition_geometric hΦ'
    (PhysicalGraphBounds.character_smooth c) x m
    (B := M^m) (D := B*D) (by positivity) (by positivity)
    (by
      intro i hi
      rw [PhysicalGraphBounds.norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans (pow_le_pow_right₀ hM hi))
    (by
      intro i hi him
      rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq heΦ i]
      apply (hΦb i hi him).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_right₀ hB hi) (pow_nonneg hD _))
  have hcar : ∀ i ≤ m, ‖iteratedFDeriv ℝ i
      (PhysicalGraphBounds.character c ∘ Φ') x‖ ≤ ((m.factorial:ℝ)*M^m*B^m)*D^i := by
    intro i hi
    apply (hb i hi).trans
    rw [mul_pow]
    calc
      _ ≤ (m.factorial:ℝ)*M^m*(B^m*D^i) := by gcongr
      _ = _ := by ring
  have ham : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a' x‖ ≤ A*D^i := by
    intro i hi
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  exact (smul_geometric ((PhysicalGraphBounds.character_smooth c).comp hΦ') ha' x m
    (by positivity) hA hD hcar ham).trans_eq (by ring)

end NavierStokes.SharpGeometricModeJets

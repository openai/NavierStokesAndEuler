import NavierStokes.ParametricFlatFactor
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! The flat primitive lemma with coefficients specified only near a compact
parameter rectangle. The factor includes the manuscript's explicit `1/2`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.FlatPrimitivePaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Local smooth coefficient data near a compact set can be extended for
use under the transformed integral. No bound outside that neighborhood is
required. -/
theorem smooth_extension_on_compact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {b : E → ℝ}
    (hb : ContDiffOn ℝ ∞ b U) :
    ∃ b' : E → ℝ, ContDiff ℝ ∞ b' ∧ EqOn b' b K := by
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨f, hfV, hf, hf01⟩ := hV.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgK, hg, hg01⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hsum (x : E) : 0 < f x + g x := by
    have hf0 := (hf01 (mem_range_self x)).1
    have hg0 := (hg01 (mem_range_self x)).1
    by_cases hx : x ∈ K
    · have hfx : f x ≠ 0 := by
        change x ∈ Function.support f
        rw [hfV]
        exact hKV hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 hfx.symm) hg0
    · have hgx : g x ≠ 0 := by
        change x ∈ Function.support g
        rw [hgK]
        exact hx
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 hgx.symm)
  let χ : E → ℝ := fun x => f x / (f x + g x)
  have hχ : ContDiff ℝ ∞ χ := hf.div (hf.add hg) (fun x => (hsum x).ne')
  have hχK : EqOn χ 1 K := by
    intro x hx
    have hgx : g x = 0 := by
      apply Function.notMem_support.mp
      rw [hgK]
      exact not_not.mpr hx
    dsimp [χ]
    rw [hgx, add_zero, div_self (by simpa [hgx] using (hsum x).ne')]
  have hχU : tsupport χ ⊆ U := by
    apply Subset.trans (closure_mono (t := V) ?_) hVU
    intro x hx
    by_contra hxV
    have hfx : f x = 0 := Function.notMem_support.mp (by simpa [hfV] using hxV)
    exact hx (by simp [χ, hfx])
  refine ⟨fun x => χ x * b x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hb.contDiffAt (hU.mem_nhds hx))
    · have hz : χ =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hx' => hx (hχU hx'))
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      change χ y * b y = 0
      change χ y = 0 at hy
      rw [hy, zero_mul]
  · intro x hx
    change χ x * b x = b x
    rw [hχK hx]
    exact one_mul _

/-- The parameterized `heat:flat-primitive` identity and all mixed jet
bounds on a compact rectangle, for locally smooth coefficient data. -/
theorem exists_factor_on_rectangle {K : Set E} (hK : IsCompact K)
    {δ₀ c : ℝ} (hδ : 0 < δ₀) (hc : 0 < c) (j : ℕ)
    {U : Set (E × ℝ)} (hU : IsOpen U) (hKU : K ×ˢ Icc 0 δ₀ ⊆ U)
    {b : E × ℝ → ℝ} (hb : ContDiffOn ℝ ∞ b U) :
    ∃ B : E × ℝ → ℝ, ContDiff ℝ ∞ B ∧
      (∀ p ∈ K, B (p, 0) = b (p, 0) / c) ∧
      (∀ p ∈ K, ∀ δ ∈ Ioc 0 δ₀,
        (∫ u in (0 : ℝ)..δ, (Real.exp (-c / u ^ 2) / u ^ j) * b (p, u)) =
          (1 / 2 : ℝ) * Real.exp (-c / δ ^ 2) * δ ^ (3 - (j : ℝ)) * B (p, δ)) ∧
      (∀ n : ℕ, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ ∈ Icc 0 δ₀,
        ‖iteratedFDeriv ℝ n B (p, δ)‖ ≤ C) := by
  obtain ⟨b', hb', heq⟩ := smooth_extension_on_compact (hK.prod isCompact_Icc) hU hKU hb
  let B : E × ℝ → ℝ := fun x => 2 * ParametricFlatFactor.factor c j b' x
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul (ParametricFlatFactor.factor_contDiff hc j hb')
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro p hp
    dsimp [B]
    rw [ParametricFlatFactor.factor_at_zero hc j b', heq ⟨hp, le_rfl, hδ.le⟩]
    field_simp
  · intro p hp δ hδ'
    have hi : (∫ u in (0 : ℝ)..δ, (Real.exp (-c / u ^ 2) / u ^ j) * b (p, u)) =
        ∫ u in (0 : ℝ)..δ, (Real.exp (-c / u ^ 2) / u ^ j) * b' (p, u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc 0 δ := by simpa [uIcc_of_le hδ'.1.le] using hu
      change _ * b (p, u) = _ * b' (p, u)
      rw [heq (x := (p, u)) ⟨hp, hu'.1, hu'.2.trans hδ'.2⟩]
    rw [hi, ParametricFlatFactor.integral_original_factorization c j b' p hδ'.1]
    dsimp [B]
    ring
  · intro n
    have hcB := hB.continuous_iteratedFDeriv
      (m := n) (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
    obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hcB.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun p hp δ hδ' => (hC (p, δ) ⟨hp, hδ'⟩).trans
      (le_max_left _ _)⟩

end NavierStokes.FlatPrimitivePaper

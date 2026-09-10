import NavierStokes.WeightedClasses

namespace NavierStokes.MeanLocalCoefficient

noncomputable section

open WeightedClasses
open scoped BigOperators ContDiff

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A smooth coefficient with unweighted derivative estimates only on the
specified band-dependent sets. Constants are uniform in band and point. -/
structure LocalCoefficientBounds (s : StripData D) (A : ℕ → Set D) (α : ℝ)
    (f : ℕ → D → ℝ) : Prop where
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n x, x ∈ s.domain → x ∈ A n → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s (fun _ _ => 1) α C p n x

namespace LocalCoefficientBounds

variable {s : StripData D} {A B : ℕ → Set D} {α β : ℝ}
  {f g : ℕ → D → ℝ}

theorem of_unweighted (hf : UnweightedClass s α f) :
    LocalCoefficientBounds s A α f :=
  ⟨hf.smooth, fun m => by
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    exact ⟨C, hC, p, fun n x hx _ j hj => hb n x hx j hj⟩⟩

theorem mono_set (hf : LocalCoefficientBounds s A α f)
    (hBA : ∀ n, B n ⊆ A n) : LocalCoefficientBounds s B α f :=
  ⟨hf.smooth, fun m => by
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    exact ⟨C, hC, p, fun n x hx hB j hj => hb n x hx (hBA n hB) j hj⟩⟩

/-- A coefficient only needs derivative bounds where the mean field can be
nonzero. Every derivative of the product vanishes off its topological support. -/
theorem coefficient_mul (hf : LocalCoefficientBounds s A α f)
    (hg : MeanClass s β g) (hsupport : ∀ n, tsupport (g n) ∩ s.domain ⊆ A n) :
    MeanClass s (α + β) (fun n x => f n x * g n x) := by
  refine ⟨hg.weight_nonneg, fun n => (hf.smooth n).mul (hg.smooth n), ?_⟩
  intro m
  obtain ⟨C, hC, p, hc⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨(2 : ℝ) ^ m * C * B, by positivity, p + q, ?_⟩
  intro n x hx j hj
  by_cases hs : x ∈ tsupport (g n)
  · have hlocal := hsupport n ⟨hs, hx⟩
    have hCmajor : 0 ≤ majorant s (fun _ _ => 1) α C p n x :=
      majorant_nonneg s _ α hC p n x zero_le_one
    have hBmajor : 0 ≤ majorant s (fun _ x => s.zeta x) β B q n x :=
      majorant_nonneg s _ β hB q n x (s.zeta_nonneg x hx)
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (f n) x‖ * ‖iteratedFDeriv ℝ (j - i) (g n) x‖ :=
        JetBounds.norm_iteratedFDeriv_mul_le_on s.isOpen_domain (hf.smooth n)
          (hg.smooth n) hx (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          majorant s (fun _ _ => 1) α C p n x *
            majorant s (fun _ x => s.zeta x) β B q n x := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hc n x hx hlocal i (hij.trans hj))
            (Nat.cast_nonneg _))
          (hb n x hx (j - i) ((Nat.sub_le _ _).trans hj))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hCmajor)
      _ = (2 : ℝ) ^ j * majorant s (fun _ _ => 1) α C p n x *
          majorant s (fun _ x => s.zeta x) β B q n x := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hchoose]
      _ ≤ (2 : ℝ) ^ m * majorant s (fun _ _ => 1) α C p n x *
          majorant s (fun _ x => s.zeta x) β B q n x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCmajor)
          hBmajor
      _ = _ := by
        unfold majorant
        rw [Real.rpow_add (s.epsilon_pos n), pow_add]
        ring
  · have hz : iteratedFDeriv ℝ j (fun y => f n y * g n y) x = 0 := by
      by_contra hn
      exact hs (tsupport_mul_subset_right
        ((tsupport_iteratedFDeriv_subset j) (subset_tsupport _ hn)))
    rw [hz, norm_zero]
    exact majorant_nonneg s _ (α + β) (by positivity) (p + q) n x
      (s.zeta_nonneg x hx)

end LocalCoefficientBounds

end

end NavierStokes.MeanLocalCoefficient

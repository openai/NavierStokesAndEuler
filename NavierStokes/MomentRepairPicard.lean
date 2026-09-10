import NavierStokes.MomentRepairPicardConvergence

/-! Compatibility of the same quadratic correction in two Banach norms.
Both solutions are limits of the same zero-started Picard iterates. -/

noncomputable section

open Filter Function
open scoped Topology

namespace NavierStokes.MomentRepairPicard

variable {E₀ Eₖ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup Eₖ] [NormedSpace ℝ Eₖ]

theorem inverse_compatible (i : Eₖ →L[ℝ] E₀) (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x)) (y : Eₖ) :
    i (Bₖ.symm y) = B₀.symm (i y) := by
  apply B₀.injective
  rw [← hB, Bₖ.apply_symm_apply, B₀.apply_symm_apply]

theorem iteration_compatible (i : Eₖ →L[ℝ] E₀)
    (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (A₀ : E₀ →L[ℝ] E₀ →L[ℝ] E₀) (Aₖ : Eₖ →L[ℝ] Eₖ →L[ℝ] Eₖ)
    (d₀ : E₀) (dₖ : Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x))
    (hA : ∀ x y, i (Aₖ x y) = A₀ (i x) (i y)) (hd : i dₖ = d₀) (x : Eₖ) :
    i (MomentRepair.correctionIteration Bₖ (fun y => Aₖ y y) dₖ x) =
      MomentRepair.correctionIteration B₀ (fun y => A₀ y y) d₀ (i x) := by
  unfold MomentRepair.correctionIteration
  rw [inverse_compatible i B₀ Bₖ hB, map_sub, hd, hA]

/-- The actual Picard iterates agree before taking either norm limit. -/
theorem iterates_compatible (i : Eₖ →L[ℝ] E₀)
    (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (A₀ : E₀ →L[ℝ] E₀ →L[ℝ] E₀) (Aₖ : Eₖ →L[ℝ] Eₖ →L[ℝ] Eₖ)
    (d₀ : E₀) (dₖ : Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x))
    (hA : ∀ x y, i (Aₖ x y) = A₀ (i x) (i y)) (hd : i dₖ = d₀) (n : ℕ) :
    i ((MomentRepair.correctionIteration Bₖ (fun y => Aₖ y y) dₖ)^[n] 0) =
      (MomentRepair.correctionIteration B₀ (fun y => A₀ y y) d₀)^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        iteration_compatible i B₀ Bₖ A₀ Aₖ d₀ dₖ hB hA hd, ih]

/-- Uniqueness of the common limit identifies the branches without any
assumption that the stronger-norm solution lies in the weaker correction ball. -/
theorem limits_compatible (i : Eₖ →L[ℝ] E₀)
    (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (A₀ : E₀ →L[ℝ] E₀ →L[ℝ] E₀) (Aₖ : Eₖ →L[ℝ] Eₖ →L[ℝ] Eₖ)
    (d₀ : E₀) (dₖ : Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x))
    (hA : ∀ x y, i (Aₖ x y) = A₀ (i x) (i y)) (hd : i dₖ = d₀)
    {c₀ : E₀} {cₖ : Eₖ}
    (h₀ : Tendsto (fun n : ℕ => (MomentRepair.correctionIteration B₀ (fun y => A₀ y y) d₀)^[n] 0)
      atTop (𝓝 c₀))
    (hₖ : Tendsto (fun n : ℕ => (MomentRepair.correctionIteration Bₖ (fun y => Aₖ y y) dₖ)^[n] 0)
      atTop (𝓝 cₖ)) : i cₖ = c₀ := by
  apply tendsto_nhds_unique _ h₀
  exact ((i.continuous.tendsto cₖ).comp hₖ).congr
    (iterates_compatible i B₀ Bₖ A₀ Aₖ d₀ dₖ hB hA hd)

/-- Both printed smallness conditions select the same correction. The
exact quantitative estimate holds in each norm on that common branch. -/
theorem exists_compatible_small_solutions [CompleteSpace E₀] [CompleteSpace Eₖ]
    (i : Eₖ →L[ℝ] E₀) (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (A₀ : E₀ →L[ℝ] E₀ →L[ℝ] E₀) (Aₖ : Eₖ →L[ℝ] Eₖ →L[ℝ] Eₖ)
    (d₀ : E₀) (dₖ : Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x))
    (hA : ∀ x y, i (Aₖ x y) = A₀ (i x) (i y)) (hd : i dₖ = d₀)
    (hsmall₀ : 8 * ‖B₀.symm.toContinuousLinearMap‖ ^ 2 * ‖A₀‖ * ‖d₀‖ ≤ 1)
    (hsmallₖ : 8 * ‖Bₖ.symm.toContinuousLinearMap‖ ^ 2 * ‖Aₖ‖ * ‖dₖ‖ ≤ 1) :
    ∃ c₀ : E₀, ∃ cₖ : Eₖ, i cₖ = c₀ ∧
      ‖c₀‖ ≤ 2 * ‖B₀.symm.toContinuousLinearMap‖ * ‖d₀‖ ∧
      ‖cₖ‖ ≤ 2 * ‖Bₖ.symm.toContinuousLinearMap‖ * ‖dₖ‖ ∧
      B₀ c₀ + A₀ c₀ c₀ = d₀ ∧ Bₖ cₖ + Aₖ cₖ cₖ = dₖ := by
  obtain ⟨c₀, hc₀, he₀, ht₀⟩ :=
    MomentRepairPicardConvergence.exists_small_solution_with_iterates B₀ A₀ d₀ hsmall₀
  obtain ⟨cₖ, hcₖ, heₖ, htₖ⟩ :=
    MomentRepairPicardConvergence.exists_small_solution_with_iterates Bₖ Aₖ dₖ hsmallₖ
  exact ⟨c₀, cₖ, limits_compatible i B₀ Bₖ A₀ Aₖ d₀ dₖ hB hA hd ht₀ htₖ,
    hc₀, hcₖ, he₀, heₖ⟩

/-- A previously selected zero-started C⁰ branch satisfies the stronger
norm estimate whenever the corresponding stronger smallness test holds. -/
theorem existing_branch_has_stronger_lift [CompleteSpace Eₖ]
    (i : Eₖ →L[ℝ] E₀) (B₀ : E₀ ≃L[ℝ] E₀) (Bₖ : Eₖ ≃L[ℝ] Eₖ)
    (A₀ : E₀ →L[ℝ] E₀ →L[ℝ] E₀) (Aₖ : Eₖ →L[ℝ] Eₖ →L[ℝ] Eₖ)
    (d₀ : E₀) (dₖ : Eₖ)
    (hB : ∀ x, i (Bₖ x) = B₀ (i x))
    (hA : ∀ x y, i (Aₖ x y) = A₀ (i x) (i y)) (hd : i dₖ = d₀)
    {c₀ : E₀}
    (h₀ : Tendsto (fun n : ℕ => (MomentRepair.correctionIteration B₀ (fun y => A₀ y y) d₀)^[n] 0)
      atTop (𝓝 c₀))
    (hsmallₖ : 8 * ‖Bₖ.symm.toContinuousLinearMap‖ ^ 2 * ‖Aₖ‖ * ‖dₖ‖ ≤ 1) :
    ∃ cₖ : Eₖ, i cₖ = c₀ ∧ ‖cₖ‖ ≤ 2 * ‖Bₖ.symm.toContinuousLinearMap‖ * ‖dₖ‖ ∧
      Bₖ cₖ + Aₖ cₖ cₖ = dₖ := by
  obtain ⟨cₖ, hcₖ, heₖ, htₖ⟩ :=
    MomentRepairPicardConvergence.exists_small_solution_with_iterates Bₖ Aₖ dₖ hsmallₖ
  exact ⟨cₖ, limits_compatible i B₀ Bₖ A₀ Aₖ d₀ dₖ hB hA hd h₀ htₖ, hcₖ, heₖ⟩

end NavierStokes.MomentRepairPicard

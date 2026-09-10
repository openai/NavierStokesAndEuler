import NavierStokes.TrueConeLoop
import NavierStokes.FlatPrimitivePaper
import Mathlib.Topology.MetricSpace.Thickening

/-! Compact loop data specified on a neighborhood of the closed parameter
set suffice for the loop construction and its uniform cone margin. -/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.TrueConeLoopPaper

open TrueConeLoop SmoothLoop LoopMoments LoopVariance ConeAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- All input regularity is local to the compact parameter rectangle. The
output agrees with the original data near the boundary within that rectangle. -/
theorem exists_local_family_with_margin (a m p₁ p₂ : E → ℝ) {K B O : Set E}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K) (hO : IsOpen O) (hKO : K ⊆ O)
    (ha : ContDiffOn ℝ ∞ a O) (hm : ContDiffOn ℝ ∞ m O)
    (hp₁ : ContDiffOn ℝ ∞ p₁ O) (hp₂ : ContDiffOn ℝ ∞ p₂ O)
    (haK : ∀ x ∈ K, 0 < a x)
    (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x))
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    ∃ ε : ℝ, ∃ U N : Set E, ∃ A C : E × ℝ → ℝ,
      0 < ε ∧ IsOpen U ∧ K ⊆ U ∧ IsOpen N ∧ B ⊆ N ∧ N ⊆ U ∧
      ContDiffOn ℝ ∞ A (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ C (U ×ˢ (univ : Set ℝ)) ∧
      (∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1 ∧
        Function.Periodic (fun φ => C (x, φ)) 1 ∧
        (∫ φ in (0 : ℝ)..1, A (x, φ)) = a x ∧
        (∫ φ in (0 : ℝ)..1, C (x, φ)) = a x * m x ∧
        ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ)) ∧
          HasConeMargin ε (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) ∧
      (∀ x ∈ K ∩ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) := by
  obtain ⟨a', ha', hea⟩ := FlatPrimitivePaper.smooth_extension_on_compact hK hO hKO ha
  obtain ⟨m', hm', hem⟩ := FlatPrimitivePaper.smooth_extension_on_compact hK hO hKO hm
  obtain ⟨p₁', hp₁', he₁⟩ := FlatPrimitivePaper.smooth_extension_on_compact hK hO hKO hp₁
  obtain ⟨p₂', hp₂', he₂⟩ := FlatPrimitivePaper.smooth_extension_on_compact hK hO hKO hp₂
  obtain ⟨ε, U, N, A, C, hε, hU, hKU, hN, hBN, hNU, hA, hC, hl, hb⟩ :=
    exists_compact_trueCone_family_with_margin a' m' p₁' p₂' hK hB hBK ha' hm' hp₁' hp₂'
      (fun x hx => by simpa only [hea hx] using haK x hx)
      (fun x hx => by simpa only [he₁ hx, he₂ hx, hem hx] using hPK x hx)
      (fun x hx => by simpa only [hea hx, hem hx, he₁ hx, he₂ hx] using hrelaxed x hx)
      (fun x hx => by simpa only [hea (hBK hx), hem (hBK hx)] using htrueB x hx)
  refine ⟨ε, U, N, A, C, hε, hU, hKU, hN, hBN, hNU, hA, hC, ?_, ?_⟩
  · intro x hx
    simpa only [hea hx, hem hx, he₁ hx, he₂ hx] using hl x hx
  · intro x hx φ
    simpa only [hea hx.1, hem hx.1] using hb x hx.2 φ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The compact boundary neighborhood gives a single positive collar
width for all parameter values and all loop angles. -/
theorem uniform_boundary_collar {K B N : Set E} (hB : IsCompact B)
    (hN : IsOpen N) (hBN : B ⊆ N) {a m : E → ℝ} {A C : E × ℝ → ℝ}
    (hmatch : ∀ x ∈ K ∩ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ B, dist x y < δ →
      ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x := by
  obtain ⟨δ, hδ, hb⟩ := hB.exists_thickening_subset_open hN hBN
  exact ⟨δ, hδ, fun x hx y hy hxy =>
    hmatch x ⟨hx, hb (Metric.mem_thickening_iff.mpr ⟨y, hy, hxy⟩)⟩⟩

end NavierStokes.TrueConeLoopPaper

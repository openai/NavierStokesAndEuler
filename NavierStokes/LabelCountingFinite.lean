import NavierStokes.SlotColoring
import Mathlib.Data.Set.Card

noncomputable section

namespace NavierStokes.LabelCountingFinite

open SlotColoring
open scoped BigOperators

def gridCandidates (c : Grid) (K : Fin 3 → ℕ) : Finset Grid :=
  Fintype.piFinset (fun j => Finset.Icc (c j - (K j : ℤ)) (c j + (K j : ℤ)))

def labelCandidates (n : ℕ) (c : Grid) (K : Fin 3 → ℕ) : Finset Label :=
  ((gridCandidates c K).product (Finset.univ : Finset Bool)).image (fun gs => (n, gs))

theorem mem_gridCandidates_iff (c : Grid) (K : Fin 3 → ℕ) (g : Grid) :
    g ∈ gridCandidates c K ↔ ∀ j, |g j - c j| ≤ (K j : ℤ) := by
  simp only [gridCandidates, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor
  · intro h j
    obtain ⟨hlo, hhi⟩ := h j
    omega
  · intro h j
    obtain ⟨hlo, hhi⟩ := h j
    omega

theorem mem_labelCandidates_iff (n : ℕ) (c : Grid) (K : Fin 3 → ℕ) (L : Label) :
    L ∈ labelCandidates n c K ↔ L.1 = n ∧ ∀ j, |L.2.1 j - c j| ≤ (K j : ℤ) := by
  constructor
  · intro h
    obtain ⟨gs, hgs, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, (mem_gridCandidates_iff c K gs.1).mp (Finset.mem_product.mp hgs).1⟩
  · rintro ⟨hn, hL⟩
    apply Finset.mem_image.mpr
    refine ⟨L.2, Finset.mem_product.mpr ⟨(mem_gridCandidates_iff c K L.2.1).mpr hL,
      Finset.mem_univ _⟩, ?_⟩
    exact Prod.ext hn.symm rfl

theorem gridCandidates_card (c : Grid) (K : Fin 3 → ℕ) :
    (gridCandidates c K).card = ∏ j, (2 * K j + 1) := by
  simp only [gridCandidates, Fintype.card_piFinset, integer_interval_card]

theorem labelCandidates_card (n : ℕ) (c : Grid) (K : Fin 3 → ℕ) :
    (labelCandidates n c K).card = 2 * ∏ j, (2 * K j + 1) := by
  unfold labelCandidates
  rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2)]
  change ((gridCandidates c K) ×ˢ (Finset.univ : Finset Bool)).card = _
  rw [Finset.card_product, gridCandidates_card]
  simp only [Finset.card_univ, Fintype.card_bool, Nat.mul_comm]

theorem finite_of_index_bounds {s : Set Label} (n : ℕ) (c : Grid) (K : Fin 3 → ℕ)
    (hs : ∀ L ∈ s, L.1 = n ∧ ∀ j, |L.2.1 j - c j| ≤ (K j : ℤ)) : s.Finite := by
  apply (labelCandidates n c K).finite_toSet.subset
  intro L hL
  exact (mem_labelCandidates_iff n c K L).mpr (hs L hL)

theorem ncard_le_of_index_bounds {s : Set Label} (n : ℕ) (c : Grid) (K : Fin 3 → ℕ)
    (hs : ∀ L ∈ s, L.1 = n ∧ ∀ j, |L.2.1 j - c j| ≤ (K j : ℤ)) :
    s.ncard ≤ 2 * ∏ j, (2 * K j + 1) := by
  have hsub : s ⊆ (labelCandidates n c K : Set Label) := by
    intro L hL
    exact (mem_labelCandidates_iff n c K L).mpr (hs L hL)
  simpa only [Set.ncard_coe_finset, labelCandidates_card] using
    Set.ncard_le_ncard hsub (labelCandidates n c K).finite_toSet

/-- Count a finite collection of bands while allowing the grid center to
depend on the band. This dependence is essential for physical points viewed
in their respective normalized charts. -/
theorem count_of_band_index_bounds {s : Set Label} (F : Finset ℕ)
    (c : ℕ → Grid) (K : Fin 3 → ℕ)
    (hs : ∀ L ∈ s, L.1 ∈ F ∧ ∀ j, |L.2.1 j - c L.1 j| ≤ (K j : ℤ)) :
    s.Finite ∧ s.ncard ≤ F.card * (2 * ∏ j, (2 * K j + 1)) := by
  classical
  let G := F.biUnion (fun n => labelCandidates n (c n) K)
  have hsub : s ⊆ (G : Set Label) := by
    intro L hL
    obtain ⟨hn, hj⟩ := hs L hL
    exact Finset.mem_biUnion.mpr ⟨L.1, hn,
      (mem_labelCandidates_iff L.1 (c L.1) K L).mpr ⟨rfl, hj⟩⟩
  refine ⟨G.finite_toSet.subset hsub, ?_⟩
  have hcount : G.card ≤ F.card * (2 * ∏ j, (2 * K j + 1)) := by
    calc
      G.card ≤ ∑ n ∈ F, (labelCandidates n (c n) K).card := Finset.card_biUnion_le
      _ = F.card * (2 * ∏ j, (2 * K j + 1)) := by
        simp [labelCandidates_card]
  exact (Set.ncard_le_ncard hsub G.finite_toSet).trans
    (by simpa only [Set.ncard_coe_finset] using hcount)

/-- Five consecutive integer indices include every natural band at distance
at most one from a real logarithmic coordinate. -/
def bandCandidates (c : ℝ) : Finset ℕ :=
  (Finset.Icc (⌊c⌋ - 2) (⌊c⌋ + 2)).image Int.toNat

theorem mem_bandCandidates {c : ℝ} {n : ℕ}
    (hc : c ∈ Set.Icc ((n : ℝ) - 1) ((n : ℝ) + 1)) :
    n ∈ bandCandidates c := by
  have hi : |(n : ℤ) - ⌊c⌋| ≤ (2 : ℤ) := by
    apply index_near_floor c 1 (n : ℤ) 2
    · simp only [Int.cast_natCast, abs_le]
      constructor <;> linarith [hc.1, hc.2]
    · norm_num
  apply Finset.mem_image.mpr
  refine ⟨(n : ℤ), Finset.mem_Icc.mpr ?_, Int.toNat_natCast n⟩
  rw [abs_le] at hi
  omega

theorem bandCandidates_card_le (c : ℝ) : (bandCandidates c).card ≤ 5 := by
  calc
    (bandCandidates c).card ≤ (Finset.Icc (⌊c⌋ - 2) (⌊c⌋ + 2)).card :=
      Finset.card_image_le
    _ = 5 := by simpa using integer_interval_card ⌊c⌋ 2

theorem index_factor_le (n M K : ℕ) (hn : 1 ≤ n) :
    2 * (M * n ^ 6 + K + 1) + 1 ≤ (2 * (M + K + 1) + 1) * n ^ 6 := by
  have hpow : 1 ≤ n ^ 6 := Nat.one_le_pow 6 n hn
  have hconst : 2 * K + 3 ≤ (2 * K + 3) * n ^ 6 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * K + 3) hpow
  calc
    2 * (M * n ^ 6 + K + 1) + 1 = 2 * M * n ^ 6 + (2 * K + 3) := by ring
    _ ≤ 2 * M * n ^ 6 + (2 * K + 3) * n ^ 6 := Nat.add_le_add_left hconst _
    _ = (2 * (M + K + 1) + 1) * n ^ 6 := by ring

theorem box_polynomial_bound (n M K : ℕ) (hn : 1 ≤ n) :
    2 * (∏ _j : Fin 3, (2 * (M * n ^ 6 + K + 1) + 1)) ≤
      (2 * (2 * (M + K + 1) + 1) ^ 3) * n ^ 18 := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    2 * (2 * (M * n ^ 6 + K + 1) + 1) ^ 3 ≤
        2 * ((2 * (M + K + 1) + 1) * n ^ 6) ^ 3 :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (index_factor_le n M K hn) 3)
    _ = (2 * (2 * (M + K + 1) + 1) ^ 3) * n ^ 18 := by ring

theorem radial_polynomial_bound (n M K : ℕ) (hn : 1 ≤ n) :
    2 * (∏ j : Fin 3, (2 * (![M * n ^ 6 + K + 1, K + 1, K + 1] j) + 1)) ≤
      (2 * (2 * (M + K + 1) + 1) * (2 * (K + 1) + 1) ^ 2) * n ^ 6 := by
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc
    2 * ((2 * (M * n ^ 6 + K + 1) + 1) * (2 * (K + 1) + 1) *
        (2 * (K + 1) + 1)) ≤
      2 * (((2 * (M + K + 1) + 1) * n ^ 6) * (2 * (K + 1) + 1) *
        (2 * (K + 1) + 1)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (index_factor_le n M K hn)))
    _ = (2 * (2 * (M + K + 1) + 1) * (2 * (K + 1) + 1) ^ 2) * n ^ 6 := by ring

end NavierStokes.LabelCountingFinite

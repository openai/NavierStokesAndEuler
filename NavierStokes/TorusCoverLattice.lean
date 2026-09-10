import NavierStokes.CommonCoverSolve
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

/-! # The lattice quotient for the common torus cover -/

noncomputable section

namespace NavierStokes.TorusCoverLattice

open CommonCoverSolve TorusInverse

/-- The integer matrix of the one-step covering map. -/
def indexHom : Frequency →+ Frequency where
  toFun := indexMap
  map_zero' := by ext <;> simp [indexMap]
  map_add' x y := by ext <;> simp [indexMap] <;> ring

theorem indexHom_injective : Function.Injective indexHom := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change 3 * x.1 + x.2 = 3 * y.1 + y.2 at h₁
  change x.1 + 5 * x.2 = y.1 + 5 * y.2 at h₂
  ext <;> omega

/-- The quotient coordinate detecting the image of the cover matrix. -/
def residueHom : Frequency →+ ZMod 14 where
  toFun k := (k.2 : ZMod 14) - 5 * (k.1 : ZMod 14)
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem residueHom_surjective : Function.Surjective residueHom := by
  intro z
  refine ⟨(0, z.val), ?_⟩
  simp [residueHom]

theorem indexHom_range_eq_ker : indexHom.range = residueHom.ker := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    change ((n.1 + 5 * n.2 : ℤ) : ZMod 14) -
      5 * ((3 * n.1 + n.2 : ℤ) : ZMod 14) = 0
    push_cast
    calc
      _ = -(14 : ZMod 14) * (n.1 : ZMod 14) := by ring
      _ = 0 := by
        have h14 : (14 : ZMod 14) = 0 := ZMod.natCast_self 14
        rw [h14, neg_zero, zero_mul]
  · intro hk
    have hzero : ((k.2 - 5 * k.1 : ℤ) : ZMod 14) = 0 := by
      simpa [residueHom] using hk
    obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    refine ⟨(-q, k.1 + 3 * q), ?_⟩
    change indexMap (-q, k.1 + 3 * q) = k
    ext <;> simp [indexMap]
    omega

theorem indexHom_range_index : indexHom.range.index = 14 := by
  rw [indexHom_range_eq_ker, AddSubgroup.index_ker,
    residueHom.range_eq_top_of_surjective residueHom_surjective]
  simp

/-- The additive homomorphism of the `d`-step cover. -/
def coverHom : ℕ → Frequency →+ Frequency
  | 0 => AddMonoidHom.id Frequency
  | d + 1 => indexHom.comp (coverHom d)

@[simp] theorem coverHom_apply (d : ℕ) (k : Frequency) :
    coverHom d k = coverIndex d k := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change indexMap (coverHom d k) = _
      rw [ih]
      simp only [coverIndex, Function.iterate_succ_apply']

theorem coverHom_injective (d : ℕ) : Function.Injective (coverHom d) := by
  induction d with
  | zero => exact Function.injective_id
  | succ d ih => exact indexHom_injective.comp ih

/-- Deck-equivalent integer labels differ by an element of this lattice. -/
def coverRange (d : ℕ) : AddSubgroup Frequency := (coverHom d).range

@[simp] theorem mem_coverRange (d : ℕ) (k : Frequency) :
    k ∈ coverRange d ↔ ∃ n, coverIndex d n = k := by
  simp only [coverRange, AddMonoidHom.mem_range, coverHom_apply]

theorem coverRange_succ (d : ℕ) :
    coverRange (d + 1) = (coverRange d).map indexHom :=
  AddMonoidHom.range_comp indexHom (coverHom d)

theorem coverRange_index (d : ℕ) : (coverRange d).index = 14 ^ d := by
  induction d with
  | zero =>
      have h : coverRange 0 = ⊤ := by
        ext k
        simp [mem_coverRange, coverIndex]
      simp [h]
  | succ d ih =>
      rw [coverRange_succ, AddSubgroup.index_map_of_injective _ indexHom_injective,
        ih, indexHom_range_index, pow_succ]

/-- The distinct sheets of the `d`-step cover. -/
abbrev Sheet (d : ℕ) := Frequency ⧸ coverRange d

theorem card_sheet (d : ℕ) : Nat.card (Sheet d) = 14 ^ d := coverRange_index d

instance finite_sheet (d : ℕ) : Finite (Sheet d) :=
  Nat.finite_of_card_ne_zero (by rw [card_sheet]; positivity)

theorem sheet_eq_iff (d : ℕ) (k l : Frequency) :
    (QuotientAddGroup.mk k : Sheet d) = QuotientAddGroup.mk l ↔
      ∃ n, k = l + coverIndex d n := by
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_coverRange]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; abel⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by abel⟩

end NavierStokes.TorusCoverLattice

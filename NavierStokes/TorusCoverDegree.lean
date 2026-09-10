import NavierStokes.CommonCoverSolve
import NavierStokes.TorusCoverLattice

/-!
# Sheets of the integer torus cover

The actual map induced by `[[3,1],[1,5]]` has the lattice quotient as its
fiber. An injective native chart lifts to one disjoint chart per lattice class.
-/

noncomputable section

namespace NavierStokes.TorusCoverDegree

open Set Function TorusInverse SmoothFourierData TorusAverages CommonCoverSolve

/-- Real representatives of every point on the two-dimensional torus. -/
theorem quotientPoint_surjective : Surjective quotientPoint := by
  rintro ⟨x, y⟩
  refine Quotient.inductionOn' x (fun a => ?_)
  refine Quotient.inductionOn' y (fun b => ?_)
  exact ⟨(a, b), rfl⟩

theorem quotientPoint_add (x y : Plane) :
    quotientPoint (x + y) = quotientPoint x + quotientPoint y := by
  ext <;> simp [quotientPoint]

theorem quotientPoint_sub (x y : Plane) :
    quotientPoint (x - y) = quotientPoint x - quotientPoint y := by
  ext <;> simp [quotientPoint]

/-- Equality on the torus is precisely translation by an integral vector. -/
theorem quotientPoint_eq_iff (x y : Plane) :
    quotientPoint x = quotientPoint y ↔ ∃ k : Frequency, x = y + latticePoint k := by
  constructor
  · intro h
    have hz : quotientPoint (x - y) = 0 := by rw [quotientPoint_sub, h, sub_self]
    have h1 : ((x.1 - y.1 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.fst hz
    have h2 : ((x.2 - y.2 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.snd hz
    obtain ⟨k1, hk1⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    obtain ⟨k2, hk2⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
    refine ⟨(k1, k2), ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk1 hk2
    ext <;> dsimp [latticePoint] <;> linarith
  · rintro ⟨k, rfl⟩
    simpa [add_comm] using quotientPoint_lattice_add k y

theorem quotient_coverPower (d : ℕ) (x : Plane) :
    quotientPoint (coverPower d x) = torusCovering^[d] (quotientPoint x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change quotientPoint (coverEquiv (coverPower d x)) = _
      rw [coverEquiv_apply, SlotGeometry.cover_apply]
      change quotientPoint (covering (coverPower d x)) = _
      rw [quotient_covering, ih, Function.iterate_succ_apply']

/-- The explicit inverse chart based at the integral label `k`. -/
def rawLift (d : ℕ) (k : Frequency) (y : Plane) : Torus :=
  quotientPoint ((coverPower d).symm (y + latticePoint k))

theorem covering_rawLift (d : ℕ) (k : Frequency) (y : Plane) :
    torusCovering^[d] (rawLift d k y) = quotientPoint y := by
  rw [rawLift, ← quotient_coverPower, ContinuousLinearEquiv.apply_symm_apply]
  simpa [add_comm] using quotientPoint_lattice_add k y

/-- Integral deck translations give exactly the same inverse chart. -/
theorem rawLift_eq_iff (d : ℕ) (k l : Frequency) (y : Plane) :
    rawLift d k y = rawLift d l y ↔ ∃ n : Frequency, k = l + coverIndex d n := by
  rw [rawLift, rawLift, quotientPoint_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, latticePoint_injective ?_⟩
    have heq := congrArg (coverPower d) hn
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, coverPower_lattice] at heq
    rw [latticePoint_add]
    exact add_left_cancel (by simpa only [add_assoc] using heq)
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [latticePoint_add, ← coverPower_lattice, ← add_assoc, map_add,
      ContinuousLinearEquiv.symm_apply_apply]

/-- Every point over a real native point belongs to one integral inverse chart. -/
theorem covering_eq_iff_rawLift (d : ℕ) (p : Torus) (y : Plane) :
    torusCovering^[d] p = quotientPoint y ↔ ∃ k : Frequency, p = rawLift d k y := by
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := quotientPoint_surjective p
    rw [← quotient_coverPower, quotientPoint_eq_iff] at hp
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, congrArg quotientPoint ((coverPower d).eq_symm_apply.mpr hk)⟩
  · rintro ⟨k, rfl⟩
    exact covering_rawLift d k y

/-- An injective native chart keeps its native coordinate when lifted. -/
theorem rawLift_injOn (d : ℕ) (k : Frequency) {s : Set Plane}
    (hs : InjOn quotientPoint s) : InjOn (rawLift d k) s := by
  intro x hx y hy h
  apply hs hx hy
  have h' := congrArg (torusCovering^[d]) h
  simpa only [covering_rawLift] using h'

/-- Distinct lattice classes give disjoint lifted copies of an injective chart. -/
theorem disjoint_rawLift_images (d : ℕ) (k l : Frequency) {s : Set Plane}
    (hs : InjOn quotientPoint s) (hkl : ¬ ∃ n : Frequency, k = l + coverIndex d n) :
    Disjoint (rawLift d k '' s) (rawLift d l '' s) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  have hxy : rawLift d k x = rawLift d l y := hxp.trans hyp.symm
  have hq : quotientPoint x = quotientPoint y := by
    simpa only [covering_rawLift] using congrArg (torusCovering^[d]) hxy
  have heq := hs hx hy hq
  subst y
  exact hkl ((rawLift_eq_iff d k l x).mp hxy)

/-- The inverse image of a native set is the union of the displayed lifts. -/
theorem preimage_eq_iUnion_rawLift (d : ℕ) (s : Set Plane) :
    (torusCovering^[d]) ⁻¹' (quotientPoint '' s) = ⋃ k : Frequency, rawLift d k '' s := by
  ext p
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨k, hk⟩ := (covering_eq_iff_rawLift d p y).mp hp.symm
    exact ⟨k, y, hy, hk.symm⟩
  · rintro ⟨k, y, hy, rfl⟩
    exact ⟨y, hy, (covering_rawLift d k y).symm⟩

/-- The explicit sheet is the copy-point formula used by the common-cover
ODE construction, with the same center and native basis. -/
theorem rawLift_geometry_point (g : Geometry) (k : Frequency) (z : Plane) :
    rawLift g.gap k (g.center + g.basis z) = quotientPoint (g.point k z) := by
  unfold rawLift Geometry.point
  congr 2
  abel

/-- The original native parameter rectangle. -/
def nativeRectangle (g : Geometry) (r : ℝ) : Set Torus :=
  (fun z => quotientPoint (g.center + g.basis z)) '' Metric.ball (0 : Plane) r

/-- One of the inverse parallelograms displayed in the manuscript. -/
def liftedRectangle (g : Geometry) (r : ℝ) (k : Frequency) : Set Torus :=
  (fun z => quotientPoint (g.point k z)) '' Metric.ball (0 : Plane) r

theorem liftedRectangle_eq_rawLift (g : Geometry) (r : ℝ) (k : Frequency) :
    liftedRectangle g r k = rawLift g.gap k ''
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r) := by
  rw [Set.image_image]
  unfold liftedRectangle
  congr 1
  funext z
  exact (rawLift_geometry_point g k z).symm

theorem preimage_nativeRectangle (g : Geometry) (r : ℝ) :
    (torusCovering^[g.gap]) ⁻¹' nativeRectangle g r =
      ⋃ k : Frequency, liftedRectangle g r k := by
  have heq : nativeRectangle g r = quotientPoint ''
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r) := by
    rw [Set.image_image]
    rfl
  rw [heq, preimage_eq_iUnion_rawLift]
  congr 1
  funext k
  exact (liftedRectangle_eq_rawLift g r k).symm

theorem disjoint_liftedRectangles (g : Geometry) (r : ℝ)
    (hr : ‖(g.basis : Plane →L[ℝ] Plane)‖ * r < 1 / 2)
    (k l : Frequency) (hkl : ¬ ∃ n : Frequency, k = l + coverIndex g.gap n) :
    Disjoint (liftedRectangle g r k) (liftedRectangle g r l) := by
  rw [liftedRectangle_eq_rawLift, liftedRectangle_eq_rawLift]
  exact disjoint_rawLift_images g.gap k l
    (quotientPoint_injOn_small_chart g.basis g.center r hr) hkl

open TorusCoverLattice

/-- One inverse chart for each class in the actual covering lattice. -/
def sheetLift (d : ℕ) (i : Sheet d) (y : Plane) : Torus :=
  Quotient.lift (fun k => rawLift d k y)
    (fun k l h => (rawLift_eq_iff d k l y).mpr
      ((sheet_eq_iff d k l).mp (Quotient.sound h))) i

@[simp] theorem sheetLift_mk (d : ℕ) (k : Frequency) (y : Plane) :
    sheetLift d (QuotientAddGroup.mk k) y = rawLift d k y := rfl

theorem covering_sheetLift (d : ℕ) (i : Sheet d) (y : Plane) :
    torusCovering^[d] (sheetLift d i y) = quotientPoint y := by
  induction i using Quotient.inductionOn with | h k => exact covering_rawLift d k y

theorem sheetLift_injective (d : ℕ) (y : Plane) :
    Injective (fun i : Sheet d => sheetLift d i y) := by
  intro i j
  induction i, j using Quotient.inductionOn₂ with
  | h k l =>
      intro h
      exact (sheet_eq_iff d k l).mpr ((rawLift_eq_iff d k l y).mp h)

/-- Every point of every fiber occurs once, with no duplicated lattice labels. -/
def fiberEquiv (d : ℕ) (y : Plane) :
    Sheet d ≃ {p : Torus // torusCovering^[d] p = quotientPoint y} :=
  Equiv.ofBijective (fun i => ⟨sheetLift d i y, covering_sheetLift d i y⟩) (by
    constructor
    · intro i j h
      exact sheetLift_injective d y (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨k, hk⟩ := (covering_eq_iff_rawLift d p y).mp hp
      exact ⟨QuotientAddGroup.mk k, Subtype.ext hk.symm⟩)

/-- The degree of the actual matrix cover `[[3,1],[1,5]]` after `d` steps. -/
theorem card_fiber (d : ℕ) (p : Torus) :
    Nat.card {x : Torus // torusCovering^[d] x = p} = 14 ^ d := by
  obtain ⟨y, rfl⟩ := quotientPoint_surjective p
  exact (Nat.card_congr (fiberEquiv d y)).symm.trans (card_sheet d)

/-- A native rectangle lifted on the sheet indexed by a lattice class. -/
def sheetRectangle (g : Geometry) (r : ℝ) (i : Sheet g.gap) : Set Torus :=
  sheetLift g.gap i '' ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r)

@[simp] theorem sheetRectangle_mk (g : Geometry) (r : ℝ) (k : Frequency) :
    sheetRectangle g r (QuotientAddGroup.mk k) = liftedRectangle g r k :=
  (liftedRectangle_eq_rawLift g r k).symm

theorem preimage_nativeRectangle_sheets (g : Geometry) (r : ℝ) :
    (torusCovering^[g.gap]) ⁻¹' nativeRectangle g r =
      ⋃ i : Sheet g.gap, sheetRectangle g r i := by
  rw [preimage_nativeRectangle]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨QuotientAddGroup.mk k, by simpa using hk⟩
  · rintro ⟨i, hi⟩
    induction i using Quotient.inductionOn with
    | h k => exact ⟨k, by simpa using hi⟩

theorem pairwise_disjoint_sheetRectangles_of_injOn (g : Geometry) (r : ℝ)
    (hr : InjOn quotientPoint
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r)) :
    Pairwise (fun i j : Sheet g.gap => Disjoint (sheetRectangle g r i)
      (sheetRectangle g r j)) := by
  intro i j
  induction i, j using Quotient.inductionOn₂ with
  | h k l =>
      intro hkl
      simp only [sheetRectangle_mk, liftedRectangle_eq_rawLift]
      exact disjoint_rawLift_images g.gap k l hr (fun h =>
        hkl ((sheet_eq_iff g.gap k l).mpr h))

theorem pairwise_disjoint_sheetRectangles (g : Geometry) (r : ℝ)
    (hr : ‖(g.basis : Plane →L[ℝ] Plane)‖ * r < 1 / 2) :
    Pairwise (fun i j : Sheet g.gap => Disjoint (sheetRectangle g r i)
      (sheetRectangle g r j)) :=
  pairwise_disjoint_sheetRectangles_of_injOn g r
    (quotientPoint_injOn_small_chart g.basis g.center r hr)

theorem sheetRectangle_nonempty (g : Geometry) {r : ℝ} (hr : 0 < r)
    (i : Sheet g.gap) : (sheetRectangle g r i).Nonempty :=
  ((Metric.nonempty_ball.mpr hr).image _).image _

/-- Each of the disjoint pieces maps bijectively to the given native rectangle. -/
theorem covering_bijOn_sheetRectangle_of_injOn (g : Geometry) (r : ℝ)
    (hr : InjOn quotientPoint
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r))
    (i : Sheet g.gap) :
    BijOn (torusCovering^[g.gap]) (sheetRectangle g r i) (nativeRectangle g r) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (covering_sheetLift g.gap i _).symm⟩
  · rintro p ⟨y, hy, rfl⟩ q ⟨z, hz, rfl⟩ h
    have heq : y = z := hr hy hz (by simpa only [covering_sheetLift] using h)
    rw [heq]
  · rintro p ⟨z, hz, rfl⟩
    exact ⟨sheetLift g.gap i (g.center + g.basis z),
      ⟨g.center + g.basis z, ⟨z, hz, rfl⟩, rfl⟩, covering_sheetLift g.gap i _⟩

theorem covering_bijOn_sheetRectangle (g : Geometry) (r : ℝ)
    (hr : ‖(g.basis : Plane →L[ℝ] Plane)‖ * r < 1 / 2)
    (i : Sheet g.gap) :
    BijOn (torusCovering^[g.gap]) (sheetRectangle g r i) (nativeRectangle g r) :=
  covering_bijOn_sheetRectangle_of_injOn g r
    (quotientPoint_injOn_small_chart g.basis g.center r hr) i

/-- The collection of distinct, nonempty lifted rectangles has exactly the
degree of the covering, not merely an upper bound on the number of labels. -/
theorem card_liftedRectangles_of_injOn (g : Geometry) {r : ℝ} (hr : 0 < r)
    (hchart : InjOn quotientPoint
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r)) :
    Nat.card (Set.range (sheetRectangle g r)) = 14 ^ g.gap := by
  have hinj : Injective (sheetRectangle g r) := by
    intro i j hij
    by_contra hne
    have hdis := pairwise_disjoint_sheetRectangles_of_injOn g r hchart hne
    dsimp only at hdis
    rw [hij] at hdis
    exact (sheetRectangle_nonempty g hr j).ne_empty (disjoint_self.mp hdis)
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm.trans (card_sheet g.gap)

theorem card_liftedRectangles (g : Geometry) {r : ℝ} (hr : 0 < r)
    (hsmall : ‖(g.basis : Plane →L[ℝ] Plane)‖ * r < 1 / 2) :
    Nat.card (Set.range (sheetRectangle g r)) = 14 ^ g.gap :=
  card_liftedRectangles_of_injOn g hr
    (quotientPoint_injOn_small_chart g.basis g.center r hsmall)

theorem card_liftedRectangles_le (g : Geometry) {r : ℝ} (hr : 0 < r)
    (hsmall : ‖(g.basis : Plane →L[ℝ] Plane)‖ * r < 1 / 2)
    {maximumGap : ℕ} (hgap : g.gap ≤ maximumGap) :
    Nat.card (Set.range (sheetRectangle g r)) ≤ 14 ^ maximumGap := by
  rw [card_liftedRectangles g hr hsmall]
  exact Nat.pow_le_pow_right (by decide) hgap

end NavierStokes.TorusCoverDegree

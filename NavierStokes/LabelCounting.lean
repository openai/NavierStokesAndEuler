import NavierStokes.SquaredPartition
import Mathlib.Data.Set.Card
import NavierStokes.LabelCountingFinite
import Mathlib.Analysis.Normed.Group.Bounded
import NavierStokes.PhysicalWaveSum

/-!
# Quantitative counts of slow-grid labels

The boxes here use the actual normalized spacing `S_n⁻³` and the actual
`SlotColoring.Label` indices. The radius factor is arbitrary and fixed, so
the counting bounds include every fixed-factor enlargement.
-/

noncomputable section

namespace NavierStokes.LabelCounting

open Set
open scoped BigOperators
open SlotColoring SquaredPartition

/-- A closed slow-coordinate grid box with an arbitrary enlargement factor. -/
def normalizedBox (A : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - nativeSpacing L.1 * (L.2.1 j : ℝ)| ≤ A * nativeSpacing L.1}

/-- Both signs are counted separately, exactly as in the manuscript. -/
def relevantLabels (n : ℕ) (A : ℝ) (B : Set Position) : Set Label :=
  {L | L.1 = n ∧ (normalizedBox A L ∩ B).Nonempty}

theorem nativeSpacing_eq (n : ℕ) : nativeSpacing n = ((n : ℝ) ^ 6)⁻¹ := by
  simp only [nativeSpacing, ChartScales.S, ← pow_mul]

theorem nativeSpacing_mul_six {n : ℕ} (hn : 1 ≤ n) :
    nativeSpacing n * (n : ℝ) ^ 6 = 1 := by
  rw [nativeSpacing_eq, inv_mul_cancel₀]
  exact pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))

/-- A coordinate bounded in physical chart units gives an explicit integer
index bound. The center may vary freely; only the radius affects the count. -/
theorem index_bound {n : ℕ} (hn : 1 ≤ n) {A x c : ℝ} {i : ℤ} {M K : ℕ}
    (hA : A ≤ K) (hx : |x - c| ≤ M)
    (hi : |x - nativeSpacing n * (i : ℝ)| ≤ A * nativeSpacing n) :
    |i - ⌊c / nativeSpacing n⌋| ≤ (M * n ^ 6 + K + 1 : ℕ) := by
  have hd := nativeSpacing_pos hn
  have hdist : |c - nativeSpacing n * (i : ℝ)| ≤ (M : ℝ) + A * nativeSpacing n := by
    have h := abs_sub_le c x (nativeSpacing n * (i : ℝ))
    rw [abs_sub_comm c x] at h
    linarith
  have hgap : |c / nativeSpacing n - (i : ℝ)| ≤ (M : ℝ) * (n : ℝ) ^ 6 + K := by
    calc
      |c / nativeSpacing n - (i : ℝ)| =
          |c - nativeSpacing n * (i : ℝ)| / nativeSpacing n := by
        have he : c / nativeSpacing n - (i : ℝ) =
            (c - nativeSpacing n * (i : ℝ)) / nativeSpacing n := by field_simp
        rw [he, abs_div, abs_of_pos hd]
      _ ≤ ((M : ℝ) + A * nativeSpacing n) / nativeSpacing n :=
        div_le_div_of_nonneg_right hdist hd.le
      _ = (M : ℝ) * (n : ℝ) ^ 6 + A := by
        rw [add_div, mul_div_cancel_right₀ _ hd.ne']
        simp [nativeSpacing_eq, div_eq_mul_inv]
      _ ≤ (M : ℝ) * (n : ℝ) ^ 6 + K := by linarith
  apply index_near_floor _ _ _ _ hgap
  push_cast
  rfl

theorem slowMask_tsupport_subset_normalizedBox {n : ℕ} (hn : 1 ≤ n)
    (k : Grid) (σ : Bool) {A : ℝ} (hA : 1 ≤ A) :
    tsupport (slowMask n k) ⊆ normalizedBox A (n, k, σ) := by
  intro x hx j
  have hj := slowMask_tsupport_subset hn k hx j (mem_univ j)
  change |x j - nativeSpacing n * (k j : ℝ)| ≤ A * nativeSpacing n
  have hδ := nativeSpacing_pos hn
  have hm : nativeSpacing n ≤ A * nativeSpacing n := by nlinarith
  rw [abs_le]
  constructor <;> linarith [hj.1, hj.2]

/-- Explicit count for any chart region contained in a coordinate rectangle.
Coordinates of radius zero make only a constant contribution to this bound. -/
theorem rectangle_count {n : ℕ} (hn : 1 ≤ n) {A : ℝ} {K : ℕ} (hA : A ≤ K)
    (B : Set Position) (c : Position) (M : Fin 3 → ℕ)
    (hB : ∀ x ∈ B, ∀ j, |x j - c j| ≤ (M j : ℝ)) :
    (relevantLabels n A B).Finite ∧
      (relevantLabels n A B).ncard ≤ 2 * ∏ j, (2 * (M j * n ^ 6 + K + 1) + 1) := by
  have hi : ∀ L ∈ relevantLabels n A B, L.1 = n ∧
      ∀ j, |L.2.1 j - ⌊c j / nativeSpacing n⌋| ≤ (M j * n ^ 6 + K + 1 : ℕ) := by
    intro L hL
    obtain ⟨hl, x, hx, hxB⟩ := hL
    refine ⟨hl, fun j => ?_⟩
    apply index_bound hn hA (hB x hxB j)
    simpa only [normalizedBox, mem_ofPred_eq, hl] using hx j
  exact ⟨LabelCountingFinite.finite_of_index_bounds n _ _ hi,
    LabelCountingFinite.ncard_le_of_index_bounds n _ _ hi⟩

/-- A normalized radial slice; the two transverse coordinates are arbitrary. -/
def radialSlice (I : Set ℝ) (Z T : ℝ) : Set Position :=
  {x | x 0 ∈ I ∧ x 1 = Z ∧ x 2 = T}

theorem radial_rectangle_count {n : ℕ} (hn : 1 ≤ n) {A : ℝ} {K M : ℕ}
    (hA : A ≤ K) (I : Set ℝ) (hI : ∀ r ∈ I, |r| ≤ (M : ℝ)) (Z T : ℝ) :
    (relevantLabels n A (radialSlice I Z T)).Finite ∧
      (relevantLabels n A (radialSlice I Z T)).ncard ≤
        2 * ∏ j, (2 * (![M, 0, 0] j * n ^ 6 + K + 1) + 1) := by
  apply rectangle_count hn hA _ ![0, Z, T] ![M, 0, 0]
  intro x hx j
  fin_cases j
  · simpa using hI _ hx.1
  · simp [hx.2.1]
  · simp [hx.2.2]

/-- The three-coordinate count with its polynomial dependence separated from
the fixed chart radius and the fixed box enlargement. -/
theorem chart_count_of_coordinate_bound {n : ℕ} (hn : 1 ≤ n) {A : ℝ}
    {K M : ℕ} (hA : A ≤ K) (B : Set Position)
    (hB : ∀ x ∈ B, ∀ j, |x j| ≤ (M : ℝ)) :
    (relevantLabels n A B).Finite ∧
      ((relevantLabels n A B).ncard : ℝ) ≤
        (2 * (2 * ((M : ℝ) + K + 1) + 1) ^ 3) * ChartScales.S n ^ 9 := by
  obtain ⟨hfin, hcard⟩ := rectangle_count hn hA B 0 (fun _ => M)
    (by simpa only [Pi.zero_apply, sub_zero] using hB)
  refine ⟨hfin, ?_⟩
  have hb := hcard.trans (LabelCountingFinite.box_polynomial_bound n M K hn)
  have hr : ((relevantLabels n A B).ncard : ℝ) ≤
      (2 * (2 * ((M : ℝ) + K + 1) + 1) ^ 3) * (n : ℝ) ^ 18 := by
    exact_mod_cast hb
  simpa only [ChartScales.S, ← pow_mul] using hr

/-- The radial count has only one growing coordinate. Its constant is
independent of both transverse coordinates, including arbitrarily large ones. -/
theorem radial_count_of_bound {n : ℕ} (hn : 1 ≤ n) {A : ℝ} {K M : ℕ}
    (hA : A ≤ K) (I : Set ℝ) (hI : ∀ r ∈ I, |r| ≤ (M : ℝ)) (Z T : ℝ) :
    (relevantLabels n A (radialSlice I Z T)).Finite ∧
      ((relevantLabels n A (radialSlice I Z T)).ncard : ℝ) ≤
        (2 * (2 * ((M : ℝ) + K + 1) + 1) * (2 * (K + 1) + 1) ^ 2) *
          ChartScales.S n ^ 3 := by
  obtain ⟨hfin, hcard⟩ := radial_rectangle_count hn hA I hI Z T
  refine ⟨hfin, ?_⟩
  have hpoly := LabelCountingFinite.radial_polynomial_bound n M K hn
  simp [Fin.prod_univ_three] at hcard hpoly
  have hb := hcard.trans hpoly
  have hr : ((relevantLabels n A (radialSlice I Z T)).ncard : ℝ) ≤
      (2 * (2 * ((M : ℝ) + K + 1) + 1) * (2 * (K + 1) + 1) ^ 2) *
        (n : ℝ) ^ 6 := by
    exact_mod_cast hb
  simpa only [ChartScales.S, ← pow_mul] using hr

/-- The compact-chart estimate of `geom:counting-bounds`, proved for every
bounded chart set. The one constant works in every positive band. -/
theorem bounded_chart_count (A : ℝ) {B : Set Position} (hB : Bornology.IsBounded B) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      (relevantLabels n A B).Finite ∧
        ((relevantLabels n A B).ncard : ℝ) ≤ C * ChartScales.S n ^ 9 := by
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_ge R
  obtain ⟨K, hK⟩ := exists_nat_ge A
  refine ⟨2 * (2 * ((M : ℝ) + K + 1) + 1) ^ 3, by positivity, ?_⟩
  intro n hn
  apply chart_count_of_coordinate_bound hn hK B
  intro x hx j
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans ((hR x hx).trans hM)

/-- Compact chart sets satisfy the manuscript's `C_B S_n^9` estimate.
The enlargement factor is arbitrary and affects only `C_B`. -/
theorem compact_chart_count (A : ℝ) {B : Set Position} (hB : IsCompact B) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      (relevantLabels n A B).Finite ∧
        ((relevantLabels n A B).ncard : ℝ) ≤ C * ChartScales.S n ^ 9 :=
  bounded_chart_count A hB.isBounded

/-- The radial-line estimate of `geom:counting-bounds`. A single constant
works simultaneously for all bands and all `Z,T`. Bounded intervals are
included; no closedness or endpoint conventions are needed. -/
theorem bounded_radial_count (A : ℝ) {I : Set ℝ} (hI : Bornology.IsBounded I) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ Z T : ℝ,
      (relevantLabels n A (radialSlice I Z T)).Finite ∧
        ((relevantLabels n A (radialSlice I Z T)).ncard : ℝ) ≤ C * ChartScales.S n ^ 3 := by
  obtain ⟨R, hR⟩ := hI.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_ge R
  obtain ⟨K, hK⟩ := exists_nat_ge A
  refine ⟨2 * (2 * ((M : ℝ) + K + 1) + 1) * (2 * (K + 1) + 1) ^ 2,
    by positivity, ?_⟩
  intro n hn Z T
  apply radial_count_of_bound hn hK I _ Z T
  intro r hr
  simpa only [Real.norm_eq_abs] using (hR r hr).trans hM

/-- Labels whose genuine closed dyadic band and enlarged slow box contain
the point. Each band uses its own physical-to-normalized chart. -/
def pointwiseLabels (D A q : ℝ) (x : Position) : Set Label :=
  {L | 1 ≤ L.1 ∧ q ∈ tsupport (dyadicMask (L.1 : ℤ)) ∧
    slowCoordinates D L.1 x ∈ normalizedBox A L}

/-- For arbitrary fixed slow-box enlargement, no more than five bands and
a constant number of grid indices per band contribute at a point. -/
theorem pointwise_count_of_bound (D : ℝ) {A : ℝ} {K : ℕ} (hA : A ≤ K)
    (q : ℝ) (x : Position) :
    (pointwiseLabels D A q x).Finite ∧
      (pointwiseLabels D A q x).ncard ≤ 5 * (2 * (2 * (K + 1) + 1) ^ 3) := by
  by_cases hq : 0 < q
  · have hs : ∀ L ∈ pointwiseLabels D A q x,
        L.1 ∈ LabelCountingFinite.bandCandidates (logCoordinate q) ∧
        ∀ j, |L.2.1 j - ⌊slowCoordinates D L.1 x j / nativeSpacing L.1⌋| ≤
          ((fun _ : Fin 3 => K + 1) j : ℤ) := by
      intro L hL
      have hb : ChartScales.Q L.1 / 2 ≤ q ∧ q ≤ 2 * ChartScales.Q L.1 := by
        simpa only [dyadicMask_tsupport, integerQ_nat, mem_Icc] using hL.2.1
      refine ⟨LabelCountingFinite.mem_bandCandidates
        (PhysicalWaveSum.logCoordinate_in_band hq hb.1 hb.2), ?_⟩
      intro j
      have hi := index_bound hL.1 hA (M := 0)
        (x := slowCoordinates D L.1 x j) (c := slowCoordinates D L.1 x j)
        (by simp) (hL.2.2 j)
      simpa only [Nat.zero_mul, Nat.zero_add] using hi
    obtain ⟨hfin, hcount⟩ := LabelCountingFinite.count_of_band_index_bounds
      (LabelCountingFinite.bandCandidates (logCoordinate q))
      (fun n j => ⌊slowCoordinates D n x j / nativeSpacing n⌋) (fun _ => K + 1) hs
    refine ⟨hfin, hcount.trans ?_⟩
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Nat.mul_le_mul_right (2 * (2 * (K + 1) + 1) ^ 3)
        (LabelCountingFinite.bandCandidates_card_le (logCoordinate q))
  · have he : pointwiseLabels D A q x = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro L hL
      have hb : ChartScales.Q L.1 / 2 ≤ q ∧ q ≤ 2 * ChartScales.Q L.1 := by
        simpa only [dyadicMask_tsupport, integerQ_nat, mem_Icc] using hL.2.1
      exact hq ((div_pos (ChartScales.Q_pos L.1) (by norm_num)).trans_le hb.1)
    simp [he]

/-- The uniform pointwise overlap estimate, including every fixed-factor
enlargement of the mesh boxes. The constant is also independent of `D`. -/
theorem pointwise_count (A : ℝ) :
    ∃ C > 0, ∀ D q : ℝ, ∀ x : Position,
      (pointwiseLabels D A q x).Finite ∧
        ((pointwiseLabels D A q x).ncard : ℝ) ≤ C := by
  obtain ⟨K, hK⟩ := exists_nat_ge A
  refine ⟨(5 * (2 * (2 * ((K : ℝ) + 1) + 1) ^ 3)), by positivity, ?_⟩
  intro D q x
  obtain ⟨hfin, hcount⟩ := pointwise_count_of_bound D hK q x
  exact ⟨hfin, by exact_mod_cast hcount⟩

/-- The original mask-support regions are contained in every enlargement
of factor at least one. Thus the count above applies to the actual labels
of the constructed partition, including their support boundaries. -/
theorem labelRegion_subset_pointwiseLabels {D A q : ℝ} {x : Position} {L : Label}
    (hA : 1 ≤ A) (hn : 1 ≤ L.1)
    (hL : (q, x) ∈ PhysicalWaveSum.labelRegion D L) :
    L ∈ pointwiseLabels D A q x := by
  refine ⟨hn, hL.1, slowMask_tsupport_subset_normalizedBox hn L.2.1 L.2.2 hA ?_⟩
  have hs : tsupport (physicalSlowMask D L.1 L.2.1) ⊆
      (slowCoordinates D L.1) ⁻¹' tsupport (slowMask L.1 L.2.1) := by
    apply closure_minimal
    · intro y hy
      exact subset_tsupport (slowMask L.1 L.2.1) hy
    · exact isClosed_closure.preimage (slowCoordinates_smooth D L.1).continuous
  exact hs hL.2

/-- All three conclusions of `geom:label-counts` for an arbitrary fixed
enlargement. Constants are chosen before the band and point variables. -/
theorem number_of_relevant_labels (A : ℝ) :
    (∃ C > 0, ∀ D q : ℝ, ∀ x : Position,
      (pointwiseLabels D A q x).Finite ∧
        ((pointwiseLabels D A q x).ncard : ℝ) ≤ C) ∧
    (∀ B : Set Position, IsCompact B → ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      (relevantLabels n A B).Finite ∧
        ((relevantLabels n A B).ncard : ℝ) ≤ C * ChartScales.S n ^ 9) ∧
    (∀ I : Set ℝ, Bornology.IsBounded I → ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ Z T : ℝ,
      (relevantLabels n A (radialSlice I Z T)).Finite ∧
        ((relevantLabels n A (radialSlice I Z T)).ncard : ℝ) ≤ C * ChartScales.S n ^ 3) :=
  ⟨pointwise_count A, fun _ hB => compact_chart_count A hB,
    fun _ hI => bounded_radial_count A hI⟩

/-- Admissibility restrictions on labels can only reduce any of the three
counts. This applies without any finiteness assumption on the restriction
`Γ` itself. -/
theorem restrict_count (Γ : Set Label) {s : Set Label} {C : ℝ}
    (hs : s.Finite ∧ (s.ncard : ℝ) ≤ C) :
    (Γ ∩ s).Finite ∧ ((Γ ∩ s).ncard : ℝ) ≤ C := by
  refine ⟨hs.1.subset inter_subset_right, ?_⟩
  have hcard : ((Γ ∩ s).ncard : ℝ) ≤ s.ncard := by
    exact_mod_cast Set.ncard_le_ncard inter_subset_right hs.1
  exact hcard.trans hs.2

/-- Literal label-family version of the three counting bounds. The fixed
set `Γ` may impose every admissibility condition of the construction. -/
theorem number_of_relevant_labels_restrict (A : ℝ) (Γ : Set Label) :
    (∃ C > 0, ∀ D q : ℝ, ∀ x : Position,
      (Γ ∩ pointwiseLabels D A q x).Finite ∧
        ((Γ ∩ pointwiseLabels D A q x).ncard : ℝ) ≤ C) ∧
    (∀ B : Set Position, IsCompact B → ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      (Γ ∩ relevantLabels n A B).Finite ∧
        ((Γ ∩ relevantLabels n A B).ncard : ℝ) ≤ C * ChartScales.S n ^ 9) ∧
    (∀ I : Set ℝ, Bornology.IsBounded I → ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ Z T : ℝ,
      (Γ ∩ relevantLabels n A (radialSlice I Z T)).Finite ∧
        ((Γ ∩ relevantLabels n A (radialSlice I Z T)).ncard : ℝ) ≤
          C * ChartScales.S n ^ 3) := by
  obtain ⟨⟨C, hC, hpoint⟩, hchart, hradial⟩ := number_of_relevant_labels A
  refine ⟨⟨C, hC, fun D q x => restrict_count Γ (hpoint D q x)⟩, ?_, ?_⟩
  · intro B hB
    obtain ⟨C, hC, hcount⟩ := hchart B hB
    exact ⟨C, hC, fun n hn => restrict_count Γ (hcount n hn)⟩
  · intro I hI
    obtain ⟨C, hC, hcount⟩ := hradial I hI
    exact ⟨C, hC, fun n hn Z T => restrict_count Γ (hcount n hn Z T)⟩

theorem physicalBox_iff_normalizedBox (D : ℝ) {n : ℕ} (_hn : 1 ≤ n)
    (k : Grid) (σ : Bool) (x : Position) :
    x ∈ physicalBox D (n, k, σ) ↔
      slowCoordinates D n x ∈ normalizedBox 2 (n, k, σ) := by
  have hw (j : Fin 3) : width D j n =
      ChartScales.Q n ^ axisExponent D j * nativeSpacing n := by
    unfold width
    rw [spacing_eq_scaled_mesh]
    simp only [ChartScales.Q, nativeSpacing, ChartScales.S, one_div]
  have he (j : Fin 3) :
      |slowCoordinates D n x j - nativeSpacing n * (k j : ℝ)| =
      |x j - width D j n * (k j : ℝ)| / ChartScales.Q n ^ axisExponent D j := by
    have hq := Real.rpow_pos_of_pos (ChartScales.Q_pos n) (axisExponent D j)
    have he : slowCoordinates D n x j - nativeSpacing n * (k j : ℝ) =
        (x j - width D j n * (k j : ℝ)) / ChartScales.Q n ^ axisExponent D j := by
      dsimp [slowCoordinates]
      rw [hw]
      field_simp
    rw [he, abs_div, abs_of_pos hq]
  change (∀ j, |x j - width D j n * (k j : ℝ)| ≤ 2 * width D j n) ↔ _
  change _ ↔ ∀ j, |slowCoordinates D n x j - nativeSpacing n * (k j : ℝ)| ≤
    2 * nativeSpacing n
  simp only [he]
  apply forall_congr'
  intro j
  have hq := Real.rpow_pos_of_pos (ChartScales.Q_pos n) (axisExponent D j)
  rw [div_le_iff₀ hq, hw]
  constructor <;> intro h <;> nlinarith

end NavierStokes.LabelCounting

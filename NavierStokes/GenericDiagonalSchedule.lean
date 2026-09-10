import NavierStokes.CutStageEstimates

/-!
# A common diagonal schedule with arbitrary additional finite tests

The same sequence of cutoff scales enforces all field jet estimates and any
prescribed finite family of positive-power logarithmic tests at each stage.
The bounds apply throughout the reciprocal interval, including its endpoint.
-/

noncomputable section

namespace NavierStokes.GenericDiagonalSchedule

open Set Function Filter
open scoped Topology ContDiff BigOperators

/-- The logarithmic power and the positive decay power may both depend on the
individual member of the finite family. -/
theorem exists_integer_scale_variable {κ : Type*} (s : Finset κ)
    (B P γ : κ → ℝ) (hγ : ∀ k ∈ s, 0 < γ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ, 0 < a ∧ ∀ k ∈ s, ∀ r : ℝ, 0 < r → r ≤ 1 / (a : ℝ) →
      |DiagonalScale.logPowerWeight (B k) (P k) (γ k) r| ≤ ε := by
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ k ∈ s, |DiagonalScale.logPowerWeight (B k) (P k) (γ k) r| < ε := by
    apply (eventually_all_finset s).2
    intro k hk
    have hlim := (DiagonalScale.tendsto_logPowerWeight (B k) (P k) (γ k) (hγ k hk)).abs
    simp only [abs_zero] at hlim
    exact hlim.eventually (gt_mem_nhds hε)
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 hsmall with ⟨δ, hδ, hb⟩
  change (0 : ℝ) < δ at hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  intro k hk r hr hra
  apply (hb ⟨hr, ?_⟩ k hk).le
  apply hra.trans_lt
  simpa only [Nat.cast_add, Nat.cast_one] using hn

/-- One doubling sequence dominates any prescribed sequence of lower bounds
and meets an arbitrary finite list of tests at each stage. All cutoff supports
lie strictly below the prescribed positive outer boundary. -/
theorem exists_scales_with_tests {κ : Type*} (tests : ℕ → Finset κ)
    (B P γ : ℕ → κ → ℝ) (hγ : ∀ j k, k ∈ tests j → 0 < γ j k)
    (lower : ℕ → ℕ) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, (∀ j, lower j ≤ a j) ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < q0) ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (B j k) (P j k) (γ j k) r| ≤
          (1 / 2 : ℝ) ^ j := by
  choose b hb htest using fun j =>
    exists_integer_scale_variable (tests j) (B j) (P j) (γ j) (hγ j)
      (show (0 : ℝ) < (1 / 2) ^ j by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hq0
  let c : ℕ → ℕ := fun j => max (lower j) (max (b j) (n + 1))
  let a := DiagonalScale.doublingEnvelope c
  have hca : ∀ j, c j ≤ a j := DiagonalScale.doublingEnvelope_ge c
  have hba : ∀ j, b j ≤ a j := fun j =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hca j)
  have hna : ∀ j, n + 1 ≤ a j := fun j =>
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hca j)
  have hmono : StrictMono a := DiagonalScale.doublingEnvelope_strictMono c
  refine ⟨a, fun j => (le_max_left _ _).trans (hca j),
    DiagonalScale.doublingEnvelope_pos c, DiagonalScale.doublingEnvelope_growth c,
    hmono, SolenoidalDiagonal.realScales_tendsto hmono, ?_, ?_⟩
  · intro j
    apply (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
      (by exact_mod_cast hna j)).trans_lt
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  · intro j k hk r hr hra
    apply htest j k hk r hr
    exact hra.trans (one_div_le_one_div_of_le (by exact_mod_cast hb j)
      (by exact_mod_cast hba j))

section Fields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- The realization schedule and the additional normalized coefficient tests
are imposed simultaneously, for one finite heterogeneous family of fields. -/
theorem exists_finite_diagonal_cut_bounds_with_tests {U S : Set E}
    (hU : IsOpen U) (hSU : S ⊆ U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {A : ∀ i, ℕ → E → W i} (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, CutStageEstimates.RawStageBounds q (A i) g L (C i) (p i) S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ)
    {κ : Type*} (tests : ℕ → Finset κ) (B P γ : ℕ → κ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < q0) ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (A i)
        (fun j => g j / 2) (CutStageEstimates.cutLoss L) S) ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (B j k) (P j k) (γ j k) r| ≤
          (1 / 2 : ℝ) ^ j := by
  classical
  choose K hK hb using fun i =>
    CutStageEstimates.exists_cut_stage_constants hU hSU hq hpos Bq hBq
      (hA i) g L (C i) (p i) (hraw i)
  let Kall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |K i j m|
  let Pall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |CutStageEstimates.cutLog (p i) j m|
  have hKall : ∀ j m, 0 < Kall j m := by
    intro j m
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (K i j m))
    dsimp only [Kall]
    linarith
  have hKle : ∀ i j m, K i j m ≤ Kall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (K i j m))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  have hPle : ∀ i j m, CutStageEstimates.cutLog (p i) j m ≤ Pall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum
      (fun i _ => abs_nonneg (CutStageEstimates.cutLog (p i) j m)) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one))
  obtain ⟨b, hblower, hbpos, _, _, _, hbsmall⟩ :=
    DiagonalScale.exists_diagonal_scales Kall Pall g hg lower
  obtain ⟨a, hba, hapos, hadouble, hamono, hatop, haouter, hatest⟩ :=
    exists_scales_with_tests tests B P γ hγ b hq0
  refine ⟨a, hblower.trans (hba 0), hapos, hadouble, hamono, hatop, haouter, ?_, hatest⟩
  intro i j hj m hm x hx
  apply CutStageEstimates.cut_product_bound_of_threshold hU hSU hq hpos (hA i j hj) m
    (show (1 : ℝ) ≤ (a j : ℝ) by exact_mod_cast (Nat.succ_le_of_lt (hapos j))) (by positivity) (K := Kall j m) (P := Pall j m)
    (g := g j) (L := CutStageEstimates.cutLoss L m) ?_ ?_ x hx
  · intro c hc y hy hq1
    apply (hb i j hj m c hc y hy hq1).trans
    have hlog : 1 ≤ 1 + |Real.log (q y)| := le_add_of_nonneg_right (abs_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hpos y hy).le _)
    calc
      _ ≤ Kall j m * (1 + |Real.log (q y)|) ^ (CutStageEstimates.cutLog (p i) j m) :=
        mul_le_mul_of_nonneg_right (hKle i j m) (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (hPle i j m)) (hKall j m).le
  · intro r hr hra
    exact hbsmall j hj m hm r hr
      (hra.trans (one_div_le_one_div_of_le (by exact_mod_cast hbpos j)
        (show (b j : ℝ) ≤ (a j : ℝ) by exact_mod_cast hba j)))

end Fields

end NavierStokes.GenericDiagonalSchedule

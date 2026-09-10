import NavierStokes.MixedFiniteBackground

/-!
# Quantitative bounds for general diagonal realizations

The base is retained without a cutoff. The positive corrections are actual
locally finite cutoff sums. Logarithmic losses are absorbed at each fixed
stage, while the resulting power loss is independent of the stage.
-/

noncomputable section

namespace NavierStokes.GenericRealizationBounds

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The uncut base plus the actual positive cutoff series. -/
def realized (a : ℕ → ℝ) (q : E → ℝ) (base : E → V) (A : ℕ → E → V) : E → V :=
  fun x => base x + SolenoidalDiagonal.potentialSum a q
    (CutStageEstimates.positiveStages A) x

/-- The corresponding finite approximation, including exactly stages `1,…,J`. -/
def stage (base : E → V) (A : ℕ → E → V) (J : ℕ) : E → V :=
  fun x => base x + DiagonalJetBounds.uncutPrefix
    (CutStageEstimates.positiveStages A) (J + 1) x

theorem realized_smooth {U : Set E} (hU : IsOpen U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ U, 0 < q x)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {base : E → V}
    (hbase : ContDiffOn ℝ ∞ base U) {A : ℕ → E → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (realized a q base A) U :=
  hbase.add (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hpos hq
    (CutStageEstimates.positiveStages_smooth hA))

theorem stage_smooth {U : Set E} {base : E → V}
    (hbase : ContDiffOn ℝ ∞ base U) {A : ℕ → E → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (J : ℕ) :
    ContDiffOn ℝ ∞ (stage base A J) U :=
  hbase.add (ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j))

/-- A logarithmic weight costs one fixed power, regardless of its fixed exponent. -/
theorem jetRate_of_log_bound {l : Filter E} {q : E → ℝ} {f : E → V}
    (hq : ∀ᶠ x in l, 0 < q x) (hqzero : Tendsto q l (𝓝 0))
    (m : ℕ) (C P r : ℝ)
    (hb : ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤
      C * (1 + |Real.log (q x)|) ^ P * q x ^ r) :
    JetRate l q f m (r - 1) := by
  have hqright : Tendsto q l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqzero, hq⟩
  have ht := ((DiagonalScale.tendsto_logPowerWeight C P 1 zero_lt_one).comp hqright).abs
  simp only [abs_zero] at ht
  have hs : ∀ᶠ x in l, |DiagonalScale.logPowerWeight C P 1 (q x)| ≤ 1 := by
    simpa only [Function.comp_def] using (ht.eventually (gt_mem_nhds zero_lt_one)).mono
      (fun _ h => h.le)
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [hq, hb, hs] with x hx hbx hsx
  have he : r = 1 + (r - 1) := by ring
  calc
    _ ≤ C * (1 + |Real.log (q x)|) ^ P * q x ^ r := hbx
    _ ≤ |C * (1 + |Real.log (q x)|) ^ P * q x ^ r| := le_abs_self _
    _ = |DiagonalScale.logPowerWeight C P 1 (q x)| * q x ^ (r - 1) := by
      rw [show q x ^ r = q x ^ (1 : ℝ) * q x ^ (r - 1) from by calc
        q x ^ r = q x ^ (1 + (r - 1)) := congrArg (fun t : ℝ => q x ^ t) he
        _ = _ := Real.rpow_add hx _ _]
      simp only [DiagonalScale.logPowerWeight, ← mul_assoc, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hx.le (r - 1))]
    _ ≤ 1 * q x ^ (r - 1) :=
      mul_le_mul_of_nonneg_right hsx (Real.rpow_nonneg hx.le _)

theorem raw_log_jetRate {l : Filter E} {q : E → ℝ} {A : ℕ → E → V}
    {g L : ℕ → ℝ} {C P : ℕ → ℕ → ℝ} {U : Set E}
    (hraw : CutStageEstimates.RawStageBounds q A g L C P U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    JetRate l q (A j) m (g j - L m - 1) := by
  apply jetRate_of_log_bound (hq.mono (fun _ h => h.1)) hqzero m (C j m) (P j m)
  filter_upwards [hlU, hq] with x hx hqx
  exact hraw j hj m x hx hqx.2

theorem stage_growth {l : Filter E} {q : E → ℝ} {base : E → V}
    {A : ℕ → E → V} {g L Lbase : ℕ → ℝ} {C P : ℕ → ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (hqzero : Tendsto q l (𝓝 0))
    (hbase : ContDiffOn ℝ ∞ base U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hraw : CutStageEstimates.RawStageBounds q A g L C P U)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hbg : ∀ m, JetRate l q base m (-Lbase m)) (J m : ℕ) :
    JetRate l q (stage base A J) m (-max (L m + 1) (Lbase m)) := by
  have hzero : JetRate l q (CutStageEstimates.positiveStages A 0) m
      (-max (L m + 1) (Lbase m)) := by
    rw [CutStageEstimates.positiveStages_zero]
    refine ⟨0, le_rfl, Filter.Eventually.of_forall (fun x => ?_)⟩
    simp
  have hp := MixedFiniteBackground.nonemptyPrefix_jetRate hU hlU
    (CutStageEstimates.positiveStages_smooth hA) hzero (fun j hj => ?_) J
  · exact ((hbg m).weaken hq (neg_le_neg (le_max_right _ _))).add hp hU hlU hbase
      (ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j))
  · rw [CutStageEstimates.positiveStages_of_pos hj]
    apply (raw_log_jetRate hraw hlU hq hqzero hj m).weaken hq
    have hgain := hg j hj
    have hmax := le_max_left (L m + 1) (Lbase m)
    linarith

theorem realized_tail_jetRate {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {base : E → V} {A : ℕ → E → V} {g L : ℕ → ℝ}
    {U : Set E} {l : Filter E} (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    JetRate l q (fun x => realized a q base A x - stage base A J x)
      m (g (J + 1) - L m) := by
  have ht := jetRate_diagonal_tail ha hU hq
    (CutStageEstimates.positiveStages_smooth hA) hg
    (CutStageEstimates.positiveStages_cut_bounds hb) hlU hlq hqzero J m hm
  apply ht.congr_on hU hlU
  intro x hx
  simp only [realized, stage]
  abel

omit [NormedSpace ℝ E] in
/-- The entire finite prefix is on the constant plateau on the exact interval
printed in the realization lemma. -/
theorem prefix_eventually_uncut {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : E → ℝ} {x : E}
    (hq : ContinuousAt q x) (hqx : 0 < q x) {J : ℕ}
    (hsmall : q x < 1 / (2 * a J)) (A : ℕ → E → V) :
    SolenoidalDiagonal.partialPotential a q A (J + 1) =ᶠ[𝓝 x]
      DiagonalJetBounds.uncutPrefix A (J + 1) := by
  have hprod : a J * q x < 1 / 2 := by
    have := (lt_div_iff₀ (mul_pos (by norm_num) (hapos J))).mp hsmall
    nlinarith
  have hnear : ∀ᶠ y in 𝓝 x, 0 < q y ∧ a J * q y < 1 / 2 := by
    exact (hq.eventually (lt_mem_nhds hqx)).and
      ((continuousAt_const.mul hq).eventually (gt_mem_nhds hprod))
  filter_upwards [hnear] with y hy
  unfold SolenoidalDiagonal.partialPotential DiagonalJetBounds.uncutPrefix
  apply Finset.sum_congr rfl
  intro j hj
  have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hlow : 0 ≤ a j * q y := mul_nonneg (hapos j).le hy.1.le
  have hhigh : a j * q y ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (ha hjJ) hy.1.le).trans hy.2.le
  rw [SolenoidalDiagonal.cutStage,
    SmoothCutoffs.scaledCutoff_one_of_abs_le (by rwa [abs_of_nonneg hlow]), one_smul]

/-- Exact geometric tail, for each derivative, on `0 < q < 1/(2 a_J)`.
The derivative loss is independent of the truncation index. -/
theorem realized_tail_bound {a : ℕ → ℝ} (hatop : Tendsto a atTop atTop)
    (ha : Monotone a) (hapos : ∀ j, 0 < a j)
    {q : E → ℝ} {base : E → V} {A : ℕ → E → V} {g L : ℕ → ℝ}
    {U : Set E} (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    {x : E} (hx : x ∈ U) (hqx : 0 < q x) (hq1 : q x ≤ 1)
    (J m : ℕ) (hm : m ≤ J + 3) (hsmall : q x < 1 / (2 * a J)) :
    ‖iteratedFDeriv ℝ m (fun y => realized a q base A y - stage base A J y) x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (g (J + 1) - L m) := by
  have hp := prefix_eventually_uncut ha hapos
    (hq.contDiffAt (hU.mem_nhds hx)).continuousAt hqx hsmall
      (CutStageEstimates.positiveStages A)
  have heq :
      (fun y => SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A) y -
        SolenoidalDiagonal.partialPotential a q (CutStageEstimates.positiveStages A) (J + 1) y)
        =ᶠ[𝓝 x] (fun y => realized a q base A y - stage base A J y) := by
    filter_upwards [hp] with y hy
    simp only [realized, stage, hy]
    abel
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds]
  exact DiagonalJetBounds.potential_tail_jet_bound hatop hU hq
    (CutStageEstimates.positiveStages_smooth hA) hg
    (CutStageEstimates.positiveStages_cut_bounds hb) hx hqx hq1 J m hm

omit [NormedSpace ℝ E] in
/-- The added series is identically zero on an entire neighborhood of any
outer-boundary point beyond the first support. This proves compatible zero
extension without imposing regularity of the uncut representatives outside. -/
theorem correction_eventually_zero {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : E → ℝ} {x : E} (hq : ContinuousAt q x)
    (houter : 1 / a 0 < q x) (A : ℕ → E → V) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hq.eventually (lt_mem_nhds houter)] with y hy
  unfold SolenoidalDiagonal.potentialSum
  have hzero : ∀ j, SolenoidalDiagonal.cutStage a q A j y = 0 := by
    intro j
    rw [SolenoidalDiagonal.cutStage,
      SmoothCutoffs.scaledCutoff_zero_of_inv_le (hapos j), zero_smul]
    exact ((one_div_le_one_div_of_le (hapos 0) (ha (Nat.zero_le j))).trans hy.le)
  simp only [hzero, tsum_zero]

theorem correction_contDiffAt_outer {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : E → ℝ} {x : E} (hq : ContinuousAt q x)
    (houter : 1 / a 0 < q x) (A : ℕ → E → V) :
    ContDiffAt ℝ ∞ (SolenoidalDiagonal.potentialSum a q A) x :=
  contDiffAt_const.congr_of_eventuallyEq (correction_eventually_zero ha hapos hq houter A)

/-- The flat error in the finite residual hypothesis may be an arbitrary
nonnegative majorant; it need not itself be a derivative or a smooth field. -/
theorem jetRate_of_log_bound_add_flat {l : Filter E} {q : E → ℝ} {f : E → V}
    {error : E → ℝ} (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (m : ℕ) (C P r : ℝ)
    (hb : ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤
      C * (1 + |Real.log (q x)|) ^ P * q x ^ r + error x)
    (he : ∀ N : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ᶠ x in l, error x ≤ Ce * q x ^ N) : JetRate l q f m (r - 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (r - 1)
  obtain ⟨Ce, hCe, heN⟩ := he N
  have hqright : Tendsto q l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqzero, hq.mono fun _ hx => hx.1⟩
  have ht := ((DiagonalScale.tendsto_logPowerWeight C P 1 zero_lt_one).comp hqright).abs
  simp only [abs_zero] at ht
  have hs : ∀ᶠ x in l, |DiagonalScale.logPowerWeight C P 1 (q x)| ≤ 1 := by
    simpa only [Function.comp_def] using
      (ht.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ h => h.le)
  refine ⟨1 + Ce, by positivity, ?_⟩
  filter_upwards [hq, hb, heN, hs] with x hx hbx hex hsx
  have hpower : q x ^ r = q x ^ (1 : ℝ) * q x ^ (r - 1) := by
    calc
      _ = q x ^ (1 + (r - 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hx.1 _ _
  have hlog : C * (1 + |Real.log (q x)|) ^ P * q x ^ r ≤ q x ^ (r - 1) := by
    calc
      _ ≤ |C * (1 + |Real.log (q x)|) ^ P * q x ^ r| := le_abs_self _
      _ = |DiagonalScale.logPowerWeight C P 1 (q x)| * q x ^ (r - 1) := by
        rw [hpower]
        simp only [DiagonalScale.logPowerWeight, ← mul_assoc, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hx.1.le (r - 1))]
      _ ≤ 1 * q x ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hsx (Real.rpow_nonneg hx.1.le _)
      _ = _ := one_mul _
  have herr : error x ≤ Ce * q x ^ (r - 1) := by
    apply hex.trans
    rw [← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hN) hCe
  exact hbx.trans ((add_le_add hlog herr).trans_eq (by ring))

omit [NormedSpace ℝ E] in
/-- Local finiteness lets individually vanishing representative germs pass to
the sum, without assuming one neighborhood works for every stage. -/
theorem potentialSum_zero_germ {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {x : E} (hq : ContinuousAt q x) (hpos : 0 < q x)
    (A : ℕ → E → V) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hpos A
  have hz (j : ℕ) : SolenoidalDiagonal.cutStage a q A j =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hA j] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  apply hN.trans
  filter_upwards [(Filter.eventually_all_finset (Finset.range N)).2 (fun j _ => hz j)] with y hy
  exact Finset.sum_eq_zero hy

omit [NormedSpace ℝ E] in
theorem realized_zero_germ {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {x : E} (hq : ContinuousAt q x) (hpos : 0 < q x)
    {base : E → V} {A : ℕ → E → V}
    (hbase : base =ᶠ[𝓝 x] fun _ => 0)
    (hA : ∀ j, 1 ≤ j → A j =ᶠ[𝓝 x] fun _ => 0) :
    realized a q base A =ᶠ[𝓝 x] fun _ => 0 := by
  have hAp : ∀ j, CutStageEstimates.positiveStages A j =ᶠ[𝓝 x] fun _ => 0 := by
    intro j
    cases j with
    | zero => rw [CutStageEstimates.positiveStages_zero]; exact Eventually.of_forall (fun _ => rfl)
    | succ j => simpa only [CutStageEstimates.positiveStages_of_pos (Nat.succ_pos j)] using hA (j + 1) (Nat.succ_pos j)
  filter_upwards [hbase, potentialSum_zero_germ ha hq hpos _ hAp] with y hy hsy
  simp only [realized, hy, hsy, add_zero]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem stage_zero_germ {x : E} {base : E → V} {A : ℕ → E → V}
    (hbase : base =ᶠ[𝓝 x] fun _ => 0)
    (hA : ∀ j, 1 ≤ j → A j =ᶠ[𝓝 x] fun _ => 0) (J : ℕ) :
    stage base A J =ᶠ[𝓝 x] fun _ => 0 := by
  have hAp : ∀ j, CutStageEstimates.positiveStages A j =ᶠ[𝓝 x] fun _ => 0 := by
    intro j
    cases j with
    | zero => rw [CutStageEstimates.positiveStages_zero]; exact Eventually.of_forall (fun _ => rfl)
    | succ j => simpa only [CutStageEstimates.positiveStages_of_pos (Nat.succ_pos j)] using hA (j + 1) (Nat.succ_pos j)
  filter_upwards [hbase, (eventually_all_finset (Finset.range (J + 1))).mpr (fun j _ => hAp j)] with y hy hsum
  simp only [stage, DiagonalJetBounds.uncutPrefix, hy, zero_add]
  exact Finset.sum_eq_zero hsum

end NavierStokes.GenericRealizationBounds

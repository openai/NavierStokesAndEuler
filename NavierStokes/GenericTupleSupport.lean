import NavierStokes.GenericTupleRealization
import NavierStokes.GenericFactorSupport

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericSolenoidalRealization GenericDifferentialPolynomial
open GenericRealizationBounds GenericRealization SolenoidalDiagonal
open scoped Topology ContDiff BigOperators

def baseComponents {κ : Type*} (u0 : VelocityField) (s0 : κ → PressureField) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => u0 w i
  | .inr k => s0 k

def incrementComponents {κ : Type*} (A B : ℕ → VelocityField)
    (R : κ → ℕ → PressureField) (j : ℕ) : Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j) w +
      CutStageEstimates.positiveStages B j w) i
  | .inr k => CutStageEstimates.positiveStages (R k) j

def cutIncrementComponents {κ : Type*} (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) (j : ℕ) : Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j) w +
      cutStage a q (CutStageEstimates.positiveStages B) j w) i
  | .inr k => cutStage a q (CutStageEstimates.positiveStages (R k)) j

theorem smooth_baseComponents {κ : Type*} {U : Set SpaceTime}
    {u0 : VelocityField} {s0 : κ → PressureField}
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U) :
    ∀ i, ContDiffOn ℝ ∞ (baseComponents u0 s0 i) U := by
  intro i
  cases i with
  | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn hu0
  | inr k => exact hs0 k

theorem smooth_incrementComponents {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U) :
    ∀ j i, ContDiffOn ℝ ∞ (incrementComponents A B R j i) U := by
  intro j i
  have ha := CutStageEstimates.positiveStages_smooth hA j
  have hb := CutStageEstimates.positiveStages_smooth hB j
  cases i with
  | inl i =>
      have hcurl : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j)) U :=
        fun w hw => (SpatialCurl.contDiffAt_spatialCurl (ha.contDiffAt (hU.mem_nhds hw)) (by simp)).contDiffWithinAt
      exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hcurl.add hb)
  | inr k => exact CutStageEstimates.positiveStages_smooth (hR k) j

theorem smooth_cutIncrementComponents {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {a : ℕ → ℝ} {q : SpaceTime → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U) :
    ∀ j i, ContDiffOn ℝ ∞ (cutIncrementComponents a q A B R j i) U := by
  have hs {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      {F : ℕ → SpaceTime → W} (hF : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (F j) U) (j : ℕ) :
      ContDiffOn ℝ ∞ (cutStage a q (CutStageEstimates.positiveStages F) j) U := by
    intro w hw
    exact (cutStage_contDiffAt (hq.contDiffAt (hU.mem_nhds hw))
      (fun k => (CutStageEstimates.positiveStages_smooth hF k).contDiffAt (hU.mem_nhds hw)) j).contDiffWithinAt
  intro j i
  cases i with
  | inl i =>
      have hcurl : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j)) U :=
        fun w hw => (SpatialCurl.contDiffAt_spatialCurl ((hs hA j).contDiffAt (hU.mem_nhds hw)) (by simp)).contDiffWithinAt
      exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hcurl.add (hs hB j))
  | inr k => exact hs (hR k) j

private theorem spatialCurl_sum_on {U : Set SpaceTime} (hU : IsOpen U)
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (N : ℕ) {w : SpaceTime} (hw : w ∈ U) :
    SpatialCurl.spatialCurl (fun y => ∑ j ∈ Finset.range N, A j y) w =
      ∑ j ∈ Finset.range N, SpatialCurl.spatialCurl (A j) w := by
  have hd : ∀ j ∈ Finset.range N, DifferentiableAt ℝ (fun x : Space => A j (w.1, x)) w.2 := by
    intro j _
    exact (((hA j).contDiffAt (hU.mem_nhds hw)).comp w.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  simpa only [SpatialCurl.spatialCurl, SpatialCurl.curl, map_sum] using
    congrArg SpatialCurl.curlLinear (fderiv_fun_sum hd)

/-- The finite stages are the base plus precisely the uncut physical
increments, including the curl of each potential. -/
theorem stageComponents_local_sum {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (J : ℕ) {x : SpaceTime} (hx : x ∈ U) :
    ∃ N, ∀ i, stageComponents u0 s0 A B R J i =ᶠ[𝓝 x]
      (fun y => baseComponents u0 s0 i y + ∑ j ∈ Finset.range N, incrementComponents A B R j i y) := by
  refine ⟨J + 1, ?_⟩
  intro i
  filter_upwards [hU.mem_nhds hx] with y hy
  cases i with
  | inl i =>
      have hc := spatialCurl_sum_on hU (CutStageEstimates.positiveStages_smooth hA) (J + 1) hy
      have hv : positiveStage u0 A B J y = u0 y + ∑ j ∈ Finset.range (J + 1),
          (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j) y + CutStageEstimates.positiveStages B j y) := by
        dsimp only [positiveStage, MixedDiagonalResidual.uncutVelocity, DiagonalJetBounds.uncutPrefix]
        change u0 y + (SpatialCurl.spatialCurl (fun z => ∑ j ∈ Finset.range (J + 1),
          CutStageEstimates.positiveStages A j z) y + _) = _
        rw [hc, Finset.sum_add_distrib]
      simpa only [stageComponents, baseComponents, incrementComponents, map_add, map_sum,
        EuclideanSpace.proj, PiLp.proj_apply, PiLp.add_apply] using
        congrArg (EuclideanSpace.proj i) hv
  | inr k => rfl

/-- A single local prefix works simultaneously for all physical components.
It is chosen from the scale alone, before taking any derivatives. -/
theorem components_local_sum {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {x : SpaceTime} (hx : x ∈ U) :
    ∃ N, ∀ i, components a q u0 s0 A B R i =ᶠ[𝓝 x]
      (fun y => baseComponents u0 s0 i y + ∑ j ∈ Finset.range N, cutIncrementComponents a q A B R j i y) := by
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha (hpos x hx)
  have hz : ∀ᶠ y in 𝓝 x, ∀ j, N ≤ j → SmoothCutoffs.scaledCutoff (a j) (q y) = 0 := by
    filter_upwards [(hq.contDiffAt (hU.mem_nhds hx)).continuousAt
      (lt_mem_nhds (half_lt_self (hpos x hx)))] with y hy
    exact fun j hj => hN j hj (q y) hy
  have hp {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : ℕ → SpaceTime → W) :
      potentialSum a q F =ᶠ[𝓝 x] partialPotential a q F N := by
    filter_upwards [hz] with y hy
    apply tsum_eq_sum
    intro j hj
    simp only [cutStage, hy j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)), zero_smul]
  have hc := spatialCurl_eventuallyEq (hp (CutStageEstimates.positiveStages A))
  refine ⟨N, ?_⟩
  intro i
  cases i with
  | inl i =>
      filter_upwards [hc, hp (CutStageEstimates.positiveStages B), hU.mem_nhds hx] with y hcy hby hy
      have hv : positiveVelocity a q u0 A B y = u0 y + ∑ j ∈ Finset.range N,
          (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j) y +
            cutStage a q (CutStageEstimates.positiveStages B) j y) := by
        dsimp only [positiveVelocity, velocity, velocitySum]
        rw [hcy, spatialCurl_partialPotential (hq.contDiffAt (hU.mem_nhds hy))
          (fun j => (CutStageEstimates.positiveStages_smooth hA j).contDiffAt (hU.mem_nhds hy)), hby]
        simp only [partialPotential, Finset.sum_add_distrib]
        abel
      simpa only [components, baseComponents, cutIncrementComponents, map_add, map_sum,
        EuclideanSpace.proj, PiLp.proj_apply, PiLp.add_apply] using
        congrArg (EuclideanSpace.proj i) hv
  | inr k =>
      filter_upwards [hp (CutStageEstimates.positiveStages (R k))] with y hy
      exact congrArg (fun z => s0 k y + z) hy

/-- The paper's primitive common-support assumptions suffice: each
differentiated factor is supported there in the base and in each raw and cut
increment. Support of the final sum is proved, not assumed. -/
theorem Result.flat_residual_of_factor_support {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U) (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, DiagonalResidual.JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, DiagonalResidual.JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  apply H.flat_residual hU hq hu0 hs0 hA hB hR hgtop P hconst hc region Lc hcg
    _ _ rho hrho Lres hres m N
  · intro t ht x hx hxs
    exact (hcutsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_cutIncrementComponents hU hqs hA hB hR)
      (components_local_sum hU H.tends hqs (fun w hw => (hq w hw).1) hA hx)
  · intro t ht J x hx hxs
    exact (hrawsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_incrementComponents hU hA hB hR) (stageComponents_local_sum hU hA J hx)

end NavierStokes.GenericTupleRealization

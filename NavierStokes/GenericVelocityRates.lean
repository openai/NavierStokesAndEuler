import NavierStokes.GenericSolenoidalRealization

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rate_linear {l : Filter D} {q : D → ℝ} {U : Set D} {f : D → V}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (L : V →L[ℝ] W) {m : ℕ} {r : ℝ} (hr : JetRate l q f m r) :
    JetRate l q (fun x => L (f x)) m r := by
  obtain ⟨C, hC, hb⟩ := hr
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg L) hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  exact (ResidualStability.norm_jet_linear_map L hU hf hx m).trans
    ((mul_le_mul_of_nonneg_left hbx (norm_nonneg L)).trans_eq (mul_assoc _ _ _).symm)

end NavierStokes.GenericDifferentialPolynomial

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement DiagonalResidual GenericRealizationBounds GenericDifferentialPolynomial
open scoped Topology ContDiff BigOperators

def positiveStage (u0 : VelocityField) (A B : ℕ → VelocityField) (J : ℕ) : VelocityField :=
  fun w => u0 w + MixedDiagonalResidual.uncutVelocity
    (CutStageEstimates.positiveStages A) (CutStageEstimates.positiveStages B) J w

theorem positiveStage_smooth {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hu0 : ContDiffOn ℝ ∞ u0 U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U) (J : ℕ) :
    ContDiffOn ℝ ∞ (positiveStage u0 A B J) U :=
  hu0.add (MixedDiagonalResidual.uncutVelocity_smooth hU
    (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB) J)

/-- The scalar components of the literal solenoidal velocity have the
approximation data needed by every finite differential polynomial. The curl
costs one derivative; the power loss is independent of the truncation. -/
def velocity_component_approximation {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    {l : Filter SpaceTime} (hU : IsOpen U) (hlU : ∀ᶠ w in l, w ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hlq : ∀ᶠ w in l, 0 < q w ∧ q w ≤ 1) (hqzero : Tendsto q l (𝓝 0))
    (hu0 : ContDiffOn ℝ ∞ u0 U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (g gain LA LB LAc LBc K0 : ℕ → ℝ)
    (CA PA CB PB : ℕ → ℕ → ℝ)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA PA U)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB PB U)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j) (hgain : Monotone gain)
    (hbase : ∀ m, JetRate l q u0 m (-K0 m))
    (hcutA : DiagonalJetBounds.CutStageBounds a q A gain LAc U)
    (hcutB : DiagonalJetBounds.CutStageBounds a q B gain LBc U) (i : Fin 3) :
    ApproximationRates l q (fun J => gain (J + 1))
      (fun w => positiveVelocity a q u0 A B w i)
      (fun J w => positiveStage u0 A B J w i) := by
  let loss : ℕ → ℝ := fun m => max (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))
  have hprefixA : ∀ J, ContDiffOn ℝ ∞
      (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1)) U :=
    fun J => ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j)
  have hprefixB : ∀ J, ContDiffOn ℝ ∞
      (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages B) (J + 1)) U :=
    fun J => ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hB j)
  have hstage := positiveStage_smooth hU hu0 hA hB
  have hvel : ContDiffOn ℝ ∞ (positiveVelocity a q u0 A B) U :=
    velocity_smooth ha hU hq hpos hu0 (CutStageEstimates.positiveStages_smooth hA)
      (CutStageEstimates.positiveStages_smooth hB)
  have hgrowth : ∀ J m, JetRate l q (positiveStage u0 A B J) m (-loss m) := by
    intro J m
    have hz : ∀ k, JetRate l q (fun _ : SpaceTime => (0 : Space)) k (-(0 : ℝ)) := by
      intro k
      exact ⟨0, le_rfl, Eventually.of_forall (fun _ => by simp)⟩
    have hAr := stage_growth hU hlU hlq hqzero contDiffOn_const hA hrawA hg hz J (m + 1)
    have hAr' : JetRate l q
        (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1)) (m + 1)
          (-max (LA (m + 1) + 1) 0) := by
      have heq : GenericRealizationBounds.stage (fun _ : SpaceTime => (0 : Space)) A J =
          DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1) := by
        funext x
        simp only [GenericRealizationBounds.stage, zero_add]
      rw [heq] at hAr
      exact hAr
    have hCr := (hAr'.spatialCurl hU hlU (hprefixA J)).weaken hlq
      (neg_le_neg (le_max_left (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))))
    have hBr := (stage_growth hU hlU hlq hqzero hu0 hB hrawB hg hbase J m).weaken hlq
      (neg_le_neg (le_max_right (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))))
    have hCs : ContDiffOn ℝ ∞
        (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix
          (CutStageEstimates.positiveStages A) (J + 1))) U :=
      fun x hx => (SpatialCurl.contDiffAt_spatialCurl
        ((hprefixA J).contDiffAt (hU.mem_nhds hx)) (by simp)).contDiffWithinAt
    exact (hCr.add hBr hU hlU hCs (hu0.add (hprefixB J))).congr_on hU hlU
      (fun x _ => by dsimp [positiveStage, MixedDiagonalResidual.uncutVelocity, stage]; abel)
  refine ⟨loss, MixedDiagonalResidual.velocityLoss LAc LBc, id, ?_, ?_⟩
  · intro J m
    exact rate_linear hU hlU (hstage J) (EuclideanSpace.proj i) (hgrowth J m)
  · intro m J hJ
    change m ≤ J at hJ
    have ht := MixedDiagonalResidual.velocity_tail_jetRate ha hU hpos hq
      (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB)
      hgain (CutStageEstimates.positiveStages_cut_bounds hcutA)
      (CutStageEstimates.positiveStages_cut_bounds hcutB) hlU hlq hqzero J m (by omega)
    have ht' : JetRate l q (fun w => positiveVelocity a q u0 A B w - positiveStage u0 A B J w) m
        (gain (J + 1) - MixedDiagonalResidual.velocityLoss LAc LBc m) :=
      ht.congr_on hU hlU (fun x _ => by
        dsimp [positiveVelocity, velocity, positiveStage, MixedDiagonalResidual.velocity]
        abel)
    exact (rate_linear hU hlU (hvel.sub (hstage J)) (EuclideanSpace.proj i) ht').congr_on hU hlU
      (fun x _ => by simp only [map_sub]; rfl)

/-- Exact geometric velocity tail. The fixed curl norm is absorbed by one
additional power of the small scale, uniformly in the truncation index. -/
theorem positiveVelocity_tail_bound {a : ℕ → ℝ} (hatop : Tendsto a atTop atTop)
    (hamono : Monotone a) (hapos : ∀ j, 0 < a j)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    {gain LA LB : ℕ → ℝ} (hg : Monotone gain)
    (hcutA : DiagonalJetBounds.CutStageBounds a q A gain LA U)
    (hcutB : DiagonalJetBounds.CutStageBounds a q B gain LB U)
    (hfirst : ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1 ≤ 2 * a 0)
    {x : SpaceTime} (hx : x ∈ U) (hqx1 : q x ≤ 1)
    (J m : ℕ) (hm : m ≤ J + 2) (hsmall : q x < 1 / (2 * a J)) :
    ‖iteratedFDeriv ℝ m (fun y => positiveVelocity a q u0 A B y - positiveStage u0 A B J y) x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - (max (LA (m + 1)) (LB m) + 1)) := by
  let As := CutStageEstimates.positiveStages A
  let Bs := CutStageEstimates.positiveStages B
  let tailA := fun y => SolenoidalDiagonal.potentialSum a q As y - DiagonalJetBounds.uncutPrefix As (J + 1) y
  let tailB := fun y => SolenoidalDiagonal.potentialSum a q Bs y - DiagonalJetBounds.uncutPrefix Bs (J + 1) y
  have hAs := CutStageEstimates.positiveStages_smooth hA
  have hBs := CutStageEstimates.positiveStages_smooth hB
  have hsumA := SolenoidalDiagonal.potentialSum_contDiffOn hatop hU hpos hq hAs
  have hsumB := SolenoidalDiagonal.potentialSum_contDiffOn hatop hU hpos hq hBs
  have hpA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix As (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hAs j)
  have hpB : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix Bs (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hBs j)
  have htA : ContDiffOn ℝ ∞ tailA U := hsumA.sub hpA
  have htB : ContDiffOn ℝ ∞ tailB U := hsumB.sub hpB
  have htAc : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl tailA) U :=
    fun y hy => (SpatialCurl.contDiffAt_spatialCurl (htA.contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
  have heq : EqOn (fun y => SpatialCurl.spatialCurl tailA y + tailB y)
      (fun y => positiveVelocity a q u0 A B y - positiveStage u0 A B J y) U := by
    intro y hy
    change SpatialCurl.spatialCurl (fun z => SolenoidalDiagonal.potentialSum a q As z -
      DiagonalJetBounds.uncutPrefix As (J + 1) z) y + tailB y = _
    rw [spatialCurl_sub_on hU hsumA hpA hy]
    dsimp [tailB, positiveVelocity, velocity, positiveStage, MixedDiagonalResidual.uncutVelocity,
      SolenoidalDiagonal.velocitySum]
    dsimp only [As, Bs]
    abel
  have hAt := realized_tail_bound (base := fun _ : SpaceTime => (0 : Space)) hatop hamono hapos
    hU hq hA hg hcutA hx (hpos x hx) hqx1 J (m + 1) (by omega) hsmall
  have hBt := realized_tail_bound (base := fun _ : SpaceTime => (0 : Space)) hatop hamono hapos
    hU hq hB hg hcutB hx (hpos x hx) hqx1 J m (by omega) hsmall
  have hAt' : ‖iteratedFDeriv ℝ (m + 1) tailA x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - LA (m + 1)) := by
    have he : (fun y => realized a q (fun _ : SpaceTime => (0 : Space)) A y -
        stage (fun _ : SpaceTime => (0 : Space)) A J y) = tailA := by
      funext y
      simp only [realized, stage, tailA, As, zero_add]
    rw [he] at hAt
    exact hAt
  have hBt' : ‖iteratedFDeriv ℝ m tailB x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - LB m) := by
    have he : (fun y => realized a q (fun _ : SpaceTime => (0 : Space)) B y -
        stage (fun _ : SpaceTime => (0 : Space)) B J y) = tailB := by
      funext y
      simp only [realized, stage, tailB, Bs, zero_add]
    rw [he] at hBt
    exact hBt
  let K : ℝ := ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖
  let r : ℝ := gain (J + 1) - max (LA (m + 1)) (LB m)
  have hK : 0 ≤ K := norm_nonneg
    (SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space))
  have hpa : q x ^ (gain (J + 1) - LA (m + 1)) ≤ q x ^ r :=
    Real.rpow_le_rpow_of_exponent_ge (hpos x hx) hqx1
      (sub_le_sub_left (le_max_left _ _) _)
  have hpb : q x ^ (gain (J + 1) - LB m) ≤ q x ^ r :=
    Real.rpow_le_rpow_of_exponent_ge (hpos x hx) hqx1
      (sub_le_sub_left (le_max_right _ _) _)
  have hKq : (K + 1) * q x ≤ 1 := by
    have hqmul := (lt_div_iff₀ (mul_pos (by norm_num) (hapos J))).mp hsmall
    have hle : K + 1 ≤ 2 * a J := hfirst.trans (mul_le_mul_of_nonneg_left (hamono (Nat.zero_le J)) (by norm_num))
    have := mul_le_mul_of_nonneg_right hle (hpos x hx).le
    nlinarith
  have hpowEq : q x ^ r = q x * q x ^ (r - 1) := by
    calc
      _ = q x ^ (1 + (r - 1)) := by congr 1; ring
      _ = q x ^ (1 : ℝ) * q x ^ (r - 1) := Real.rpow_add (hpos x hx) _ _
      _ = _ := by rw [Real.rpow_one]
  have hpower : (K + 1) * q x ^ r ≤ q x ^ (r - 1) := by
    calc
      _ = ((K + 1) * q x) * q x ^ (r - 1) := by rw [hpowEq]; ring
      _ ≤ 1 * q x ^ (r - 1) := mul_le_mul_of_nonneg_right hKq (Real.rpow_nonneg (hpos x hx).le _)
      _ = _ := one_mul _
  rw [← ResidualStability.iteratedFDeriv_eqOn hU heq m hx]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl tailA) x‖ + ‖iteratedFDeriv ℝ m tailB x‖ :=
      ResidualStability.norm_jet_add_le hU htAc htB hx m
    _ ≤ K * ((1 / 2 : ℝ) ^ J * q x ^ r) + (1 / 2 : ℝ) ^ J * q x ^ r := by
      apply add_le_add
      · exact (ResidualStability.norm_iteratedFDeriv_spatialCurl_le hU htA hx m).trans
          (mul_le_mul_of_nonneg_left (hAt'.trans (mul_le_mul_of_nonneg_left hpa (by positivity))) hK)
      · exact hBt'.trans (mul_le_mul_of_nonneg_left hpb (by positivity))
    _ = (1 / 2 : ℝ) ^ J * ((K + 1) * q x ^ r) := by ring
    _ ≤ (1 / 2 : ℝ) ^ J * q x ^ (r - 1) := mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by dsimp only [r]; congr 2; ring

end NavierStokes.GenericSolenoidalRealization

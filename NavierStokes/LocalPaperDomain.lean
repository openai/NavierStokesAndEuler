import NavierStokes.LocalAngularGrowth

/-! # A common local domain for the paper's heat-exterior formula -/

noncomputable section

namespace NavierStokes.LocalPaperDomain

open Set Filter ProblemStatement CorrectionInitialization
open scoped Topology

def residualBand : ℕ :=
  ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold

def qstar (a : ℕ → ℕ) : ℝ :=
  min (ChartScales.Q residualBand) ((1 / 2) / (|(a 0 : ℝ)| + 1))

def innerEdge : ℝ := NominalConeAssembly.activeLeft ActualPrimary.nominal

def outerEdge : ℝ :=
  max innerEdge (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
    (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)) + 1

def radius (w : SpaceTime) : ℝ :=
  AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ ActualPrimary.h w

theorem radius_eq_chart (w : SpaceTime) :
    radius w = (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 := rfl

theorem qstar_pos (a : ℕ → ℕ) : 0 < qstar a :=
  lt_min (ChartScales.Q_pos _) (div_pos (by norm_num) (by positivity))

theorem innerEdge_pos : 0 < innerEdge := NominalConeAssembly.activeLeft_pos _

theorem innerEdge_lt_outerEdge : innerEdge < outerEdge := by
  have := le_max_left innerEdge
    (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
  dsimp only [outerEdge]
  linarith

theorem exterior_conditions {a : ℕ → ℕ} {w : SpaceTime} (ht : w.1 < 1)
    (hq : PhysicalWaveSum.physicalQ ActualPrimary.h w < qstar a)
    (hX : outerEdge ≤ radius w) :
    w ∈ ActualExteriorPrefix.exteriorDomain residualBand ∧
      w ∈ BaseExterior.cartesianExterior ActualPrimary.h
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal) ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2 := by
  have hright : NominalConeAssembly.activeRight ActualPrimary.nominal < radius w := by
    have h1 := le_max_left (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)
    have h2 := le_max_right innerEdge
      (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    dsimp only [outerEdge] at hX
    linarith
  have hext : BaseExterior.nominalExteriorRadius ActualPrimary.nominal < radius w := by
    have h1 := le_max_right (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)
    have h2 := le_max_right innerEdge
      (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    dsimp only [outerEdge] at hX
    linarith
  refine ⟨ActualExteriorPrefix.mem_exteriorDomain.mpr ⟨ht,
    hq.trans_le (min_le_left _ _), ?_⟩, ⟨ht, hext⟩, ?_⟩
  · intro ha
    exact (not_le_of_gt hright) ha.2
  · have hpos := PhysicalWaveSum.physicalQ_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half ht
    have hδ := (lt_div_iff₀ (show 0 < |(a 0 : ℝ)| + 1 by positivity)).mp
      (hq.trans_le (min_le_right _ _))
    rw [abs_mul, abs_of_pos hpos]
    nlinarith

/-- The three strict exterior conditions persist on a neighborhood. -/
theorem exterior_conditions_eventually {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain residualBand)
    (he : w ∈ BaseExterior.cartesianExterior ActualPrimary.h
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    (hc : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    ∀ᶠ z in 𝓝 w,
      z ∈ ActualExteriorPrefix.exteriorDomain residualBand ∧
      z ∈ BaseExterior.cartesianExterior ActualPrimary.h
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal) ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h z| < 1 / 2 := by
  have hq := (PhysicalWaveSum.physicalQ_smoothAt ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half he.1).continuousAt
  filter_upwards [(ActualExteriorPrefix.exteriorDomain_open residualBand).mem_nhds hw,
    (BaseExterior.cartesianExterior_isOpen ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half _).mem_nhds he,
    ((hq.const_mul (a 0 : ℝ)).abs).eventually_lt_const hc] with z hz hez hcz
  exact ⟨hz, hez, hcz⟩

end NavierStokes.LocalPaperDomain

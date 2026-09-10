import NavierStokes.WholeDomainHeatGeometry

/-! # Uniform heat jets on the normalized compact annulus -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum WholeDomainStageBounds

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def positiveRadius : Set SpaceTime := {w | 0 < AxisymmetricFields.radialEnergy w.2}

theorem positiveRadius_open : IsOpen positiveRadius :=
  isOpen_lt continuous_const
    ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)

theorem closedHeat_mem_nhds {w : SpaceTime} (ht : w.1 < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.closedCartesianHeatDomain ∈ 𝓝 w := by
  have hU : IsOpen {y : SpaceTime | y.1 < 1 ∧ 0 < AxisymmetricFields.radialEnergy y.2} :=
    (isOpen_lt continuous_fst continuous_const).inter positiveRadius_open
  exact Filter.mem_of_superset (hU.mem_nhds ⟨ht,hs⟩) (fun _ hy => ⟨hy.1.le,hy.2⟩)

theorem heat_smoothAt {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {w : SpaceTime} (ht : w.1 < 1) (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    ContDiffAt ℝ ∞ f w := hf.contDiffAt (closedHeat_mem_nhds ht hs)

variable [CompleteSpace V]

theorem normalized_local_rate {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {R : ℝ} (hR : 0 < R) (m : ℕ) {w : SpaceTime} (hw : w ∈ normalizedAnnulus R) :
    DiagonalResidual.JetRate (𝓝[normalizedAnnulus R ∩ preterminal] w)
      (fun _ => (1 : ℝ)) f m 0 := by
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := hR.trans_le hw.2.2.1
  by_cases ht : w.1 < 1
  · have hc : ContDiffAt ℝ 0 (iteratedFDeriv ℝ m f) w :=
      (heat_smoothAt hf ht hs).iteratedFDeriv_right
        (by exact_mod_cast (le_top : 0 + (m : ℕ∞) ≤ ⊤))
    exact rate_of_jet_limit (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds zero_lt_one 0
  · have ht1 : w.1 = 1 := le_antisymm hw.1.2 (le_of_not_gt ht)
    obtain ⟨U⟩ := SlowBaseEndpoint.oneSidedExtension_of_closed_local
      (f := f) (g := f) positiveRadius_open
      (show (1,w.2) ∈ positiveRadius by simpa [positiveRadius] using hs)
      (hf.mono (fun y hy => ⟨hy.2.1,hy.1⟩)) (fun _ _ => rfl)
    have hmono : 𝓝[normalizedAnnulus R ∩ preterminal] (1,w.2) ≤
        𝓝[SpacetimeEndpoint.openPast 1] (1,w.2) :=
      nhdsWithin_mono _ (fun _ hy => ⟨hy.2,mem_univ _⟩)
    have hew : w = (1,w.2) := Prod.ext ht1 rfl
    rw [hew]
    exact rate_of_jet_limit ((U.jet_tendsto m).mono_left hmono)
      tendsto_const_nhds zero_lt_one 0

theorem normalized_jet_bound {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ normalizedAnnulus R, w.1 < 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := compact_bound_of_local_rates
    (S := normalizedAnnulus R ∩ preterminal) (normalizedAnnulus_compact R)
    (fun _ _ => zero_lt_one) (fun _ hw => normalized_local_rate hf hR m hw)
  refine ⟨C,hC,fun w hw ht => ?_⟩
  simpa only [Real.rpow_zero,mul_one] using hb w ⟨hw,hw,ht⟩

end NavierStokes.WholeDomainHeatBounds

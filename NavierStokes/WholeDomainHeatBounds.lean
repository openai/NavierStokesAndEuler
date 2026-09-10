import NavierStokes.WholeDomainHeatScaling
import NavierStokes.WholeDomainHeatCompact

/-! # Whole-domain jet bounds for the actual exterior heat fields

The parabolic normalization uses the larger of the similarity scale and
physical radial energy. Its image lies in one compact annulus, even when
the original radial coordinate is unbounded.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum

def heatLoss (m : ℕ) : ℝ := 2*((m : ℝ)+1)

theorem heatLoss_nonneg (m : ℕ) : 0 ≤ heatLoss m := by unfold heatLoss; positivity

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem homogeneous_heat_bound {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {b : ℝ} (hb : -2 ≤ b ∧ b ≤ 0)
    (hscale : ∀ (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime),
      0 < AxisymmetricFields.radialEnergy w.2 →
        f w = a ^ b • f (rescale a ha z w))
    {h R : ℝ} (hh : 0 < h) (hh1 : h < 1/2) (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-heatLoss m) := by
  obtain ⟨C,hC,hCb⟩ := normalized_jet_bound hf (lt_min hR zero_lt_one) m
  refine ⟨C,hC,?_⟩
  intro w hw hq1 hX
  let q := physicalQ h w
  have hq : 0 < q := physicalQ_pos hh hh1 hw
  let a := max q (AxisymmetricFields.radialEnergy w.2)
  have ha : 0 < a := hq.trans_le (le_max_left _ _)
  have hqa : q ≤ a := le_max_left _ _
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := by
    change R < AxisymmetricFields.radialEnergy w.2 / q at hX
    exact (mul_pos hR hq).trans ((lt_div_iff₀ hq).mp hX)
  have hT := normalize_mem_annulus hh hh1 hR hw hX
  change rescale a ha (w.2 2) w ∈ normalizedAnnulus (min R 1) at hT
  have htp := rescale_past a ha (w.2 2) hw
  have hts : 0 < AxisymmetricFields.radialEnergy (rescale a ha (w.2 2) w).2 := by
    rw [rescale_radialEnergy]
    exact div_pos hs ha
  have hcomp : ContDiffAt ℝ ∞ (fun y => f (rescale a ha (w.2 2) y)) w :=
    (heat_smoothAt hf htp hts).comp w
      (((parabolicLinear a ha).contDiff.contDiffAt).add contDiffAt_const)
  have he : f =ᶠ[𝓝 w] (fun y => a^b • f (rescale a ha (w.2 2) y)) :=
    Filter.eventuallyEq_of_mem (positiveRadius_open.mem_nhds hs)
      (fun y hy => hscale a ha (w.2 2) y hy)
  rw [iteratedFDeriv_eq_of_eventuallyEq he m,
    iteratedFDeriv_const_smul_apply' (hcomp.of_le (nat_le_infty m)), norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg ha.le b)]
  have hL := parabolicLinear_norm_le ha hq hqa hq1
  have hj : ‖iteratedFDeriv ℝ m (fun y => f (rescale a ha (w.2 2) y)) w‖ ≤
      C * (q⁻¹)^m := by
    exact (norm_iteratedFDeriv_affine_le (parabolicLinear a ha) (rescaleOffset a (w.2 2))
      f w m).trans (mul_le_mul (hCb _ hT htp)
        (pow_le_pow_left₀ (norm_nonneg _) hL m) (pow_nonneg (norm_nonneg _) m) hC)
  have hab : a^b ≤ q^b := Real.rpow_le_rpow_of_nonpos hq hqa hb.2
  calc
    a^b * ‖iteratedFDeriv ℝ m (fun y => f (rescale a ha (w.2 2) y)) w‖ ≤
        q^b * (C*(q⁻¹)^m) :=
      mul_le_mul hab hj (norm_nonneg _) (Real.rpow_nonneg hq.le b)
    _ = C*q^(b-(m : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul_natCast hq.le]
      rw [show (-1 : ℝ)*(m : ℝ) = -(m : ℝ) by ring]
      rw [show q^b * (C*q^(-(m : ℝ))) = C*(q^b*q^(-(m : ℝ))) by ring,
        ← Real.rpow_add hq]
      congr 2
    _ ≤ C*q^(-heatLoss m) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
        unfold heatLoss
        have hm : 0 ≤ (m : ℝ) := by positivity
        linarith [hb.1])) hC

/-- Every actual heat-velocity jet is uniformly bounded on the entire
exterior region of the unit similarity sublevel. -/
theorem heat_velocity_bound (C : ℝ) {h R : ℝ}
    (hh : 0 < h) (hh1 : h < 1/2) (hR : 0 < R) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m (BaseExterior.heatVelocity C h) w‖ ≤
        K * physicalQ h w ^ (-heatLoss m) :=
  homogeneous_heat_bound (BaseExterior.heatVelocity_contDiffOn_closed C hh)
    (by unfold RadialHeatProfile.spatialExponent; constructor <;> linarith)
    (fun a ha z _ hs => heatVelocity_rescale C h a ha z hs) hh hh1 hR m

/-- The canonical improper-integral pressure satisfies the same global
fixed-order bound; no bound on the radial coordinate is imposed. -/
theorem heat_pressure_bound (C : ℝ) {h R : ℝ}
    (hh : 0 < h) (hh1 : h < 1/2) (hR : 0 < R) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m (BaseExterior.heatPressureField C h) w‖ ≤
        K * physicalQ h w ^ (-heatLoss m) := by
  exact homogeneous_heat_bound (BaseExterior.heatPressureField_contDiffOn_closed C hh)
    (by unfold TerminalPressure.amplitudeExponent; constructor <;> linarith)
    (fun a ha z _ hs => heatPressure_rescale C h a ha z hs) hh hh1 hR m

end NavierStokes.WholeDomainHeatBounds

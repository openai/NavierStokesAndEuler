import NavierStokes.R3.CompactEnergy
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spatial Cauchy--Schwarz for the force work

The integrals use ordinary Euclidean volume. Square integrability supplies
the two finite L² norms appearing in the bound.
-/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement

/-- Cauchy--Schwarz bounds the force work by the product of the ordinary
spatial L² norms. The force only needs finite L² norm and continuity. -/
theorem work_le_sqrt_l2Sq {u f : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hf_sq : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2)) :
    (∫ x : Space, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
      Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) := by
  have huLp : MemLp (fun x : Space => u (t, x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
      (integrable_norm_sq hu hcu)
  have hfLp : MemLp (fun x : Space => f (t, x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hf_sq
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using huLp) (by simpa using hfLp)
  have hprod : Integrable (fun x : Space => ‖u (t, x)‖ * ‖f (t, x)‖) :=
    huLp.norm.integrable_mul hfLp.norm
  calc
    (∫ x : Space, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
        ∫ x : Space, ‖u (t, x)‖ * ‖f (t, x)‖ :=
      integral_mono (integrable_inner_left hu hf hcu) hprod
        (fun x => real_inner_le_norm _ _)
    _ ≤ Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) := by
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, l2Sq] using hholder

end NavierStokesR3.CompactEnergy

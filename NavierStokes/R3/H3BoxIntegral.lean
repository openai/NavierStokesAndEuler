import NavierStokes.R3.H3Definitions
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

private def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

private instance : IsFiniteMeasure unitMeasure := by
  unfold unitMeasure
  infer_instance

private theorem unitPi_eq (n : ℕ) :
    Measure.pi (fun _ : Fin n => unitMeasure) = volume.restrict (Icc 0 1) := by
  unfold unitMeasure
  rw [← Measure.restrict_pi_pi]
  congr 1
  ext x
  simp [Set.mem_Icc, Pi.le_def]

private theorem integrable_unitPi {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : Continuous g) : Integrable g (Measure.pi (fun _ : Fin n => unitMeasure)) := by
  rw [unitPi_eq]
  exact hg.integrableOn_Icc

/-- The iterated coordinate integral used by the elementary FTC proof is
exactly the ordinary product-volume integral on the cube. -/
theorem boxIntegral_eq_cubeIntegral {h : Space → ℝ} (hh : Continuous h) :
    NavierStokes.PeriodicSobolev.boxIntegral h = cubeIntegral h := by
  have hi := integrable_unitPi (hh.comp toSpace.continuous)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => unitMeasure) 0).symm
  have hei : Integrable (fun z : ℝ × (Fin 2 → ℝ) => h (toSpace (e.symm z)))
      (unitMeasure.prod (Measure.pi (fun _ : Fin 2 => unitMeasure))) := by
    exact (he.integrable_comp_emb e.symm.measurableEmbedding).2 hi
  have h2 (a : ℝ) : Integrable (fun y : Fin 2 → ℝ => h (toSpace (Fin.cons a y)))
      (Measure.pi (fun _ : Fin 2 => unitMeasure)) := by
    apply integrable_unitPi
    apply hh.comp
    apply toSpace.continuous.comp
    fun_prop
  have h2e := (measurePreserving_piFinTwo (fun _ : Fin 2 => unitMeasure)).symm
  have h2i (a : ℝ) : Integrable (fun z : ℝ × ℝ => h (toSpace ![a, z.1, z.2]))
      (unitMeasure.prod unitMeasure) := by
    exact (h2e.integrable_comp_emb
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm.measurableEmbedding).2 (h2 a)
  symm
  calc
    cubeIntegral h = ∫ y : Fin 3 → ℝ, h (toSpace y)
        ∂Measure.pi (fun _ : Fin 3 => unitMeasure) := by
      rw [unitPi_eq]
      rfl
    _ = ∫ z : ℝ × (Fin 2 → ℝ), h (toSpace (e.symm z))
        ∂unitMeasure.prod (Measure.pi (fun _ : Fin 2 => unitMeasure)) :=
      (he.integral_comp' (fun y => h (toSpace y))).symm
    _ = ∫ a, (∫ y : Fin 2 → ℝ, h (toSpace (Fin.cons a y))
        ∂Measure.pi (fun _ : Fin 2 => unitMeasure)) ∂unitMeasure := by
      rw [integral_prod _ hei]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    _ = ∫ a, (∫ z : ℝ × ℝ, h (toSpace ![a, z.1, z.2])
        ∂unitMeasure.prod unitMeasure) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      exact (h2e.integral_comp' (fun y : Fin 2 → ℝ => h (toSpace (Fin.cons a y)))).symm
    _ = NavierStokes.PeriodicSobolev.boxIntegral h := by
      apply integral_congr_ae
      filter_upwards with a
      exact integral_prod _ (h2i a)

/-- A nonnegative box integral is at most the integral on all of ℝ³. -/
theorem boxIntegral_le_integral {h : Space → ℝ} (hh : Continuous h)
    (hi : Integrable h) (hn : ∀ x, 0 ≤ h x) :
    NavierStokes.PeriodicSobolev.boxIntegral h ≤ ∫ x, h x := by
  rw [boxIntegral_eq_cubeIntegral hh]
  have he : MeasurePreserving toSpace volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hei : Integrable (fun y : Coords => h (toSpace y)) :=
    (he.integrable_comp_emb toSpace.toHomeomorph.measurableEmbedding).2 hi
  calc
    cubeIntegral h ≤ ∫ y : Coords, h (toSpace y) :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun y => hn (toSpace y))) hei
    _ = ∫ x, h x := he.integral_comp toSpace.toHomeomorph.measurableEmbedding h

end NavierStokesR3.H3Embedding

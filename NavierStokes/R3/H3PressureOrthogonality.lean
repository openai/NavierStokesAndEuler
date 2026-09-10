import NavierStokes.R3.H3PressureDistribution
import NavierStokes.R3.H3DivCurlFourier

/-! # Pressure cancellation for ordinary first-order Sobolev fields

The pressure is an arbitrary C¹ scalar function. Only its gradient must be
square integrable; no decay or growth condition is imposed on the pressure.
-/

noncomputable section

open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology BigOperators LineDeriv

namespace NavierStokesR3.H3PressureOrthogonality

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open H3Comparison H3PressureDistribution

def complexComponent (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

@[simp] theorem complexComponent_apply (i : Fin 3) (x : Space) :
    complexComponent i x = (x i : ℂ) := rfl

theorem spatialPartial_ofReal {p : Space → ℝ} (hp : ContDiff ℝ 1 p) (i : Fin 3) :
    spatialPartial i (fun x => (p x : ℂ)) = fun x => ((spatialPartial i p x : ℝ) : ℂ) := by
  funext x
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hp.differentiable (by norm_num) x).hasFDerivAt).fderiv
  exact congrArg (fun M => M (coordinateVector i)) hd

theorem sum_distribution_eq_zero (f : Fin 3 → Space → ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume)
    (hzero : ∀ᵐ x : Space ∂volume, ∑ i : Fin 3, f i x = 0) :
    (∑ i : Fin 3, distribution ((hf i).toLp (f i))) = 0 := by
  ext ψ
  change (∑ i : Fin 3, distribution ((hf i).toLp (f i)) ψ) = 0
  simp only [distribution, Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hi (i : Fin 3) : Integrable (fun x : Space => ψ x * (hf i).toLp (f i) x) :=
    (ψ.memLp (p := 2) (μ := volume)).integrable_mul (Lp.memLp ((hf i).toLp (f i)))
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_eq_zero_of_ae
  have hrep : ∀ᵐ x : Space ∂volume, ∀ i : Fin 3, (hf i).toLp (f i) x = f i x := by
    rw [ae_all_iff]
    exact fun i => (hf i).coeFn_toLp
  filter_upwards [hzero, hrep] with x hx hr
  simp only [hr, ← Finset.mul_sum, hx, mul_zero, Pi.zero_apply]

theorem component_divergence_eq_zero {w : Space → Space} {dw : Fin 3 → Space → Space}
    (hw : H1Approximation w dw)
    (hdiv : ∀ᵐ x : Space ∂volume, ∑ i : Fin 3, dw i x i = 0) :
    (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i) (distribution
      ((hw.map (complexComponent i)).memLp.toLp (complexComponent i ∘ w)))) = 0 := by
  have hd (i : Fin 3) :=
    H3PressureDistribution.H1Approximation.derivative_distribution
      (hw.map (complexComponent i)) i
  simp_rw [hd]
  apply sum_distribution_eq_zero
  filter_upwards [hdiv] with x hx
  simpa only [Function.comp_apply, complexComponent_apply, ← Complex.ofReal_sum,
    Complex.ofReal_eq_zero] using hx

theorem integral_representatives (f g : Fin 3 → Space → ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : ∀ i, MemLp (g i) 2 volume) :
    (∑ i : Fin 3, inner ℂ ((hf i).toLp (f i)) ((hg i).toLp (g i))) =
      ∫ x : Space, ∑ i : Fin 3, star (f i x) * g i x := by
  rw [H3DivCurlFourier.sum_inner_eq_integral]
  apply integral_congr_ae
  have hrep : ∀ᵐ x : Space ∂volume, ∀ i : Fin 3,
      (hf i).toLp (f i) x = f i x ∧ (hg i).toLp (g i) x = g i x := by
    rw [ae_all_iff]
    exact fun i => (hf i).coeFn_toLp.and (hg i).coeFn_toLp
  filter_upwards [hrep] with x hx
  apply Finset.sum_congr rfl
  intro i _
  rw [(hx i).1, (hx i).2]

/-- A divergence-free ordinary H¹ field is orthogonal to an arbitrary C¹
pressure gradient in L². In particular the pressure need not belong to L². -/
theorem pressure_pairing_zero {w : Space → Space} {dw : Fin 3 → Space → Space}
    (hw : H1Approximation w dw)
    (hdiv : ∀ᵐ x : Space ∂volume, ∑ i : Fin 3, dw i x i = 0)
    {p : Space → ℝ} (hp : ContDiff ℝ 1 p)
    (hg : ∀ i : Fin 3, MemLp (spatialPartial i p) 2 volume) :
    (∫ x : Space, ∑ i : Fin 3, w x i * spatialPartial i p x) = 0 := by
  let pC : Space → ℂ := fun x => (p x : ℂ)
  have hpC : ContDiff ℝ 1 pC := Complex.ofRealCLM.contDiff.comp hp
  have hgC : ∀ i : Fin 3, MemLp (spatialPartial i pC) 2 volume := by
    intro i
    rw [show pC = (fun x => (p x : ℂ)) from rfl, spatialPartial_ofReal hp i]
    exact Complex.ofRealCLM.comp_memLp' (hg i)
  let W : Fin 3 → H3DivCurlFourier.ComplexL2 := fun i =>
    (hw.map (complexComponent i)).memLp.toLp (complexComponent i ∘ w)
  let G : Fin 3 → H3DivCurlFourier.ComplexL2 := fun i =>
    (hgC i).toLp (spatialPartial i pC)
  have hd : (∑ i : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (W i))) = 0 :=
    component_divergence_eq_zero hw hdiv
  have hc : ∀ i j : Fin 3, LineDeriv.lineDerivOp (coordinateVector i)
      (Lp.toTemperedDistribution (G j)) =
      LineDeriv.lineDerivOp (coordinateVector j) (Lp.toTemperedDistribution (G i)) :=
    gradient_curl_free hpC hgC
  have hz := H3DivCurlFourier.inner_eq_zero_of_divergence_eq_zero_curl_eq_zero W G hd hc
  have hi := integral_representatives (fun i => complexComponent i ∘ w)
    (fun i => spatialPartial i pC) (fun i => (hw.map (complexComponent i)).memLp) hgC
  change (∑ i : Fin 3, inner ℂ (W i) (G i)) = _ at hi
  rw [hz] at hi
  have hs (x : Space) : (∑ i : Fin 3, star ((complexComponent i ∘ w) x) *
      spatialPartial i pC x) = ((∑ i : Fin 3, w x i * spatialPartial i p x : ℝ) : ℂ) := by
    simp only [Function.comp_apply, complexComponent_apply, pC,
      spatialPartial_ofReal hp, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [hs] at hi
  rw [integral_complex_ofReal] at hi
  exact Complex.ofReal_eq_zero.mp hi.symm

end NavierStokesR3.H3PressureOrthogonality

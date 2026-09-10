import NavierStokes.PositiveAxisExistence
import NavierStokes.RegularSingularIntegral
import NavierStokes.CompactHolomorphicFamily

noncomputable section

namespace NavierStokes.PositiveAxisDifferential

open Set Filter
open scoped Topology Interval
open VolterraAnalyticBounds NilpotentVolterra
open PositiveAxisExistence (matrixOperator matrixOperator_apply matrixOperator_toMatrix)

local instance : NormedAddCommGroup (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedAddCommGroup (Fin 6 → Fin 6 → ℂ))
local instance : NormedSpace ℂ (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedSpace ℂ (Fin 6 → Fin 6 → ℂ))

section Families

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual profile restricted to the compact positive radial interval. -/
def familyPath (R : ℝ) (F : ℝ → ℂ → E) : ℂ → C(Icc (0 : ℝ) R, E) :=
  CompactSmoothFamily.family (Icc (0 : ℝ) R) (fun p : ℂ × ℝ => F p.2 p.1)

omit [NormedSpace ℂ E] in
theorem familyPath_apply {R : ℝ} {U : Set ℂ} {F : ℝ → ℂ → E}
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    familyPath R F z r = F r z := by
  apply CompactSmoothFamily.family_apply
  exact hF.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun x => ⟨x.2, hz⟩)

theorem familyPath_holomorphic [CompleteSpace E] {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ → ℂ → E}
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hh : ∀ r ∈ Icc (0 : ℝ) R, DifferentiableOn ℂ (F r) U) :
    DifferentiableOn ℂ (familyPath R F) U := by
  apply CompactHolomorphicFamily.differentiableOn_of_evaluations hU
  · exact CompactSmoothFamily.continuousOn_family
      (hF.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun p hp => ⟨hp.2, hp.1⟩))
  · intro r
    exact (hh r r.2).congr (fun z hz => familyPath_apply hF hz r)

end Families

/-- Ordinary competitors are described by their values, holomorphic parameter
slices, zero axis data, and actual radial derivatives. No integral equation,
path-space holomorphy, or norm smallness is assumed. -/
structure IsDifferentialSolution (R : ℝ) (U : Set ℂ) (A₀ A₁ : Coeff) (f W : Field) : Prop where
  jointly_continuous : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U)
  parameter_holomorphic : ∀ r ∈ Icc (0 : ℝ) R, ∀ i,
    DifferentiableOn ℂ (fun z => W r z i) U
  axis_zero : ∀ z ∈ U, W 0 z = 0
  equation : ∀ r ∈ Ioo (0 : ℝ) R, ∀ z ∈ U, ∀ i,
    HasDerivAt (fun s => W s z i)
      (equationRHS A₀ A₁ f W r z i - ((exponent i : ℝ) / r) • W r z i) r

/-- The usual formulation with `deriv` and radial differentiability supplies
the differential comparison class directly. -/
theorem IsDifferentialSolution.of_deriv_equation {R : ℝ} {U : Set ℂ}
    {A₀ A₁ : Coeff} {f W : Field}
    (hc : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hh : ∀ r ∈ Icc (0 : ℝ) R, ∀ i, DifferentiableOn ℂ (fun z => W r z i) U)
    (hzero : ∀ z ∈ U, W 0 z = 0)
    (hd : ∀ r ∈ Ioo (0 : ℝ) R, ∀ z ∈ U, ∀ i,
      DifferentiableAt ℝ (fun s => W s z i) r)
    (he : ∀ r ∈ Ioo (0 : ℝ) R, ∀ z ∈ U, ∀ i,
      deriv (fun s => W s z i) r + ((exponent i : ℝ) / r) • W r z i =
        equationRHS A₀ A₁ f W r z i) :
    IsDifferentialSolution R U A₀ A₁ f W := by
  refine ⟨hc, hh, hzero, ?_⟩
  intro r hr z hz i
  exact (hd r hr z hz i).hasDerivAt.congr_deriv (eq_sub_of_add_eq (he r hr z hz i))

theorem regularSolution_toDifferential {R : ℝ} {U : Set ℂ}
    {A₀ A₁ : Coeff} {f W : Field} (hW : IsRegularSolution R U A₀ A₁ f W) :
    IsDifferentialSolution R U A₀ A₁ f W :=
  IsDifferentialSolution.of_deriv_equation hW.jointly_continuous hW.parameter_holomorphic
    hW.axis_zero (fun r _ z hz i => hW.radial_differentiable z hz i r)
    (fun r hr z hz i => hW.equation r ⟨hr.1.le, hr.2.le⟩ hr.1.ne' z hz i)

theorem IsDifferentialSolution.path_holomorphic {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field} (hW : IsDifferentialSolution R U A₀ A₁ f W) :
    DifferentiableOn ℂ (familyPath R W) U :=
  familyPath_holomorphic hU hW.jointly_continuous
    (fun r hr => differentiableOn_pi.mpr (hW.parameter_holomorphic r hr))

def coefficientPath (R : ℝ) (A : Coeff) : ℂ → CoefficientPath R :=
  familyPath R (fun r z => matrixOperator (A r z))

theorem coefficientPath_apply {R : ℝ} {U : Set ℂ} {A : Coeff}
    (hA : ContinuousOn (fun p : ℝ × ℂ => A p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    coefficientPath R A z r = matrixOperator (A r z) :=
  familyPath_apply (matrixOperator.continuous.comp_continuousOn hA) hz r

theorem coefficientPath_holomorphic {R : ℝ} {U : Set ℂ} (hU : IsOpen U) {A : Coeff}
    (hA : ContinuousOn (fun p : ℝ × ℂ => A p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hh : ∀ r ∈ Icc (0 : ℝ) R, DifferentiableOn ℂ (A r) U) :
    DifferentiableOn ℂ (coefficientPath R A) U :=
  familyPath_holomorphic hU (matrixOperator.continuous.comp_continuousOn hA)
    (fun r hr => matrixOperator.differentiable.comp_differentiableOn (hh r hr))

theorem coefficientPath_shape {R : ℝ} (hR : 0 ≤ R) {A : Coeff}
    (hA : DerivativeShape A) : DerivativeShape (rawCoefficient hR (coefficientPath R A)) := by
  intro r z i j hij
  classical
  by_cases hc : Continuous (fun x : Icc (0 : ℝ) R => matrixOperator (A x z))
  · simp only [rawCoefficient, coefficientPath, familyPath, CompactSmoothFamily.family,
      dite_eq_left hc, ContinuousMap.coe_mk, matrixOperator_toMatrix]
    exact hA _ z i j hij
  · simp [rawCoefficient, coefficientPath, familyPath, CompactSmoothFamily.family, hc]

theorem parameterDeriv_eq_path {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    {W : Field}
    (hc : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hh : DifferentiableOn ℂ (familyPath R W) U)
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    parameterDeriv W r z = deriv (familyPath R W) z r := by
  ext i
  rw [← pathEvaluation_deriv (hh.differentiableAt (hU.mem_nhds hz)) r i]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with v hv
  exact congrFun (familyPath_apply hc hv r).symm i

theorem rhsPath_eq_equationRHS {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hA₀ : ContinuousOn (fun p : ℝ × ℂ => A₀ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hA₁ : ContinuousOn (fun p : ℝ × ℂ => A₁ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hf : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hc : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hh : DifferentiableOn ℂ (familyPath R W) U)
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    rhsPath (coefficientPath R A₀) (coefficientPath R A₁)
      (familyPath R f) (familyPath R W) z r = equationRHS A₀ A₁ f W r z := by
  change familyPath R f z r + (coefficientPath R A₀ z r (familyPath R W z r) +
    coefficientPath R A₁ z r (deriv (familyPath R W) z r)) = _
  rw [familyPath_apply hf hz, coefficientPath_apply hA₀ hz,
    coefficientPath_apply hA₁ hz, familyPath_apply hc hz,
    ← parameterDeriv_eq_path hU hc hh hz]
  rfl

section Conversion

variable {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
  {A₀ A₁ : Coeff} {f W : Field}
  (hA₀ : ContinuousOn (fun p : ℝ × ℂ => A₀ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
  (hA₁ : ContinuousOn (fun p : ℝ × ℂ => A₁ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
  (hf : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
  (hW : IsDifferentialSolution R U A₀ A₁ f W)

include hR hU hA₀ hA₁ hf hW

theorem IsDifferentialSolution.extended_rhs {z : ℂ} (hz : z ∈ U)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    extendPath hR (rhsPath (coefficientPath R A₀) (coefficientPath R A₁)
      (familyPath R f) (familyPath R W) z) r = equationRHS A₀ A₁ f W r z := by
  have hh := hW.path_holomorphic hU
  change extendPath hR _ (⟨r, hr⟩ : Icc (0 : ℝ) R) = _
  rw [extendPath_apply]
  exact rhsPath_eq_equationRHS hU hA₀ hA₁ hf hW.jointly_continuous hh hz ⟨r, hr⟩

/-- Ordinary differential competitors satisfy the actual radial Volterra
integral equation, including the axis and the outer endpoint. -/
theorem IsDifferentialSolution.integral_equation :
    VolterraParity.IntegralEquationOn (Icc (0 : ℝ) R) U A₀ A₁ f W := by
  intro r hr z hz
  ext i
  have hcont : ContinuousOn (fun s => W s z i) (Icc (0 : ℝ) R) :=
    (continuous_apply i).comp_continuousOn (hW.jointly_continuous.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hz⟩))
  have hg : ContinuousOn (fun s => equationRHS A₀ A₁ f W s z i) (Icc (0 : ℝ) R) := by
    apply (((continuous_apply i).comp (extendPath_continuous hR
      (rhsPath (coefficientPath R A₀) (coefficientPath R A₁)
        (familyPath R f) (familyPath R W) z))).continuousOn).congr
    intro s hs
    exact congrFun (hW.extended_rhs hR hU hA₀ hA₁ hf hz hs).symm i
  exact eq_regularPrimitive_of_hasDerivAt (exponent i) hcont hg
    (congrFun (hW.axis_zero z hz) i) (fun s hs => hW.equation s hs z hz i) hr

/-- The path-space equation is proved from the ordinary differential equation;
it is not an assumption on competing profiles. -/
theorem IsDifferentialSolution.path_equation {z : ℂ} (hz : z ∈ U) :
    familyPath R W z = pathInverse hR exponent
      (rhsPath (coefficientPath R A₀) (coefficientPath R A₁)
        (familyPath R f) (familyPath R W) z) := by
  ext r i
  rw [familyPath_apply hW.jointly_continuous hz,
    hW.integral_equation hR hU hA₀ hA₁ hf r r.2 z hz]
  change (r : ℝ) • (∫ t in (0 : ℝ)..1, (t ^ exponent i) •
    equationRHS A₀ A₁ f W (t * r) z i) =
    (r : ℝ) • (∫ t in (0 : ℝ)..1, (t ^ exponent i) •
      extendPath hR (rhsPath (coefficientPath R A₀) (coefficientPath R A₁)
        (familyPath R f) (familyPath R W) z) (t * r) i)
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only
  rw [hW.extended_rhs hR hU hA₀ hA₁ hf hz (scaled_radius_mem r.2 ht)]

end Conversion

/-- Uniqueness among ordinary differential profiles with continuous radial
dependence and holomorphic parameter slices. The comparison class has no
integral-equation assumptions and no smallness restriction. -/
theorem differential_solution_unique {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W V : Field}
    (hA₀ : ContinuousOn (fun p : ℝ × ℂ => A₀ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hA₁ : ContinuousOn (fun p : ℝ × ℂ => A₁ p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hf : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Icc (0 : ℝ) R ×ˢ U))
    (hhol₀ : ∀ r ∈ Icc (0 : ℝ) R, DifferentiableOn ℂ (A₀ r) U)
    (hhol₁ : ∀ r ∈ Icc (0 : ℝ) R, DifferentiableOn ℂ (A₁ r) U)
    (hshape : DerivativeShape A₁)
    (hW : IsDifferentialSolution R U A₀ A₁ f W)
    (hV : IsDifferentialSolution R U A₀ A₁ f V) :
    ∀ r ∈ Icc (0 : ℝ) R, ∀ z ∈ U, W r z = V r z := by
  have heq := integral_solution_unique hR hU
    (coefficientPath_holomorphic hU hA₀ hhol₀) (coefficientPath_holomorphic hU hA₁ hhol₁)
    (hW.path_holomorphic hU) (hV.path_holomorphic hU) (coefficientPath_shape hR hshape)
    (fun z hz => hW.path_equation hR hU hA₀ hA₁ hf hz)
    (fun z hz => hV.path_equation hR hU hA₀ hA₁ hf hz)
  intro r hr z hz
  have hv := congrArg (fun p : Path R => p ⟨r, hr⟩) (heq hz)
  simpa only [familyPath_apply hW.jointly_continuous hz,
    familyPath_apply hV.jointly_continuous hz] using hv

/-- The already constructed symmetric integral solution is an ordinary
differential solution on its positive radial interval. -/
theorem symmetricIntegral_toDifferential {R : ℝ} (hR : 0 ≤ R)
    {U : Set ℂ} (hU : IsOpen U) {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : VolterraRegularity.SmoothCoefficientData R U A₀ A₁ f) :
    IsDifferentialSolution R U A₀ A₁ f W := by
  have hsub : Icc (0 : ℝ) R ⊆ Icc (-R) R :=
    Icc_subset_Icc (neg_nonpos.mpr hR) le_rfl
  refine ⟨hW.jointly_continuous.mono (Set.prod_mono hsub Subset.rfl),
    (fun r hr => hW.parameter_holomorphic r (hsub hr)), hW.axis_zero, ?_⟩
  intro r hr z hz i
  have hr' : r ∈ VolterraRegularity.radialDomain R := by
    simpa only [VolterraRegularity.radialDomain, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
  have hd := PositiveAxisExistence.solution_hasDerivAt hR hU hW hdata hr' hz i
  have he := PositiveAxisExistence.solution_differential_equation hR hU hW hdata
    hr' hr.1.ne' hz i
  have hd' : HasDerivAt (fun s => W s z i) (deriv (fun s => W s z i) r) r :=
    hd.differentiableAt.hasDerivAt
  rw [eq_sub_of_add_eq he] at hd'
  exact hd'

/-- Every ordinary differential competitor equals the constructed positive
axis solution. This is uniqueness for the explicit positive-order coefficients. -/
theorem positive_solution_unique {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {h : ℂ} (lam C : ℂ)
    {F : PositiveAxisSystem.CoefficientData}
    (hF : PositiveAxisExistence.LowerInputRegularity T U h F)
    {V : Field}
    (hV : IsDifferentialSolution R U
      (PositiveAxisSystem.coefficient0 h lam C F) (PositiveAxisSystem.coefficient1 h F)
      (PositiveAxisSystem.sourceField h C F) V) :
    ∀ r ∈ Icc (0 : ℝ) R, ∀ z ∈ U,
      V r z = PositiveAxisExistence.positiveSolution hR h lam C F r z := by
  have hdata := hF.system hU lam C
  have hsub : Icc (0 : ℝ) R ⊆ VolterraRegularity.radialDomain T :=
    (Icc_subset_Icc (neg_nonpos.mpr hR) le_rfl).trans
      (PositiveAxisExistence.symmetricInterval_subset_radialDomain hRT)
  have hprod := Set.prod_mono hsub (Subset.rfl (s := U))
  have hc₀ := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr
    (fun j => ((hdata.smooth.zeroth i j).continuousOn).mono hprod))
  have hc₁ := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr
    (fun j => ((hdata.smooth.first i j).continuousOn).mono hprod))
  have hcf := continuousOn_pi.mpr
    (fun i => ((hdata.smooth.forcing i).continuousOn).mono hprod)
  have hW := symmetricIntegral_toDifferential hR hU
    (PositiveAxisExistence.positiveSolution_spec hR hRT hU lam C hF)
    ((hdata.restrict hRT.le).smooth)
  exact differential_solution_unique hR hU hc₀ hc₁ hcf
    (fun r hr => hdata.zeroth_holomorphic r (hsub hr))
    (fun r hr => hdata.first_holomorphic r (hsub hr))
    (PositiveAxisSystem.coefficient1_shape h F) hV hW

end NavierStokes.PositiveAxisDifferential

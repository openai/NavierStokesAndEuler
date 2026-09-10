import NavierStokes.ReferenceUniformJets
import NavierStokes.ClosedIntervalJetAlgebra

/-! # Reference history and stock bounds chosen before amplitude and width -/

noncomputable section

namespace NavierStokes.ReferenceUniformStocks

open Set Filter MeasureTheory ProfileHistories ReferencePath
open ReferenceUniformJets ClosedIntervalJetAlgebra
open scoped Topology ContDiff

/-- A family of smooth parameter functions with one bound for all its members. -/
def Uniform {ι : Type*} (k : ℕ) (F : ι → ℝ → ℝ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (F i) J) ∧ ∃ B, 0 ≤ B ∧ ∀ i, Bound k (F i) B

namespace Uniform

variable {ι κ : Type*} {k : ℕ} {F G : ι → ℝ → ℝ}

theorem reindex (hF : Uniform k F) (r : κ → ι) : Uniform k (fun i => F (r i)) :=
  ⟨fun i => hF.1 (r i), by obtain ⟨B,hB,hb⟩ := hF.2; exact ⟨B,hB,fun i => hb (r i)⟩⟩

theorem of_le (hF : Uniform k F) {n : ℕ} (hn : n ≤ k) : Uniform n F :=
  ⟨hF.1, by obtain ⟨B,hB,hb⟩ := hF.2; exact ⟨B,hB,fun i => (hb i).of_le hn⟩⟩

theorem const (c : ℝ) : Uniform k (fun _ : ι => fun _ : ℝ => c) :=
  ⟨fun _ => contDiffOn_const, |c|, abs_nonneg c, fun _ => Bound.const k c⟩

theorem id : Uniform k (fun _ : ι => fun η : ℝ => η) :=
  ⟨fun _ => contDiffOn_id, 1, zero_le_one, fun _ => Bound.id k⟩

theorem parameter (c : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |c i| ≤ B) :
    Uniform k (fun i => fun _ : ℝ => c i) :=
  ⟨fun _ => contDiffOn_const, B, hB, fun i => (Bound.const k (c i)).mono (hb i)⟩

theorem add (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η + G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).add (hG.1 i), B+C, add_nonneg hB hC,
    fun i => (hb i).add (hF.1 i) (hG.1 i) (hc i)⟩

theorem sub (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η - G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).sub (hG.1 i), B+C, add_nonneg hB hC,
    fun i => (hb i).sub (hF.1 i) (hG.1 i) (hc i)⟩

theorem mul (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η * G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).mul (hG.1 i), 2^k*B*C,
    mul_nonneg (mul_nonneg (by positivity) hB) hC,
    fun i => (hb i).mul (hF.1 i) (hG.1 i) (hc i)⟩

theorem neg (hF : Uniform k F) : Uniform k (fun i η => -F i η) := by
  simpa only [zero_sub] using (const (ι := ι) (k := k) 0).sub hF

theorem congr (hF : Uniform k F) (he : ∀ i, EqOn (G i) (F i) J) : Uniform k G := by
  obtain ⟨B,hB,hb⟩ := hF.2
  exact ⟨fun i => (hF.1 i).congr (he i), B,hB,fun i => (hb i).congr (he i)⟩

theorem inverse (hF : Uniform k F) {μ : ℝ} (hμ : 0 < μ)
    (hp : ∀ i η, η ∈ J → μ ≤ F i η) : Uniform k (fun i η => (F i η)⁻¹) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := inverse_bound k μ B hμ
  exact ⟨fun i => (hF.1 i).inv (fun η hη => (hμ.trans_le (hp i η hη)).ne'),
    C,hC,fun i => hc _ (hF.1 i) (hp i) (hb i)⟩

end Uniform

theorem bound_iff_jets {k : ℕ} {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ η ∈ J, ContDiffAt ℝ ∞ f η) :
    Bound k f B ↔ ∀ n ≤ k, ∀ η ∈ J, |iteratedDeriv n f η| ≤ B := by
  constructor <;> intro hb n hn η hη
  · have hh := hb n hn η hη
    rw [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiff
      ((hf η hη).of_le (TransitionRamp.nat_le_infty n)) hη,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hh
    exact hh
  · rw [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiff
      ((hf η hη).of_le (TransitionRamp.nat_le_infty n)) hη,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hb n hn η hη

theorem slice_smoothAt (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {X η : ℝ} (hp : (X,η) ∈ D.carrier) :
    ContDiffAt ℝ ∞ (fun ξ => F (X,ξ)) η :=
  (hF.contDiffAt (D.isOpen.mem_nhds hp)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)

theorem primitive_bound (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {k : ℕ} {X B : ℝ} (hX : 0 ≤ X)
    (hmem : ∀ x ∈ Icc 0 X, ∀ η ∈ J, (x,η) ∈ D.carrier)
    (hb : ∀ x ∈ Icc 0 X, Bound k (fun η => F (x,η)) B) :
    Bound k (fun η => primitive F (X,η)) (B*X) := by
  apply (bound_iff_jets (fun η hη => slice_smoothAt D (primitive_smooth D hF)
    (hmem X ⟨hX,le_rfl⟩ η hη))).mpr
  intro n hn η hη
  rw [← etaJet_eq_iteratedDeriv D (primitive_smooth D hF) n
    (hmem X ⟨hX,le_rfl⟩ η hη), etaJet_primitive D hF n (hmem X ⟨hX,le_rfl⟩ η hη)]
  change |∫ x in (0 : ℝ)..X, etaJet n F (x,η)| ≤ B*X
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := X)
    (C := B) (f := fun x => etaJet n F (x,η)) (fun x hx => by
      rw [uIoc_of_le hX] at hx
      have hxx : x ∈ Icc 0 X := ⟨hx.1.le,hx.2⟩
      rw [Real.norm_eq_abs, etaJet_eq_iteratedDeriv D hF n (hmem x hxx η hη)]
      exact (bound_iff_jets (fun ξ hξ => slice_smoothAt D hF (hmem x hxx ξ hξ))).mp
        (hb x hxx) n hn η hη)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX, mul_comm] using hi

abbrev Slab (R : ℝ) := {X : ℝ // X ∈ Icc 0 R}

abbrev FieldUniform {ι : Type*} (k : ℕ) (R : ℝ) (F : ι → Field) : Prop :=
  Uniform k (fun q : ι × Slab R => fun η => F q.1 (q.2,η))

theorem fieldUniform_primitive {ι : Type*} (D : ι → RadialDomain) {F : ι → Field}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (D i).carrier) {k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hmem : ∀ i, ∀ X ∈ Icc 0 R, ∀ η ∈ J, (X,η) ∈ (D i).carrier)
    (hb : FieldUniform k R F) : FieldUniform k R (fun i => primitive (F i)) := by
  obtain ⟨B,hB,hb⟩ := hb.2
  refine ⟨fun q η hη => (slice_smoothAt (D q.1) (primitive_smooth (D q.1) (hF q.1))
    (hmem q.1 q.2 q.2.property η hη)).contDiffWithinAt,
    B*R, mul_nonneg hB hR, ?_⟩
  intro q
  exact (primitive_bound (D q.1) (hF q.1) q.2.property.1
    (fun X hX => hmem q.1 X ⟨hX.1,hX.2.trans q.2.property.2⟩)
    (fun X hX => hb (q.1,⟨X,⟨hX.1,hX.2.trans q.2.property.2⟩⟩))).mono
      (mul_le_mul_of_nonneg_left q.2.property.2 hB)

theorem fieldUniform_partial {ι : Type*} (D : ι → RadialDomain) {F : ι → Field}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (D i).carrier) {k : ℕ} {R : ℝ}
    (hmem : ∀ i, ∀ X ∈ Icc 0 R, ∀ η ∈ J, (X,η) ∈ (D i).carrier)
    (hb : FieldUniform (k+1) R F) : FieldUniform k R (fun i => parameterPartial (F i)) := by
  obtain ⟨B,hB,hb⟩ := hb.2
  refine ⟨fun q η hη => (slice_smoothAt (D q.1) (parameterPartial_smooth (D q.1) (hF q.1))
    (hmem q.1 q.2 q.2.property η hη)).contDiffWithinAt, B,hB,?_⟩
  intro q
  apply (hb q).derivWithin.congr
  intro η hη
  exact ((parameterPartial_hasDerivAt (D q.1) (hF q.1)
    (hmem q.1 q.2 q.2.property η hη)).hasDerivWithinAt.derivWithin
      (uniqueDiff η hη)).symm

theorem uniform_smooth_fixed {ι : Type*} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g parameterInterval) (k : ℕ) :
    Uniform k (fun _ : ι => g) := by
  obtain ⟨B,hB,hb⟩ := TransitionRamp.compact_scalar_jets parameterInterval_open isCompact_Icc
    NaturalAxisCoefficients.original_interval_interior hg k
  refine ⟨fun _ => hg.mono NaturalAxisCoefficients.original_interval_interior,B,hB,fun _ => ?_⟩
  exact (bound_iff_jets (fun η hη => hg.contDiffAt
    (parameterInterval_open.mem_nhds (NaturalAxisCoefficients.original_interval_interior hη)))).mpr hb

theorem parameterPartial_const_mul (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (c : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (fun q => c*F q) p = c*parameterPartial F p :=
  (parameterPartial_hasDerivAt D (contDiffOn_const.mul hF) hp).unique
    ((parameterPartial_hasDerivAt D hF hp).const_mul c)

def axialFormula {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) : ℝ :=
  (-ActivationStocks.massFlux h p.1 p.2 (P.M p) (parameterPartial P.M p)*P.U p +
    NaturalAxisData.D h*(P.M p-p.2*parameterPartial P.M p) +
    4*h*p.2*P.S p-NaturalAxisData.d p.2*parameterPartial P.S p +
    p.1*(4*NaturalAxisData.A h*p.2*P.pressure p-
      NaturalAxisData.d p.2*parameterPartial P.pressure p)) / NaturalAxisData.L h p.2

theorem axialFormula_eq {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) :
    axialFormula P h p = p.1*P.axialLag h p/NaturalAxisData.L h p.2 := by
  rw [axialFormula, P.axialLag_integrated h hp hX,
    ← ActivationStocks.profile_massFlux P h hp]
  dsimp only [StressAlgebra.axialExponent, StressAlgebra.velocityExponent,
    StressAlgebra.coordinateFactor, NaturalAxisData.D, NaturalAxisData.A, NaturalAxisData.d]
  congr 1
  field_simp
  ring

def angularNormalizedFormula {D : RadialDomain} (P : Profiles D) (h C : ℝ) (p : Point) : ℝ :=
  (-ActivationStocks.massFlux h p.1 p.2 (P.M p) (parameterPartial P.M p) +
    ActivationStocks.angularRemainder h p.2 (C*P.I p)
      (parameterPartial (fun q => C*P.I q) p) (C*P.J p)
      (parameterPartial (fun q => C*P.J q) p) * (2*p.1)⁻¹ * (C*P.f p)⁻¹) /
      NaturalAxisData.L h p.2

theorem angularNormalizedFormula_eq {D : RadialDomain} (P : Profiles D) (h C : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) (hC : 0 < C) (hf : 0 < P.f p) :
    angularNormalizedFormula P h C p = ActivationStocks.profileStockOne P h p := by
  rw [ActivationStocks.profileStockOne_eq P h hp hX.ne' hf.ne', angularNormalizedFormula,
    parameterPartial_const_mul D P.I_smooth C hp, parameterPartial_const_mul D P.J_smooth C hp]
  unfold ActivationStocks.stockOne ActivationStocks.angularRemainder
  congr 2
  field_simp

section ActualReference

open NaturalProfile

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ}
    (d : NaturalAxisCoefficients.AnalyticInputs h j σ P0)

/-- All amplitudes and all admissible cutoff widths are quantified together. -/
structure Choice (Λ : ℝ) where
  C : ℝ
  C_ge_one : 1 ≤ C
  profile : NaturalEntrance.CoefficientProfile d Λ C
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt : 2*δ < rampLimit

namespace Choice

variable {d}

def input (hΛ : 0 < Λ) (q : Choice d Λ) : Input := Input.ofNatural hΛ q.profile.family

def profiles (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0) (q : Choice d Λ) :
    Profiles (q.input hΛ).radialDomain :=
  (q.input hΛ).histories q.δ_pos q.δ_lt P0 hP0

theorem mem (hΛ : 0 < Λ) (q : Choice d Λ) {X η : ℝ} (hX : 0 ≤ X)
    (hη : η ∈ J) : (X,η) ∈ (q.input hΛ).radialDomain.carrier :=
  ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), NaturalAxisCoefficients.original_interval_interior hη⟩

theorem C_pos (q : Choice d Λ) : 0 < q.C := zero_lt_one.trans_le q.C_ge_one

end Choice

variable (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)

theorem uniform_refU (k : ℕ) (R : ℝ) :
    FieldUniform k R (fun q : Choice d Λ => (q.profiles hΛ hP0).U) := by
  obtain ⟨B,hB,hb⟩ := exists_referenceU_jets d hΛ k
  refine ⟨fun q η hη => (slice_smoothAt _ (q.1.profiles hΛ hP0).U_smooth
    (q.1.mem hΛ q.2.property.1 hη)).contDiffWithinAt, B,zero_le_one.trans hB,?_⟩
  intro q
  apply (bound_iff_jets (fun η hη => slice_smoothAt _ (q.1.profiles hΛ hP0).U_smooth
    (q.1.mem hΛ q.2.property.1 hη))).mpr
  intro n hn η hη
  exact hb q.1.C q.1.profile q.1.δ q.1.δ_pos q.1.δ_lt q.2 q.2.property.1 n hn η hη

theorem uniform_refF_normalized (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) (R : ℝ) :
    FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(q.profiles hΛ hP0).f p) ∧
    FieldUniform k R (fun q : Choice d Λ => fun p => (q.C*(q.profiles hΛ hP0).f p)⁻¹) := by
  obtain ⟨B,hB,hb⟩ := exists_normalizedReferenceF_jets d hΛ hσ hscale k
  have hs (q : Choice d Λ × Slab R) (η : ℝ) (hη : η ∈ J) :
      ContDiffAt ℝ ∞ (fun ξ => q.1.C*(q.1.profiles hΛ hP0).f (q.2,ξ)) η :=
    contDiffAt_const.mul (slice_smoothAt _ (q.1.profiles hΛ hP0).f_smooth
      (q.1.mem hΛ q.2.property.1 hη))
  have hp (q : Choice d Λ × Slab R) (η : ℝ) (hη : η ∈ J) :
      0 < q.1.C*(q.1.profiles hΛ hP0).f (q.2,η) :=
    mul_pos q.1.C_pos ((q.1.input hΛ).refF_pos _ (q.1.mem hΛ q.2.property.1 hη) q.2.property.1)
  constructor
  · refine ⟨fun q η hη => (hs q η hη).contDiffWithinAt,B,zero_le_one.trans hB,?_⟩
    intro q
    apply (bound_iff_jets (hs q)).mpr
    intro n hn η hη
    exact (hb q.1.C q.1.C_pos q.1.profile q.1.δ q.1.δ_pos q.1.δ_lt q.2 q.2.property.1 n hn η hη).1
  · refine ⟨fun q η hη => ((hs q η hη).inv (hp q η hη).ne').contDiffWithinAt,
      B,zero_le_one.trans hB,?_⟩
    intro q
    apply (bound_iff_jets (fun η hη => (hs q η hη).inv (hp q η hη).ne')).mpr
    intro n hn η hη
    exact (hb q.1.C q.1.C_pos q.1.profile q.1.δ q.1.δ_pos q.1.δ_lt q.2 q.2.property.1 n hn η hη).2

theorem uniform_refF (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) (R : ℝ) : FieldUniform k R (fun q : Choice d Λ => (q.profiles hΛ hP0).f) := by
  have hi : Uniform k (fun q : Choice d Λ × Slab R => fun _ : ℝ => q.1.C⁻¹) :=
    Uniform.parameter _ zero_le_one (fun q => by
      rw [abs_of_pos (inv_pos.mpr q.1.C_pos)]
      exact inv_le_one_of_one_le₀ q.1.C_ge_one)
  exact (hi.mul (uniform_refF_normalized d hΛ hP0 hσ hscale k R).1).congr
    (fun q η _ => by field_simp [q.1.C_pos.ne'])

theorem uniform_radius {ι : Type*} (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Uniform k (fun q : ι × Slab R => fun _ : ℝ => (q.2 : ℝ)) :=
  Uniform.parameter _ hR (fun q => by rw [abs_of_nonneg q.2.property.1]; exact q.2.property.2)

theorem uniform_ref_histories (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    FieldUniform k R (fun q : Choice d Λ => (q.profiles hΛ hP0).M) ∧
    FieldUniform k R (fun q : Choice d Λ => (q.profiles hΛ hP0).S) ∧
    FieldUniform k R (fun q : Choice d Λ => (q.profiles hΛ hP0).pressure) ∧
    FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(q.profiles hΛ hP0).I p) ∧
    FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(q.profiles hΛ hP0).J p) := by
  let D := fun q : Choice d Λ => (q.input hΛ).radialDomain
  let P := fun q : Choice d Λ => q.profiles hΛ hP0
  have hm : ∀ q, ∀ X ∈ Icc 0 R, ∀ η ∈ J, (X,η) ∈ (D q).carrier :=
    fun q X hX η hη => q.mem hΛ hX.1 hη
  have hu := uniform_refU d hΛ hP0 k R
  have hf := uniform_refF d hΛ hP0 hσ hscale k R
  have hcf := (uniform_refF_normalized d hΛ hP0 hσ hscale k R).1
  have hx := uniform_radius (ι := Choice d Λ) k hR
  have hM := fieldUniform_primitive D (fun q => (P q).U_smooth) hR hm hu
  have hff : FieldUniform k R (fun q : Choice d Λ => fun p => (P q).f p^2) := by
    simpa only [pow_two] using hf.mul hf
  have he : FieldUniform k R (fun q : Choice d Λ => (P q).energyDensity) := by
    exact ((hu.mul hu).sub (hx.mul (hf.mul hf))).congr
      (fun q η _ => by dsimp [Profiles.energyDensity,P]; ring)
  have hS := fieldUniform_primitive D (fun q => (P q).energyDensity_smooth) hR hm he
  have hpress : FieldUniform k R (fun q : Choice d Λ => (P q).pressure) := by
    have hz := fieldUniform_primitive D (fun q => (P q).f_smooth.pow 2) hR hm hff
    exact (uniform_smooth_fixed (ι := Choice d Λ × Slab R) hP0.contDiffOn k).add hz
  have hH : FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(P q).H p) := by
    exact (((Uniform.const 2).mul hx).mul hcf).congr (fun q η _ => by dsimp [Profiles.H]; ring)
  have hI := fieldUniform_primitive D
    (fun q => contDiffOn_const.mul (P q).H_smooth) hR hm hH
  have hI' : FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(P q).I p) := by
    apply hI.congr
    intro q η _
    simp only [Profiles.I, primitive, intervalIntegral.integral_const_mul]
  have hJ := fieldUniform_primitive D
    (fun q => contDiffOn_const.mul (P q).transportDensity_smooth) hR hm
    ((hu.mul hH).congr (fun q η _ => by dsimp [Profiles.transportDensity]; ring))
  have hJ' : FieldUniform k R (fun q : Choice d Λ => fun p => q.C*(P q).J p) := by
    apply hJ.congr
    intro q η _
    simp only [Profiles.J, primitive, intervalIntegral.integral_const_mul]
  exact ⟨hM,hS,hpress,hI',hJ'⟩

theorem uniform_geometric_factors (hs : NaturalAxisRange.Parameters h j) (k : ℕ) {ι : Type*} :
    Uniform k (fun _ : ι => NaturalAxisData.d) ∧
    Uniform k (fun _ : ι => fun η => (NaturalAxisData.L h η)⁻¹) := by
  have hi : Uniform k (fun _ : ι => fun η : ℝ => η) := Uniform.id
  have hd : Uniform k (fun _ : ι => NaturalAxisData.d) := by
    exact ((Uniform.const 1).sub (hi.mul hi)).congr
      (fun q η _ => by dsimp [NaturalAxisData.d]; ring)
  have hl : Uniform k (fun _ : ι => fun η => NaturalAxisData.L h η) := by
    exact ((Uniform.const 1).sub (((Uniform.const (2*h)).mul hi).mul hi)).congr
      (fun q η _ => by dsimp [NaturalAxisData.L]; ring)
  exact ⟨hd,hl.inverse (by norm_num : (0:ℝ)<49/50)
    (fun _ _ hη => NaturalAxisRange.L_lower_bound hs hη)⟩

theorem uniform_axialFormula (hs : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    FieldUniform k R (fun q : Choice d Λ => axialFormula (q.profiles hΛ hP0) h) := by
  let D := fun q : Choice d Λ => (q.input hΛ).radialDomain
  let P := fun q : Choice d Λ => q.profiles hΛ hP0
  have hm : ∀ q, ∀ X ∈ Icc 0 R, ∀ η ∈ J, (X,η) ∈ (D q).carrier :=
    fun q X hX η hη => q.mem hΛ hX.1 hη
  obtain ⟨hM,hS,hp,-⟩ := uniform_ref_histories d hΛ hP0 hσ hscale (k+1) hR
  have hMη := fieldUniform_partial D (fun q => (P q).M_smooth) hm hM
  have hSη := fieldUniform_partial D (fun q => (P q).S_smooth) hm hS
  have hpη := fieldUniform_partial D (fun q => (P q).pressure_smooth) hm hp
  have hM := hM.of_le (Nat.le_succ k)
  have hS := hS.of_le (Nat.le_succ k)
  have hp := hp.of_le (Nat.le_succ k)
  have hu := uniform_refU d hΛ hP0 k R
  have hx := uniform_radius (ι := Choice d Λ) k hR
  have hη : Uniform k (fun _ : Choice d Λ × Slab R => fun η : ℝ => η) := Uniform.id
  obtain ⟨hd,hl⟩ := uniform_geometric_factors hs k (ι := Choice d Λ × Slab R)
  have hmass := (hx.sub ((((Uniform.const (2*NaturalAxisData.D h)).mul hη).mul hM))).sub
    (hd.mul hMη)
  have hn := (((hmass.neg.mul hu).add
    ((Uniform.const (NaturalAxisData.D h)).mul (hM.sub (hη.mul hMη)))).add
    (((Uniform.const (4*h)).mul hη).mul hS)).sub (hd.mul hSη)
  have hlast := hx.mul ((((Uniform.const (4*NaturalAxisData.A h)).mul hη).mul hp).sub
    (hd.mul hpη))
  exact ((hn.add hlast).mul hl).congr (fun q η _ => by
    simp only [axialFormula,ActivationStocks.massFlux,div_eq_mul_inv,mul_assoc,P])

abbrev PositiveSlab (a R : ℝ) := {X : ℝ // X ∈ Icc a R}

def toSlab {a R : ℝ} (ha : 0 ≤ a) (X : PositiveSlab a R) : Slab R :=
  ⟨X,ha.trans X.property.1,X.property.2⟩

theorem uniform_angularNormalizedFormula (hs : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun η =>
      angularNormalizedFormula (q.1.profiles hΛ hP0) h q.1.C (q.2,η)) := by
  let D := fun q : Choice d Λ => (q.input hΛ).radialDomain
  let P := fun q : Choice d Λ => q.profiles hΛ hP0
  let r : Choice d Λ × PositiveSlab a R → Choice d Λ × Slab R :=
    fun q => (q.1,toSlab ha.le q.2)
  have hm : ∀ q, ∀ X ∈ Icc 0 R, ∀ η ∈ J, (X,η) ∈ (D q).carrier :=
    fun q X hX η hη => q.mem hΛ hX.1 hη
  obtain ⟨hM,-,-,hI,hJ⟩ := uniform_ref_histories d hΛ hP0 hσ hscale (k+1) (ha.le.trans haR)
  have hMη := (fieldUniform_partial D (fun q => (P q).M_smooth) hm hM).reindex r
  have hIη := (fieldUniform_partial D
    (fun q => contDiffOn_const.mul (P q).I_smooth) hm hI).reindex r
  have hJη := (fieldUniform_partial D
    (fun q => contDiffOn_const.mul (P q).J_smooth) hm hJ).reindex r
  have hM := (hM.of_le (Nat.le_succ k)).reindex r
  have hI := (hI.of_le (Nat.le_succ k)).reindex r
  have hJ := (hJ.of_le (Nat.le_succ k)).reindex r
  have hx := (uniform_radius (ι := Choice d Λ) k (ha.le.trans haR)).reindex r
  have hη : Uniform k (fun _ : Choice d Λ × PositiveSlab a R => fun η : ℝ => η) := Uniform.id
  obtain ⟨hd,hl⟩ := uniform_geometric_factors hs k (ι := Choice d Λ × PositiveSlab a R)
  have hmass := (hx.sub ((((Uniform.const (2*NaturalAxisData.D h)).mul hη).mul hM))).sub
    (hd.mul hMη)
  have hr := ((((Uniform.const (1-h)).mul hI).sub
    (((Uniform.const (NaturalAxisData.D h)).mul hη).mul hIη)).sub (hd.mul hJη)).add
      (((Uniform.const (2*(h-NaturalAxisData.D h))).mul hη).mul hJ)
  have hxi : Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun _ : ℝ => (2*(q.2:ℝ))⁻¹) :=
    Uniform.parameter _ (inv_nonneg.mpr (by positivity : 0 ≤ 2*a)) (fun q => by
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) (ha.trans_le q.2.property.1)))]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left q.2.property.1 (by norm_num)))
  have hfi := ((uniform_refF_normalized d hΛ hP0 hσ hscale k R).2).reindex r
  exact ((hmass.neg.add ((hr.mul hxi).mul hfi)).mul hl).congr (fun q η _ => by
    simp only [angularNormalizedFormula,ActivationStocks.massFlux,
      ActivationStocks.angularRemainder,div_eq_mul_inv,mul_assoc,P,r,toSlab])

/-- The four literal reference quantities in `join:reference`, with all amplitudes
and all admissible cutoff widths included in one uniform family. -/
theorem uniform_reference_quantities (hs : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (k : ℕ) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun η =>
      q.1.C*(q.1.profiles hΛ hP0).E (q.2,η)) ∧
    Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun η =>
      (q.1.C*(q.1.profiles hΛ hP0).E (q.2,η))⁻¹) ∧
    Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun η =>
      ActivationStocks.profileStockOne (q.1.profiles hΛ hP0) h (q.2,η)) ∧
    Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun η =>
      (q.1.profiles hΛ hP0).axialLag h (q.2,η) / NaturalAxisData.L h η) := by
  let r : Choice d Λ × PositiveSlab a R → Choice d Λ × Slab R :=
    fun q => (q.1,toSlab ha.le q.2)
  have hcf := ((uniform_refF_normalized d hΛ hP0 hσ hscale k R).1).reindex r
  have hcfi := ((uniform_refF_normalized d hΛ hP0 hσ hscale k R).2).reindex r
  have he : Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun _ : ℝ => Real.sqrt (2*(q.2:ℝ))) :=
    Uniform.parameter _ (Real.sqrt_nonneg _) (fun q => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left q.2.property.2 (by norm_num)))
  have hei : Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun _ : ℝ =>
      (Real.sqrt (2*(q.2:ℝ)))⁻¹) :=
    Uniform.parameter _ (inv_nonneg.mpr (Real.sqrt_nonneg (2*a))) (fun q => by
      rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
        (mul_pos (by norm_num) (ha.trans_le q.2.property.1))))]
      exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left q.2.property.1 (by norm_num))))
  have hp := uniform_angularNormalizedFormula d hΛ hP0 hs hσ hscale k ha haR
  have haF := (uniform_axialFormula d hΛ hP0 hs hσ hscale k (ha.le.trans haR)).reindex r
  have hxi : Uniform k (fun q : Choice d Λ × PositiveSlab a R => fun _ : ℝ => (q.2:ℝ)⁻¹) :=
    Uniform.parameter _ (inv_nonneg.mpr ha.le) (fun q => by
      rw [abs_of_pos (inv_pos.mpr (ha.trans_le q.2.property.1))]
      exact inv_anti₀ ha q.2.property.1)
  refine ⟨(he.mul hcf).congr (fun q η _ => by dsimp [Profiles.E,r,toSlab]; ring),
    (hei.mul hcfi).congr (fun q η _ => by
      simp only [Profiles.E,mul_inv_rev,r,toSlab]; ring),
    hp.congr (fun q η hη => ?_), (haF.mul hxi).congr (fun q η hη => ?_)⟩
  · exact (angularNormalizedFormula_eq (q.1.profiles hΛ hP0) h q.1.C
      (q.1.mem hΛ (ha.le.trans q.2.property.1) hη) (ha.trans_le q.2.property.1) q.1.C_pos
      ((q.1.input hΛ).refF_pos q.1.δ
        (q.1.mem hΛ (ha.le.trans q.2.property.1) hη) (ha.le.trans q.2.property.1))).symm
  · dsimp only [r,toSlab]
    rw [axialFormula_eq _ h (q.1.mem hΛ (ha.le.trans q.2.property.1) hη)
      (ha.trans_le q.2.property.1)]
    field_simp [(ha.trans_le q.2.property.1).ne']

end ActualReference

end NavierStokes.ReferenceUniformStocks

import NavierStokes.GenericSupportedPolynomial

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter
open scoped Topology ContDiff BigOperators

variable {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A single Cartesian field factor. Coordinate vectors give the usual
multi-index derivatives; arbitrary fixed directions are also permitted. -/
inductive FieldFactor (D ι : Type*) where
  | input : ι → FieldFactor D ι
  | directional : D → FieldFactor D ι → FieldFactor D ι

def FieldFactor.expression : FieldFactor D ι → Expression D ι Empty
  | .input i => .input i
  | .directional v f => .directional v f.expression

def FieldFactor.eval (f : FieldFactor D ι) (u : ι → D → ℝ) : D → ℝ :=
  f.expression.eval (fun k => Empty.elim k) u

theorem FieldFactor.smooth_eval (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {u : ι → D → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) :
    ContDiffOn ℝ ∞ (f.eval u) U :=
  f.expression.smooth_eval hU (fun k => Empty.elim k) hu

theorem FieldFactor.congr_germ (f : FieldFactor D ι) {u v : ι → D → ℝ} {x : D}
    (h : ∀ i, u i =ᶠ[𝓝 x] v i) : f.eval u =ᶠ[𝓝 x] f.eval v := by
  induction f with
  | input i => exact h i
  | directional w f ih =>
      exact (ih.fderiv (𝕜 := ℝ)).mono (fun y hy => congrArg (fun L => L w) hy)

theorem FieldFactor.add_on (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {u v : ι → D → ℝ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U) :
    EqOn (f.eval (fun i x => u i x + v i x)) (fun x => f.eval u x + f.eval v x) U := by
  induction f with
  | input i => exact fun _ _ => rfl
  | directional w f ih =>
      intro x hx
      have he : f.eval (fun i x => u i x + v i x) =ᶠ[𝓝 x]
          (fun x => f.eval u x + f.eval v x) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hy
      change fderiv ℝ (f.eval (fun i x => u i x + v i x)) x w =
        fderiv ℝ (f.eval u) x w + fderiv ℝ (f.eval v) x w
      rw [he.fderiv_eq, fderiv_fun_add
        (((f.smooth_eval hU hu).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        (((f.smooth_eval hU hv).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      rfl

theorem FieldFactor.zero (f : FieldFactor D ι) : f.eval (fun _ _ => 0) = (fun _ => 0) := by
  induction f with
  | input i => rfl
  | directional w f ih =>
      change (fun x => fderiv ℝ (f.eval (fun _ _ => 0)) x w) = _
      rw [ih]
      simp

theorem FieldFactor.sum_on (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {σ : Type*} (s : Finset σ) {v : σ → ι → D → ℝ}
    (hv : ∀ j i, ContDiffOn ℝ ∞ (v j i) U) :
    EqOn (f.eval (fun i x => ∑ j ∈ s, v j i x)) (fun x => ∑ j ∈ s, f.eval (v j) x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x _
      simpa only [Finset.sum_empty] using congrFun f.zero x
  | @insert j s hj ih =>
      intro x hx
      have hadd := f.add_on hU (hv j) (fun i => ContDiffOn.sum (s := s) (fun k _ => hv k i)) hx
      simpa only [Finset.sum_insert hj, ih hx] using hadd

/-- Linearity propagates each field factor's support through the actual
locally finite sum. The neighborhoods for individual increments may differ. -/
theorem FieldFactor.zero_germ_of_local_sum (f : FieldFactor D ι)
    {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    {u base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ}
    (hb : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (hi : ∀ j i, ContDiffOn ℝ ∞ (inc j i) U)
    (hlocal : ∃ N, ∀ i, u i =ᶠ[𝓝 x] (fun y => base i y + ∑ j ∈ Finset.range N, inc j i y))
    (hbase : f.eval base =ᶠ[𝓝 x] (fun _ => 0))
    (hinc : ∀ j, f.eval (inc j) =ᶠ[𝓝 x] (fun _ => 0)) :
    f.eval u =ᶠ[𝓝 x] (fun _ => 0) := by
  obtain ⟨N, hN⟩ := hlocal
  have he := f.congr_germ hN
  have hs : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range N, f.eval (inc j) y = 0 :=
    (Filter.eventually_all_finset (Finset.range N)).mpr (fun j _ => hinc j)
  filter_upwards [he, hbase, hs, hU.mem_nhds hx] with y hy hyb hys hyU
  rw [hy]
  change f.eval (fun i z => base i z + ∑ j ∈ Finset.range N, inc j i z) y = 0
  have ha := f.add_on hU hb (fun i => ContDiffOn.sum (s := Finset.range N) (fun j _ => hi j i)) hyU
  calc
    _ = f.eval base y + f.eval (fun i z => ∑ j ∈ Finset.range N, inc j i z) y := ha
    _ = f.eval base y + ∑ j ∈ Finset.range N, f.eval (inc j) y :=
      congrArg (fun z => f.eval base y + z) (f.sum_on hU (Finset.range N) hi hyU)
    _ = 0 := by rw [hyb, Finset.sum_eq_zero hys, add_zero]

/-- Each leaf records the support of one differentiated field factor in the
base and every increment. Multiplication constructs arbitrary positive-degree
monomials without requiring undifferentiated components to share the support. -/
inductive FactorSupportAt (base : ι → D → ℝ) (inc : ℕ → ι → D → ℝ) (x : D) :
    Expression D ι Empty → Prop where
  | factor (f : FieldFactor D ι)
      (base_zero : f.eval base =ᶠ[𝓝 x] (fun _ => 0))
      (increment_zero : ∀ j, f.eval (inc j) =ᶠ[𝓝 x] (fun _ => 0)) :
      FactorSupportAt base inc x f.expression
  | mul {e f : Expression D ι Empty} :
      FactorSupportAt base inc x e → FactorSupportAt base inc x f →
      FactorSupportAt base inc x (.mul e f)

theorem FactorSupportAt.factor_of_tsupport {base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ}
    (f : FieldFactor D ι) {S U : Set D} {x : D} (hx : x ∈ U) (hxs : x ∉ S)
    (hb : tsupport (f.eval base) ∩ U ⊆ S)
    (hi : ∀ j, tsupport (f.eval (inc j)) ∩ U ⊆ S) :
    FactorSupportAt base inc x f.expression := by
  apply FactorSupportAt.factor f
  · exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hxs (hb ⟨h, hx⟩))
  · intro j
    exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hxs (hi j ⟨h, hx⟩))

theorem FactorSupportAt.zero_germ {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    {u base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ} {e : Expression D ι Empty}
    (h : FactorSupportAt base inc x e)
    (hb : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (hi : ∀ j i, ContDiffOn ℝ ∞ (inc j i) U)
    (hlocal : ∃ N, ∀ i, u i =ᶠ[𝓝 x] (fun y => base i y + ∑ j ∈ Finset.range N, inc j i y)) :
    e.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0) := by
  induction h with
  | factor f hbase hinc => exact f.zero_germ_of_local_sum hU hx hb hi hlocal hbase hinc
  | mul he hf ihe ihf =>
      filter_upwards [ihe, ihf] with y hy hz
      simp only [Expression.eval, hy, hz, mul_zero]

end NavierStokes.GenericDifferentialPolynomial

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Banach space of finite jets on a closed interval

A finite tuple of continuous functions is a genuine jet when neighboring
components satisfy the fundamental theorem of calculus. These are closed
linear constraints, so the resulting space is complete in the maximum jet norm.
-/

noncomputable section

namespace NavierStokes.ClosedIntervalCk

open Set MeasureTheory
open scoped Topology ContDiff

abbrev I : Set ℝ := Icc (-1 : ℝ) 1

variable (E : Type*) [NormedAddCommGroup E]

abbrev Path := C(I,E)
abbrev Jets (k : ℕ) := Fin (k+1) → Path E

variable {E}

def extend (f : Path E) : ℝ → E := Set.IccExtend (by norm_num : (-1:ℝ) ≤ 1) f

theorem extend_continuous (f : Path E) : Continuous (extend f) :=
  continuous_IccExtend_iff.mpr f.continuous

@[simp] theorem extend_apply (f : Path E) (x : I) : extend f x = f x := by
  simp [extend]

theorem extend_of_mem (f : Path E) {x : ℝ} (hx : x ∈ I) :
    extend f x = f ⟨x,hx⟩ := extend_apply f ⟨x,hx⟩

@[simp] theorem extend_zero : extend (0 : Path E) = 0 := by funext x; rfl
@[simp] theorem extend_add (f g : Path E) : extend (f+g) = extend f+extend g := by funext x; rfl

variable [NormedSpace ℝ E]

@[simp] theorem extend_smul (c : ℝ) (f : Path E) : extend (c • f) = c • extend f := by funext x; rfl

def primitiveLinear (x : ℝ) : Path E →ₗ[ℝ] E where
  toFun f := ∫ t in (-1:ℝ)..x, extend f t
  map_add' f g := by
    simp only [extend_add, Pi.add_apply]
    exact intervalIntegral.integral_add ((extend_continuous f).intervalIntegrable _ _)
      ((extend_continuous g).intervalIntegrable _ _)
  map_smul' c f := by
    simp only [extend_smul, Pi.smul_apply, RingHom.id_apply]
    exact intervalIntegral.integral_smul c (extend f)

theorem norm_primitiveLinear_le (x : ℝ) (f : Path E) :
    ‖primitiveLinear x f‖ ≤ |x+1| *‖f‖ := by
  have hb : ∀ t ∈ uIcc (-1:ℝ) x, ‖extend f t‖ ≤ ‖f‖ := by
    intro t ht
    exact f.norm_coe_le_norm _
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hb t (uIoc_subset_uIcc ht))
  simpa only [primitiveLinear, LinearMap.coe_mk, AddHom.coe_mk, sub_neg_eq_add,
    mul_comm] using hi

def primitive (x : ℝ) : Path E →L[ℝ] E :=
  (primitiveLinear x).mkContinuous |x+1| (norm_primitiveLinear_le x)

@[simp] theorem primitive_apply (x : ℝ) (f : Path E) :
    primitive x f = ∫ t in (-1:ℝ)..x, extend f t := rfl

def leftEndpoint : I := ⟨-1, by constructor <;> norm_num⟩

def constraint (k : ℕ) (j : Fin k) (x : I) : Jets E k →L[ℝ] E :=
  (((ContinuousMap.evalCLM ℝ x - ContinuousMap.evalCLM ℝ leftEndpoint) : Path E →L[ℝ] E).comp
    (ContinuousLinearMap.proj j.castSucc)) -
      (primitive x).comp (ContinuousLinearMap.proj j.succ)

@[simp] theorem constraint_apply (k : ℕ) (j : Fin k) (x : I) (f : Jets E k) :
    constraint k j x f = f j.castSucc x-f j.castSucc leftEndpoint-
      ∫ t in (-1:ℝ)..(x:ℝ), extend (f j.succ) t := rfl

/-- Every compatibility condition is the kernel of a concrete continuous linear map. -/
def jetSubmodule (k : ℕ) : Submodule ℝ (Jets E k) :=
  ⨅ (j : Fin k) (x : I), (constraint k j x).ker

theorem mem_jetSubmodule_iff (k : ℕ) (f : Jets E k) :
    f ∈ jetSubmodule k ↔ ∀ (j : Fin k) (x : I),
      f j.castSucc x = f j.castSucc leftEndpoint+
        ∫ t in (-1:ℝ)..(x:ℝ), extend (f j.succ) t := by
  simp only [jetSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hf j x
    have hx := hf j x
    change f j.castSucc x-f j.castSucc leftEndpoint-
      (∫ t in (-1:ℝ)..(x:ℝ), extend (f j.succ) t) = 0 at hx
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hx)).trans (add_comm _ _)
  · intro hf j x
    change f j.castSucc x-f j.castSucc leftEndpoint-
      (∫ t in (-1:ℝ)..(x:ℝ), extend (f j.succ) t) = 0
    rw [hf j x]
    abel

theorem jetSubmodule_closed (k : ℕ) : IsClosed (jetSubmodule (E := E) k : Set (Jets E k)) := by
  simp only [jetSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter (fun j => isClosed_iInter (fun x => (constraint k j x).isClosed_ker))

/-- The actual finite `C^k` jet space with the inherited maximum-component norm. -/
def CK (k : ℕ) : Type _ := jetSubmodule (E := E) k

instance (k : ℕ) : NormedAddCommGroup (CK (E := E) k) :=
  inferInstanceAs (NormedAddCommGroup (jetSubmodule (E := E) k))

instance (k : ℕ) : NormedSpace ℝ (CK (E := E) k) :=
  inferInstanceAs (NormedSpace ℝ (jetSubmodule (E := E) k))

instance [CompleteSpace E] (k : ℕ) : CompleteSpace (CK (E := E) k) :=
  (jetSubmodule_closed (E := E) k).completeSpace_coe



theorem uniqueDiff : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by norm_num)

variable [CompleteSpace E]

/-- Compatibility gives the actual one-sided derivative, including both endpoints. -/
theorem component_hasDerivWithinAt {k : ℕ} (f : CK (E := E) k) (j : Fin k) (x : I) :
    HasDerivWithinAt (extend (f.val j.castSucc)) (f.val j.succ x) I x := by
  have hc := extend_continuous (f.val j.succ)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (-1) x)
    (hc.continuousOn.stronglyMeasurableAtFilter isOpen_univ x (mem_univ _)) hc.continuousAt
  have hs := (hd.const_add (f.val j.castSucc leftEndpoint)).hasDerivWithinAt (s := I)
  rw [extend_apply] at hs
  have he : EqOn (extend (f.val j.castSucc))
      (fun y => f.val j.castSucc leftEndpoint+∫ t in (-1:ℝ)..y, extend (f.val j.succ) t) I := by
    intro y hy
    have h := (mem_jetSubmodule_iff k f.val).mp f.property j ⟨y,hy⟩
    simpa only [← extend_apply, Subtype.coe_mk] using h
  exact hs.congr he (he x.property)

/-- Every stored component is the actual iterated parameter derivative. -/
theorem actual_jet {k : ℕ} (f : CK (E := E) k) (n : ℕ) (hn : n ≤ k) (x : I) :
    iteratedDerivWithin n (extend (f.val 0)) I x = f.val ⟨n,by omega⟩ x := by
  induction n generalizing x with
  | zero => simp [iteratedDerivWithin_zero]
  | succ n ih =>
      have hnk : n ≤ k := by omega
      have he : EqOn (iteratedDerivWithin n (extend (f.val 0)) I)
          (extend (f.val ⟨n,by omega⟩)) I := by
        intro y hy
        simpa only [extend_of_mem _ hy] using ih hnk ⟨y,hy⟩
      rw [iteratedDerivWithin_succ, derivWithin_congr he (he x.property)]
      exact (component_hasDerivWithinAt f ⟨n,by omega⟩ x).derivWithin (uniqueDiff x x.property)

/-- Genuine `C^k` regularity follows from the defining closed constraints. -/
theorem contDiffOn {k : ℕ} (f : CK (E := E) k) :
    ContDiffOn ℝ k (extend (f.val 0)) I := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv uniqueDiff).mpr
  constructor
  · intro n hn
    apply (extend_continuous (f.val ⟨n,by omega⟩)).continuousOn.congr
    intro x hx
    simpa only [extend_of_mem _ hx] using actual_jet f n hn ⟨x,hx⟩
  · intro n hn x hx
    have hj : (⟨n,hn⟩ : Fin k).castSucc = (⟨n,by omega⟩ : Fin (k+1)) := Fin.ext rfl
    have hd : DifferentiableWithinAt ℝ (extend (f.val (⟨n,by omega⟩ : Fin (k+1)))) I x := by
      simpa only [hj] using (component_hasDerivWithinAt f ⟨n,hn⟩ ⟨x,hx⟩).differentiableWithinAt
    apply hd.congr
    · intro y hy
      simpa only [extend_of_mem _ hy] using actual_jet f n hn.le ⟨y,hy⟩
    · simpa only [extend_of_mem _ hx] using actual_jet f n hn.le ⟨x,hx⟩

/-- The inherited norm is precisely the maximum norm of all derivatives through `k`. -/
theorem norm_le_iff {k : ℕ} (f : CK (E := E) k) {B : ℝ} (hB : 0 ≤ B) :
    ‖f‖ ≤ B ↔ ∀ n ≤ k, ∀ x : I, ‖iteratedDerivWithin n (extend (f.val 0)) I x‖ ≤ B := by
  change ‖f.val‖ ≤ B ↔ _
  rw [pi_norm_le_iff_of_nonneg hB]
  constructor
  · intro hf n hn x
    rw [actual_jet f n hn x]
    exact (ContinuousMap.norm_le (f.val ⟨n,by omega⟩) hB).mp (hf _) x
  · intro hf j
    apply (ContinuousMap.norm_le (f.val j) hB).mpr
    intro x
    have hh := hf j.val (by omega) x
    rw [actual_jet f j.val (by omega) x] at hh
    exact hh



/-- Forgetting derivatives is a continuous linear map to continuous functions. -/
def value (k : ℕ) : CK (E := E) k →L[ℝ] Path E :=
  (ContinuousLinearMap.proj 0).comp (jetSubmodule (E := E) k).subtypeL

omit [CompleteSpace E] in
@[simp] theorem value_apply {k : ℕ} (f : CK (E := E) k) : value k f = f.val 0 := rfl

theorem value_injective (k : ℕ) : Function.Injective (value (E := E) k) := by
  intro f g hfg
  have he : extend (f.val 0) = extend (g.val 0) := congrArg extend hfg
  apply Subtype.ext
  funext j
  apply ContinuousMap.ext
  intro x
  rw [← actual_jet f j.val (by omega) x, ← actual_jet g j.val (by omega) x, he]

theorem norm_value_le {k : ℕ} (f : CK (E := E) k) : ‖value k f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  simpa only [iteratedDerivWithin_zero, value_apply, extend_apply] using
    (norm_le_iff f (norm_nonneg f)).mp le_rfl 0 (Nat.zero_le _) x

theorem norm_zero_eq_value (f : CK (E := E) 0) : ‖f‖ = ‖value 0 f‖ := by
  apply le_antisymm _ (norm_value_le f)
  apply (norm_le_iff f (norm_nonneg _)).mpr
  intro n hn x
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  simpa only [iteratedDerivWithin_zero, value_apply, extend_apply] using
    (value 0 f).norm_coe_le_norm x

/-- The actual derivative tuple of a `C^k` function. -/
def functionJets {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I) : Jets E k :=
  fun j => ⟨fun x => iteratedDerivWithin j.val f I x,
    (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast Nat.le_of_lt_succ j.isLt)
      uniqueDiff).domRestrict⟩

omit [CompleteSpace E] in
@[simp] theorem functionJets_apply {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I)
    (j : Fin (k+1)) (x : I) : functionJets f hf j x = iteratedDerivWithin j.val f I x := rfl

theorem functionJets_mem {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I) :
    functionJets f hf ∈ jetSubmodule k := by
  apply (mem_jetSubmodule_iff k _).mpr
  intro j x
  have hj : j.val < k := j.isLt
  have hcont := hf.continuousOn_iteratedDerivWithin (m := j.val) (by exact_mod_cast hj.le) uniqueDiff
  have hcont' := hf.continuousOn_iteratedDerivWithin (m := j.val+1) (by exact_mod_cast Nat.succ_le_of_lt hj) uniqueDiff
  have hsub : Icc (-1:ℝ) (x:ℝ) ⊆ I := Icc_subset_Icc le_rfl x.property.2
  have hder : ∀ y ∈ Ioo (-1:ℝ) (x:ℝ),
      HasDerivAt (iteratedDerivWithin j.val f I) (iteratedDerivWithin (j.val+1) f I y) y := by
    intro y hy
    have hyI : y ∈ I := ⟨hy.1.le,hy.2.le.trans x.property.2⟩
    have hd := (hf.differentiableOn_iteratedDerivWithin (m := j.val)
      (by exact_mod_cast hj) uniqueDiff y hyI).hasDerivWithinAt
    have hn : I ∈ nhds y := Icc_mem_nhds hy.1 (hy.2.trans_le x.property.2)
    simpa only [← iteratedDerivWithin_succ] using hd.hasDerivAt hn
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
    (hcont.mono hsub) hder ((hcont'.mono hsub).intervalIntegrable_of_Icc x.property.1)
  have he : (∫ t in (-1:ℝ)..(x:ℝ), extend (functionJets f hf j.succ) t) =
      ∫ t in (-1:ℝ)..(x:ℝ), iteratedDerivWithin (j.val+1) f I t := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyI : y ∈ I := hsub (by simpa only [uIcc_of_le x.property.1] using hy)
    rw [extend_of_mem _ hyI]
    rfl
  rw [he, hi]
  simp only [functionJets_apply, Fin.val_castSucc, leftEndpoint]
  abel

/-- Every ordinary `C^k` function supplies an element of the complete jet space. -/
def ofContDiffOn {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I) : CK (E := E) k :=
  ⟨functionJets f hf,functionJets_mem f hf⟩

@[simp] theorem ofContDiffOn_value {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I) (x : I) :
    value k (ofContDiffOn f hf) x = f x := rfl



theorem norm_ofContDiffOn_le_iff {k : ℕ} (f : ℝ → E) (hf : ContDiffOn ℝ k f I)
    {B : ℝ} (hB : 0 ≤ B) :
    ‖ofContDiffOn f hf‖ ≤ B ↔ ∀ n ≤ k, ∀ x : I, ‖iteratedDerivWithin n f I x‖ ≤ B := by
  change ‖functionJets f hf‖ ≤ B ↔ _
  rw [pi_norm_le_iff_of_nonneg hB]
  constructor
  · intro hb n hn x
    exact (ContinuousMap.norm_le (functionJets f hf ⟨n,by omega⟩) hB).mp (hb _) x
  · intro hb j
    apply (ContinuousMap.norm_le (functionJets f hf j) hB).mpr
    exact fun x => hb j.val (by omega) x



def lowerValue {k l : ℕ} (h : l ≤ k) (f : CK (E := E) k) : CK (E := E) l :=
  ofContDiffOn (extend (value k f)) ((contDiffOn f).of_le (by exact_mod_cast h))

@[simp] theorem lowerValue_value {k l : ℕ} (h : l ≤ k) (f : CK (E := E) k) (x : I) :
    value l (lowerValue h f) x = value k f x := by
  change extend (value k f) x = _
  exact extend_apply _ _

theorem norm_lowerValue_le {k l : ℕ} (h : l ≤ k) (f : CK (E := E) k) :
    ‖lowerValue h f‖ ≤ ‖f‖ := by
  apply (norm_ofContDiffOn_le_iff _ _ (norm_nonneg f)).mpr
  intro n hn x
  exact (norm_le_iff f (norm_nonneg f)).mp le_rfl n (hn.trans h) x

def lowerLinear {k l : ℕ} (h : l ≤ k) : CK (E := E) k →ₗ[ℝ] CK (E := E) l where
  toFun := lowerValue h
  map_add' f g := by
    apply value_injective l
    apply ContinuousMap.ext
    intro x
    simp only [lowerValue_value, map_add, ContinuousMap.add_apply]
  map_smul' c f := by
    apply value_injective l
    apply ContinuousMap.ext
    intro x
    simp only [lowerValue_value, map_smul, ContinuousMap.smul_apply, RingHom.id_apply]

/-- The natural inclusion `C^k → C^l` for `l ≤ k`, with its actual maximum derivative norm. -/
def lower {k l : ℕ} (h : l ≤ k) : CK (E := E) k →L[ℝ] CK (E := E) l :=
  (lowerLinear (E := E) h).mkContinuous 1 (fun f => by
    change ‖lowerValue h f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_lowerValue_le h f)

@[simp] theorem lower_apply {k l : ℕ} (h : l ≤ k) (f : CK (E := E) k) : lower h f = lowerValue h f := rfl

theorem lower_injective {k l : ℕ} (h : l ≤ k) : Function.Injective (lower (E := E) h) := by
  intro f g hfg
  apply value_injective k
  apply ContinuousMap.ext
  intro x
  have he := congrArg (fun u : CK (E := E) l => value l u x) hfg
  simpa only [lower_apply, lowerValue_value] using he

@[simp] theorem lower_ofContDiffOn {k l : ℕ} (h : l ≤ k) (f : ℝ → E) (hf : ContDiffOn ℝ k f I) :
    lower h (ofContDiffOn f hf) = ofContDiffOn f (hf.of_le (by exact_mod_cast h)) := by
  apply value_injective l
  apply ContinuousMap.ext
  intro x
  simp only [lower_apply, lowerValue_value, ofContDiffOn_value]

end NavierStokes.ClosedIntervalCk

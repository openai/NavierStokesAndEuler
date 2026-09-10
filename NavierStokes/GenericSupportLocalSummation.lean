import NavierStokes.GenericSummationRealization
import NavierStokes.GenericSupportLocalCoefficients

/-! # Actual summation residuals with support-local coefficient regularity

Every statement retains the given cutoff schedule, literal polynomial and
coefficient functions. Smoothness and growth of a nonconstant coefficient
are only needed on its common differentiated-factor support region.
-/

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericDifferentialPolynomial DiagonalResidual
open GenericRealizationBounds GenericRealization GenericSolenoidalRealization
open scoped Topology ContDiff BigOperators

/-! ## Residual transfer from actual field approximation -/

theorem Result.flat_residual_support_local {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (components (fun j => (a j : ℝ)) q u0 s0 A B R)
        =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (stageComponents u0 s0 A B R J)
        =ᶠ[𝓝 x] (fun _ => 0))
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hu : ∀ i, ContDiffOn ℝ ∞ (components (fun j => (a j : ℝ)) q u0 s0 A B R i) U := by
    intro i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn H.smooth_velocity
    | inr k => exact H.smooth_scalars k
  have hus : ∀ J i, ContDiffOn ℝ ∞ (stageComponents u0 s0 A B R J i) U := by
    intro J i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (positiveStage_smooth hU hu0 hA hB J)
    | inr k => exact stage_smooth (hs0 k) (hR k) J
  have hgain : Tendsto (fun J => g (J + 1) / 2) atTop atTop :=
    (hgtop.comp (tendsto_add_atTop_nat 1)).atTop_div_const (by norm_num)
  exact uniform_bound_of_rate (P.flat_of_support_local_coefficients hU hlU hlq hu hus hgain hrho
    (fun i => (H.approximation i).some) hconst region hc Lc hcg hzero hszero Lres hres m N)


/-- Raw and cut differentiated-factor supports imply the required zero germs
for the actual finite stages and locally finite realized sum. -/
theorem Result.flat_residual_of_support_local_factors {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, DiagonalResidual.JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, DiagonalResidual.JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  apply H.flat_residual_support_local hU hq hu0 hs0 hA hB hR hgtop P hconst region hc Lc hcg
    _ _ rho hrho Lres hres m N
  · intro t ht x hx hxs
    exact (hcutsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_cutIncrementComponents hU hqs hA hB hR)
      (components_local_sum hU H.tends hqs (fun w hw => (hq w hw).1) hA hx)
  · intro t ht J x hx hxs
    exact (hrawsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_incrementComponents hU hA hB hR) (stageComponents_local_sum hU hA J hx)


/-- The printed logarithmic hypotheses with coefficients smooth only on the
common supports, independent correction and residual gains, and an arbitrary
all-orders-flat finite-stage error, imply flatness of the actual residual. -/
theorem Result.flat_residual_of_support_local_raw_bounds {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Cc Pc Kc : ℕ → ℝ)
    (hcoeff : ∀ t ∈ P.terms, ∀ m x, x ∈ U → x ∈ region t →
      ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Cr Pr : ℕ → ℕ → ℝ) (Kr : ℕ → ℝ)
    (error : ℕ → ℕ → SpaceTime → ℝ)
    (hres : ∀ J m x, x ∈ U →
      ‖iteratedFDeriv ℝ m (P.eval (stageComponents u0 s0 A B R J)) x‖ ≤
        Cr J m * (1 + |Real.log (q x)|) ^ Pr J m * q x ^ (rho J - Kr m) + error J m x)
    (he : ∀ J m N, ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ x ∈ U, error J m x ≤ Ce * q x ^ (N : ℕ))
    (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hqzero := scale_tendsto U q
  have hcoeffRate : ∀ t ∈ P.terms, ∀ m,
      JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-(Kc m + 1)) := by
    intro t ht m
    have hregion : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t), x ∈ region t :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    have hb : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t),
        ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m) := by
      filter_upwards [hlU.filter_mono inf_le_left, hregion] with x hx hr
      exact hcoeff t ht m x hx hr
    convert jetRate_of_log_bound ((hlq.filter_mono inf_le_left).mono fun _ hx => hx.1)
      (hqzero.mono_left inf_le_left) m (Cc m) (Pc m) (-Kc m) hb using 1
    ring
  have hresRate : ∀ J k, JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) k (rho J - (Kr k + 1)) := by
    intro J k
    have herr : ∀ M : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ᶠ x in scaleApproach U q, error J k x ≤ Ce * q x ^ M := by
      intro M
      obtain ⟨Ce, hCe, hb⟩ := he J k M
      exact ⟨Ce, hCe, hlU.mono fun x hx => hb x hx⟩
    convert jetRate_of_log_bound_add_flat hlq hqzero k (Cr J k) (Pr J k)
      (rho J - Kr k) (hlU.mono fun x hx => hres J k x hx) herr using 1
    ring
  exact H.flat_residual_of_support_local_factors hU hqs hq hu0 hs0 hA hB hR hgtop P hconst region hc
    (fun _ m => Kc m + 1) hcoeffRate hrawsupport hcutsupport rho hrho
    (fun m => Kr m + 1) hresRate m N


end NavierStokes.GenericTupleRealization

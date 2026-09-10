import NavierStokes.GenericTupleSupport
import NavierStokes.GenericAngularRecovery

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericDifferentialPolynomial DiagonalResidual
open GenericRealizationBounds GenericRealization
open scoped Topology ContDiff BigOperators

/-- The base-growth assumption of the manuscript implies the approximation
interface used in the simultaneous realization theorem. -/
theorem base_rate_of_raw_log {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set SpaceTime} {q : SpaceTime → ℝ} {f : SpaceTime → W}
    (hq : ∀ w ∈ U, 0 < q w) (C P K : ℕ → ℝ)
    (hb : ∀ m w, w ∈ U → ‖iteratedFDeriv ℝ m f w‖ ≤
      C m * (1 + |Real.log (q w)|) ^ P m * q w ^ (-K m)) :
    ∀ m, JetRate (scaleApproach U q) q f m (-(K m + 1)) := by
  intro m
  have hlU := eventually_domain U q
  convert jetRate_of_log_bound (hlU.mono fun w hw => hq w hw) (scale_tendsto U q)
    m (C m) (P m) (-K m) (hlU.mono fun w hw => hb m w hw) using 1
  ring

/-- The simultaneous realization under the literal smooth Cartesian angular
representatives and axial scale of the manuscript. Solenoidality and tangency
are derived; cylindrical rate derivatives are not hypotheses. -/
theorem exists_angular_realization {κ : Type*} [Fintype κ] {U : Set SpaceTime}
    (hU : IsOpen U) {q : SpaceTime → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (Q : ℝ × ℝ → ℝ) (haxial : q = fun w => Q (w.1, w.2 2))
    (hpos : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (Bq : ℕ → ℝ) (hBq : ∀ k w, w ∈ U → q w ≤ 1 →
      ‖iteratedFDeriv ℝ k q w‖ ≤ Bq k * q w ^ (1 - (k : ℝ)))
    {u0 : VelocityField} {s0 : κ → PressureField}
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (K0 : ℕ → ℝ) (Ks : κ → ℕ → ℝ)
    (hbaseU : ∀ m, JetRate (scaleApproach U q) q u0 m (-K0 m))
    (hbaseS : ∀ k m, JetRate (scaleApproach U q) q (s0 k) m (-Ks k m))
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (b : ℕ → DirectAngularDiagonal.Coefficient)
    (hangular : ∀ j, 1 ≤ j → B j = DirectAngularDiagonal.angularField (b j))
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (g L : ℕ → ℝ) (C P : Entry κ → ℕ → ℕ → ℝ)
    (hraw : ∀ e, CutStageEstimates.RawStageBounds q (representatives A B R e) g L (C e) (P e) U)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (hgmono : Monotone g)
    (hdiv0 : ∀ w ∈ U, spatialDivergence u0 w.1 w.2 = 0)
    {τ : Type*} (tests : ℕ → Finset τ) (Bt Pt γ : ℕ → τ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, (∀ j, 1 / (a j : ℝ) < q0) ∧ Result U q u0 s0 A B R g L a ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (Bt j k) (Pt j k) (γ j k) r| ≤ (1 / 2 : ℝ) ^ j := by
  have hadmissible : ∀ j, 1 ≤ j → ∀ w ∈ U,
      spatialDivergence (B j) w.1 w.2 = 0 ∧
        ∑ i : Fin 3, fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0 := by
    intro j hj w hw
    have hqa : ContDiffAt ℝ ∞ (fun z : SpaceTime => Q (z.1, z.2 2)) w := by
      simpa only [haxial] using hq.contDiffAt (hU.mem_nhds hw)
    have hba : ContDiffAt ℝ ∞ (DirectAngularDiagonal.angularField (b j)) w := by
      rw [← hangular j hj]
      exact (hB j hj).contDiffAt (hU.mem_nhds hw)
    simpa only [hangular j hj, haxial] using
      GenericSolenoidalRealization.angular_admissibility Q (b j) hqa hba
  exact exists_realization hU hq hpos Bq hBq hu0 hs0 K0 Ks hbaseU hbaseS
    hA hB hR g L C P hraw hg hgmono hdiv0 (fun j hj w hw => (hadmissible j hj w hw).1)
    (fun j hj w hw => (hadmissible j hj w hw).2) tests Bt Pt γ hγ hq0

/-- Full residual conclusion of `sum:realization`, including logarithmic
coefficient growth only on common factor supports and an arbitrary flat
finite-stage error. The realization and schedule are those of
`GenericTupleRealization.exists_realization`; no residual or support property
of the unknown infinite sum is an assumption. -/
theorem Result.flat_residual_of_raw_bounds {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U) (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
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
  exact H.flat_residual_of_factor_support hU hqs hq hu0 hs0 hA hB hR hgtop P hconst hc
    region (fun _ m => Kc m + 1) hcoeffRate hrawsupport hcutsupport rho hrho
    (fun m => Kr m + 1) hresRate m N

end NavierStokes.GenericTupleRealization

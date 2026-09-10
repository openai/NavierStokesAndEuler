import NavierStokes.GenericVelocityRates

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement DiagonalResidual GenericRealizationBounds GenericDifferentialPolynomial
open GenericSolenoidalRealization GenericRealization
open scoped Topology ContDiff BigOperators

abbrev Entry (κ : Type*) := Bool ⊕ κ

def Value {κ : Type*} : Entry κ → Type
  | .inl _ => Space
  | .inr _ => ℝ

instance {κ : Type*} (e : Entry κ) : NormedAddCommGroup (Value e) :=
  match e with
  | .inl _ => inferInstanceAs (NormedAddCommGroup Space)
  | .inr _ => inferInstanceAs (NormedAddCommGroup ℝ)

instance {κ : Type*} (e : Entry κ) : NormedSpace ℝ (Value e) :=
  match e with
  | .inl _ => inferInstanceAs (NormedSpace ℝ Space)
  | .inr _ => inferInstanceAs (NormedSpace ℝ ℝ)

def representatives {κ : Type*} (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) :
    ∀ e : Entry κ, ℕ → SpaceTime → Value e
  | .inl false => A
  | .inl true => B
  | .inr k => R k

/-- The optional scalar entries comprise pressure and any finite stress
components. Taking a singleton retains pressure alone. -/
def components {κ : Type*} (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => positiveVelocity a q u0 A B w i
  | .inr k => realized a q (s0 k) (R k)

def stageComponents {κ : Type*} (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) (J : ℕ) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => positiveStage u0 A B J w i
  | .inr k => stage (s0 k) (R k) J

structure Result {κ : Type*} (U : Set SpaceTime) (q : SpaceTime → ℝ)
    (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField)
    (g L : ℕ → ℝ) (a : ℕ → ℕ) : Prop where
  positive : ∀ j, 0 < a j
  doubling : ∀ j, 2 * a j ≤ a (j + 1)
  monotone : StrictMono a
  tends : Tendsto (fun j => (a j : ℝ)) atTop atTop
  locallyFinite_representatives : ∀ e, LocallyFinite (fun j => Function.support
    (fun w : U => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) q
      (CutStageEstimates.positiveStages (representatives A B R e)) j w))
  smooth_velocity : ContDiffOn ℝ ∞ (positiveVelocity (fun j => (a j : ℝ)) q u0 A B) U
  smooth_scalars : ∀ k, ContDiffOn ℝ ∞ (realized (fun j => (a j : ℝ)) q (s0 k) (R k)) U
  divergence : ∀ w ∈ U, spatialDivergence (positiveVelocity (fun j => (a j : ℝ)) q u0 A B) w.1 w.2 = 0
  approximation : ∀ i, Nonempty (ApproximationRates (scaleApproach U q) q (fun J => g (J + 1) / 2)
    (components (fun j => (a j : ℝ)) q u0 s0 A B R i) (fun J => stageComponents u0 s0 A B R J i))
  tail_velocity : ∀ w ∈ U, ∀ J m, m ≤ J + 2 → q w < 1 / (2 * (a J : ℝ)) →
    ‖iteratedFDeriv ℝ m (fun y => positiveVelocity (fun j => (a j : ℝ)) q u0 A B y -
      positiveStage u0 A B J y) w‖ ≤ (1 / 2 : ℝ) ^ J * q w ^
        (g (J + 1) / 2 - (max (CutStageEstimates.cutLoss L (m + 1)) (CutStageEstimates.cutLoss L m) + 1))
  tail_scalars : ∀ k w, w ∈ U → ∀ J m, m ≤ J + 3 → q w < 1 / (2 * (a J : ℝ)) →
    ‖iteratedFDeriv ℝ m (fun y => realized (fun j => (a j : ℝ)) q (s0 k) (R k) y -
      stage (s0 k) (R k) J y) w‖ ≤
      (1 / 2 : ℝ) ^ J * q w ^ (g (J + 1) / 2 - CutStageEstimates.cutLoss L m)
  outer_velocity : ∀ w, ContinuousAt q w → 1 / (a 0 : ℝ) < q w →
    positiveVelocity (fun j => (a j : ℝ)) q u0 A B =ᶠ[𝓝 w] u0
  outer_scalars : ∀ k w, ContinuousAt q w → 1 / (a 0 : ℝ) < q w →
    realized (fun j => (a j : ℝ)) q (s0 k) (R k) =ᶠ[𝓝 w] s0 k

/-- Simultaneous realization of the literal solenoidal velocity, pressure,
and arbitrary additional finite stress entries. All polynomial tests use
this same schedule and these same scalar components. -/
theorem exists_realization {κ : Type*} [Fintype κ] {U : Set SpaceTime}
    (hU : IsOpen U) {q : SpaceTime → ℝ} (hq : ContDiffOn ℝ ∞ q U)
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
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (g L : ℕ → ℝ) (C P : Entry κ → ℕ → ℕ → ℝ)
    (hraw : ∀ e, CutStageEstimates.RawStageBounds q (representatives A B R e) g L (C e) (P e) U)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (hgmono : Monotone g)
    (hdiv0 : ∀ w ∈ U, spatialDivergence u0 w.1 w.2 = 0)
    (hdivB : ∀ j, 1 ≤ j → ∀ w ∈ U, spatialDivergence (B j) w.1 w.2 = 0)
    (htan : ∀ j, 1 ≤ j → ∀ w ∈ U, ∑ i : Fin 3,
      fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0)
    {τ : Type*} (tests : ℕ → Finset τ) (Bt Pt γ : ℕ → τ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, (∀ j, 1 / (a j : ℝ) < q0) ∧ Result U q u0 s0 A B R g L a ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (Bt j k) (Pt j k) (γ j k) r| ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨lower, hlower⟩ := exists_nat_ge
    ((‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1) / 2)
  have hs : ∀ e j, 1 ≤ j → ContDiffOn ℝ ∞ (representatives A B R e j) U := by
    intro e j hj
    cases e with
    | inl b => cases b; exact hA j hj; exact hB j hj
    | inr k => exact hR k j hj
  obtain ⟨a, hlo, hap, had, ham, hat, hao, hab, hatest⟩ :=
    GenericDiagonalSchedule.exists_finite_diagonal_cut_bounds_with_tests hU Subset.rfl hq
      (fun w hw => (hpos w hw).1) Bq hBq hs g L C P hraw hg lower tests Bt Pt γ hγ hq0
  have haReal : Monotone (fun j => (a j : ℝ)) := fun i j hij => by
    change (a i : ℝ) ≤ (a j : ℝ)
    exact_mod_cast ham.monotone hij
  have hapReal : ∀ j, 0 < (a j : ℝ) := fun j => by exact_mod_cast hap j
  have hfirst : ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1 ≤ 2 * (a 0 : ℝ) := by
    have hloR : (lower : ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast hlo
    linarith
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hpos w hw
  have hzero := scale_tendsto U q
  have hgHalf : Monotone (fun j => g j / 2) := fun i j hij => div_le_div_of_nonneg_right (hgmono hij) (by norm_num)
  have hcutA : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q A (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := hab (.inl false)
  have hcutB : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q B (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := hab (.inl true)
  have hcutR : ∀ k, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (R k) (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := fun k => hab (.inr k)
  have hu := velocity_smooth hat hU hq (fun w hw => (hpos w hw).1) hu0
    (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB)
  have hr := fun k => realized_smooth hU hq (fun w hw => (hpos w hw).1) hat (hs0 k) (hR k)
  refine ⟨a, hao, ?_, hatest⟩
  refine ⟨hap, had, ham, hat, ?_, hu, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact SolenoidalDiagonal.locallyFinite_cutStage_support_on hat hq.continuousOn
      (fun w hw => (hpos w hw).1) _
  · intro w hw
    exact positiveVelocity_divergence hat hU hq (fun w hw => (hpos w hw).1) hu0 hA hB hdiv0 hdivB htan hw
  · intro i
    cases i with
    | inl i =>
        exact ⟨velocity_component_approximation hat hU hlU hq (fun w hw => (hpos w hw).1)
          hlq hzero hu0 hA hB g (fun j => g j / 2) L L (CutStageEstimates.cutLoss L)
          (CutStageEstimates.cutLoss L) K0 (C (.inl false)) (P (.inl false)) (C (.inl true)) (P (.inl true))
          (hraw (.inl false)) (hraw (.inl true)) (fun j hj => (hg j hj).le) hgHalf hbaseU hcutA hcutB i⟩
    | inr k =>
        refine ⟨⟨fun m => max (L m + 1) (Ks k m), CutStageEstimates.cutLoss L, id, ?_, ?_⟩⟩
        · intro J m
          exact stage_growth hU hlU hlq hzero (hs0 k) (hR k) (hraw (.inr k))
            (fun j hj => (hg j hj).le) (hbaseS k) J m
        · intro m J hJ
          change m ≤ J at hJ
          exact realized_tail_jetRate hat hU hq (hR k) hgHalf (hcutR k) hlU hlq hzero J m (by omega)
  · intro w hw J m hm hsmall
    exact positiveVelocity_tail_bound hat haReal hapReal hU hq (fun w hw => (hpos w hw).1)
      hA hB hgHalf hcutA hcutB hfirst hw (hpos w hw).2 J m hm hsmall
  · intro k w hw J m hm hsmall
    exact realized_tail_bound hat haReal hapReal hU hq (hR k) hgHalf (hcutR k)
      hw (hpos w hw).1 (hpos w hw).2 J m hm hsmall
  · intro w hqw houter
    exact positiveVelocity_outer_germ haReal hapReal hqw houter u0 A B
  · intro k w hqw houter
    have hz := correction_eventually_zero haReal hapReal hqw houter (CutStageEstimates.positiveStages (R k))
    filter_upwards [hz] with y hy
    simp only [realized, hy, add_zero]

/-- Every finite differential polynomial of the realized physical tuple has
flat residual under the manuscript's finite-stage residual hypothesis.
The coefficient estimates are needed only on each term's common support. -/
theorem Result.flat_residual {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
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
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
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
  exact uniform_bound_of_rate (P.flat_of_local_coefficients hU hlU hlq hu hus hgain hrho
    (fun i => (H.approximation i).some) hconst hc region Lc hcg hzero hszero Lres hres m N)

end NavierStokes.GenericTupleRealization

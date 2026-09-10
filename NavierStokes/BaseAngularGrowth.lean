import NavierStokes.FinalSlowBase

/-!
# Angular growth of the actual slow base

Along a radial ray with fixed positive similarity radius, the normalized
tangential velocity approaches the positive leading angular profile.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace NavierStokes.BaseAngularGrowth

open ProblemStatement

def ray (X τ : ℝ) : Space := Real.sqrt (2 * X * τ) • coordinateVector 0

@[simp] theorem ray_apply_zero (X τ : ℝ) : ray X τ 0 = Real.sqrt (2 * X * τ) := by
  simp [ray, coordinateVector]

@[simp] theorem ray_apply_one (X τ : ℝ) : ray X τ 1 = 0 := by
  simp [ray, coordinateVector]

@[simp] theorem ray_apply_two (X τ : ℝ) : ray X τ 2 = 0 := by
  simp [ray, coordinateVector]

theorem radialEnergy_ray {X τ : ℝ} (hX : 0 ≤ X) (hτ : 0 ≤ τ) :
    AxisymmetricFields.radialEnergy (ray X τ) = X * τ := by
  simp only [AxisymmetricFields.radialEnergy, ray_apply_zero, ray_apply_one, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem physicalQ_ray {h X τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) :
    NaturalCore.physicalQ h (AxisymmetricFields.profilePoint (1 - τ) (ray X τ)) = τ := by
  simp only [AxisymmetricFields.profilePoint, ray_apply_two]
  rw [NaturalCore.physicalQ_at_zero_z hh hh1 (by linarith)]
  ring

theorem cartesianChart_ray {h X τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hX : 0 ≤ X) (hτ : 0 < τ) :
    SlowBorelBase.cartesianChart h (1 - τ, ray X τ) = (τ, (X, 0)) := by
  have hq := physicalQ_ray (X := X) hh hh1 hτ
  change (NaturalCore.physicalQ h (AxisymmetricFields.profilePoint (1 - τ) (ray X τ)),
    (AxisymmetricFields.radialEnergy (ray X τ) /
      NaturalCore.physicalQ h (AxisymmetricFields.profilePoint (1 - τ) (ray X τ)),
      NaturalCore.physicalEta h (AxisymmetricFields.profilePoint (1 - τ) (ray X τ)))) = _
  rw [hq, radialEnergy_ray hX hτ.le, mul_div_cancel_right₀ _ hτ.ne']
  simp [AxisymmetricFields.profilePoint, NaturalCore.physicalEta_at_zero_z]

section Base

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

def leadingAmplitude (X : ℝ) : ℝ := Real.sqrt (2 * X) * v.profiles.f (X, 0)

theorem leadingAmplitude_pos {X : ℝ} (hX : 0 < X) : 0 < leadingAmplitude v X := by
  apply mul_pos (Real.sqrt_pos.mpr (by positivity))
  exact v.positive_f hX (by constructor <;> norm_num)

theorem normalized_velocity_ray (upper : ℝ) (B : ℕ) {X τ : ℝ}
    (hX : 0 < X) (hτ : 0 < τ) :
    τ ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (1 - τ, ray X τ) 1 =
      SlowBorelBase.normalizedSwirl (FinalSlowBase.scales H v upper B)
        F.data.h W.axis.normalization (FinalSlowBase.coefficients H v) (τ, (X, 0)) := by
  have he := SlowBorelBase.angularMoment_eq_normalizedSwirl
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (FinalSlowBase.coefficients_smooth H v) W.axis.normalization
    (t := 1 - τ) (by linarith) (ray X τ)
  rw [ray_apply_zero, ray_apply_one, neg_zero, zero_mul, zero_add,
    radialEnergy_ray hX.le hτ.le, cartesianChart_ray F.data.h_pos F.data.h_lt_half hX.le hτ] at he
  change Real.sqrt (2 * X * τ) * FinalSlowBase.velocity H v upper B (1 - τ, ray X τ) 1 =
    Real.sqrt (2 * (X * τ)) * τ ^ (-CoordinateAlgebra.A F.data.h) *
      SlowBorelBase.normalizedSwirl (FinalSlowBase.scales H v upper B)
        F.data.h W.axis.normalization (FinalSlowBase.coefficients H v) (τ, (X, 0)) at he
  rw [← mul_assoc] at he
  have hsqrt : Real.sqrt (2 * X * τ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have he' := mul_left_cancel₀ hsqrt (he.trans (mul_assoc _ _ _))
  rw [he', ← mul_assoc, ← Real.rpow_add hτ, add_neg_cancel, Real.rpow_zero, one_mul]

theorem normalized_swirl_estimate (upper : ℝ) (B : ℕ) {X : ℝ}
    (hX : 0 < X) (hXhi : X ≤ FinalSlowBase.boxRadius W upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      |SlowBorelBase.normalizedSwirl (FinalSlowBase.scales H v upper B)
        F.data.h W.axis.normalization (FinalSlowBase.coefficients H v) (τ, (X, 0)) -
        leadingAmplitude v X| ≤ C * τ ^ (2 * F.data.h) := by
  obtain ⟨C, hC, hb⟩ := SlowBorelBase.normalized_tangential_bounds F.data.h_pos hX
    (FinalSlowBase.coefficients_smooth H v)
    (FinalSlowBase.scales_admissible_on H v upper B (lo := X) (hi := X) hX.le hXhi) 0
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1
  have hx : (X, (0 : ℝ)) ∈ SlowBorelBase.innerBox X X := by
    constructor
    · exact ⟨le_rfl, le_rfl⟩
    · constructor <;> norm_num
  have he := (hb τ hτ hτ1 (X, 0) hx).1
  have hlead : SlowBorelBase.leadingSwirl W.axis.normalization
      (FinalSlowBase.coefficients H v) (X, 0) = leadingAmplitude v X := by
    unfold SlowBorelBase.leadingSwirl FinalSlowBase.coefficients leadingAmplitude
    rw [(EntranceAlignedBase.modulated_zero_fields H v (p := (X, 0)) hX.le (by norm_num)).1]
    dsimp only
    field_simp [W.axis.normalization_pos.ne']
  simpa only [SlowBorelBase.blownJet, norm_iteratedFDeriv_zero, Function.comp_apply,
    SlowBorelBase.scaleMap_apply, mul_one, hlead, Real.norm_eq_abs] using he

/-- The actual Cartesian velocity has a strictly positive limiting normalized
tangential component at every fixed positive radius in the admitted box. -/
theorem normalized_velocity_ray_bound (upper : ℝ) (B : ℕ) {X : ℝ}
    (hX : 0 < X) (hXhi : X ≤ FinalSlowBase.boxRadius W upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      |τ ^ CoordinateAlgebra.A F.data.h *
        FinalSlowBase.velocity H v upper B (1 - τ, ray X τ) 1 - leadingAmplitude v X| ≤
        C * τ ^ (2 * F.data.h) := by
  obtain ⟨C, hC, hb⟩ := normalized_swirl_estimate H v upper B hX hXhi
  refine ⟨C, hC, fun τ hτ hτ1 => ?_⟩
  rw [normalized_velocity_ray H v upper B hX hτ]
  exact hb τ hτ hτ1

end Base

end NavierStokes.BaseAngularGrowth

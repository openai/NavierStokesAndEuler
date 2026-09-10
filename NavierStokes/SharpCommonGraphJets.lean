import NavierStokes.SharpPhysicalLoss
import NavierStokes.LocalPhysicalCopyBounds

noncomputable section
namespace NavierStokes.SharpCommonGraphJets
open Set Function Filter ProblemStatement
open PhysicalGraphBounds PhysicalWaveSum LocalPhysicalCopyBounds
open scoped ContDiff Topology

theorem common_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ f : PhysicalWaveSum.LiftPoint → E,
      SmoothNear f (commonLift h n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ commonLift h n d) w‖ ≤
        C * A * ChartScales.Q n ^ (-(k : ℝ)*(1+h)) := by
  obtain ⟨G,hG,hgraph⟩ := SharpGraphBounds.physicalLift_positive_jet_bound
    hh ha m
  let C := (m.factorial : ℝ)*G^m*coverBound Δ^m
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m))
      (one_le_pow₀ hG)) (one_le_pow₀ (coverBound_ge_one Δ))
  refine ⟨C,hC,?_⟩
  intro n hn d hd w hw ht f hf A hA hfb k hkm
  have hQ := ChartScales.Q_pos n
  have hcover : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨F,hF,he⟩ := hf.exists_global_germ
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have he' := he.comp_tendsto (commonLift_smoothAt h n d haxis).continuousAt
  rw [iteratedFDeriv_eq_of_eventuallyEq he' k]
  have hFb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (F ∘ downLift d) (physicalLift h n w)‖ ≤
      A*coverBound Δ^m := by
    apply downLift_jet_bound hF hd _ hA
    intro i hi
    change ‖iteratedFDeriv ℝ i F (commonLift h n d w)‖ ≤ A
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hfb i hi
  let U : Set SpaceTime := {w | radialProjection w ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  have hb := SharpPhaseJetAlgebra.composition_geometric_on hU (physicalLift_smooth h n)
    (hF.comp (downLift d).contDiff) haxis m
    (B := A*coverBound Δ^m) (D := G*ChartScales.Q n^(-(1+h))) (by positivity) (by positivity)
    hFb (by
      intro i hi him
      apply (hgraph n hn w hw ht i hi him).trans
      rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le,
        show -(1+h)*(i:ℝ) = -(i:ℝ)*(1+h) by ring]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_right₀ hG hi) (by positivity)) k hkm
  apply hb.trans
  rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  calc
    _ ≤ (m.factorial : ℝ)*(A*coverBound Δ^m)*(G^m*ChartScales.Q n^(-(1+h)*(k:ℝ))) := by
      gcongr
    _ = _ := by
      rw [show -(1+h)*(k:ℝ) = -(k:ℝ)*(1+h) by ring]
      dsimp [C]
      ring

end NavierStokes.SharpCommonGraphJets

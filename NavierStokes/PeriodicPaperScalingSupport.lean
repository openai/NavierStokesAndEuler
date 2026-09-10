import NavierStokes.PeriodicPaperSupport
import NavierStokes.R3.ParabolicDefinitions
import NavierStokes.R3.ParabolicSupport

/-! # Support bounds for the compressed fields used on the torus -/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set

/-- The compressed velocity has the required coordinate bound at every
presingular time, including the negative-time extension used in the lattice sum. -/
theorem compressed_velocity_supported {ν l r : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hl : 0 < l)
    (hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ r) :
    ∀ t < (1 : ℝ), ∀ x : Space,
      NavierStokesR3.ParabolicScaling.velocity l u (t, x) ≠ 0 → ∀ i, |x i| ≤ r := by
  intro t ht x hne
  have hclock := NavierStokesR3.ParabolicScaling.clock_lt_one hl ht
  by_cases ht0 : 0 ≤ NavierStokesR3.ParabolicScaling.clock l t
  · have hu : u (NavierStokesR3.ParabolicScaling.clock l t, l • x) ≠ 0 := by
      intro hz
      apply hne
      simp only [NavierStokesR3.ParabolicScaling.velocity,
        NavierStokesR3.ParabolicScaling.pull,
        NavierStokesR3.ParabolicScaling.zeroBefore, ht0, ite_eq_left, hz, smul_zero]
    apply hK
    refine ⟨l • x, hc.velocity_support _ ⟨ht0, hclock⟩ (subset_tsupport _ hu), ?_⟩
    simp [smul_smul, hl.ne']
  · exfalso
    apply hne
    simp [NavierStokesR3.ParabolicScaling.velocity, NavierStokesR3.ParabolicScaling.pull,
      NavierStokesR3.ParabolicScaling.zeroBefore, ht0]

/-- Pressure has the same fixed coordinate support as the velocity. -/
theorem compressed_pressure_supported {ν l r : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hl : 0 < l)
    (hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ r) :
    ∀ t < (1 : ℝ), ∀ x : Space,
      NavierStokesR3.ParabolicScaling.pressure l p (t, x) ≠ 0 → ∀ i, |x i| ≤ r := by
  intro t ht x hne
  have hclock := NavierStokesR3.ParabolicScaling.clock_lt_one hl ht
  by_cases ht0 : 0 ≤ NavierStokesR3.ParabolicScaling.clock l t
  · have hp : p (NavierStokesR3.ParabolicScaling.clock l t, l • x) ≠ 0 := by
      intro hz
      apply hne
      simp only [NavierStokesR3.ParabolicScaling.pressure,
        NavierStokesR3.ParabolicScaling.pull,
        NavierStokesR3.ParabolicScaling.zeroBefore, ht0, ite_eq_left, hz, smul_zero]
    apply hK
    refine ⟨l • x, hc.pressure_support _ ⟨ht0, hclock⟩ (subset_tsupport _ hp), ?_⟩
    simp [smul_smul, hl.ne']
  · exfalso
    apply hne
    simp [NavierStokesR3.ParabolicScaling.pressure, NavierStokesR3.ParabolicScaling.pull,
      NavierStokesR3.ParabolicScaling.zeroBefore, ht0]

/-- The force has the coordinate support bound uniformly over all times. -/
theorem compressed_force_supported {l r : ℝ} {f : VelocityField}
    (hl : 0 < l)
    (hf : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' (Prod.snd '' tsupport f),
      ∀ i, |x i| ≤ r) :
    SupportedInCube r (NavierStokesR3.ParabolicScaling.force l f) := by
  intro z hz
  have hne : f (NavierStokesR3.ParabolicScaling.clock l z.1, l • z.2) ≠ 0 := by
    intro hfzero
    apply hz
    simp only [NavierStokesR3.ParabolicScaling.force,
      NavierStokesR3.ParabolicScaling.pull, hfzero, smul_zero]
  apply hf
  refine ⟨l • z.2, ⟨(_, l • z.2), subset_tsupport _ hne, rfl⟩, ?_⟩
  simp [smul_smul, hl.ne']

/-- One spatial scaling factor simultaneously compresses the velocity,
pressure, and all spacetime slices of the force into the quarter cube. -/
theorem exists_compression_scale {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K) :
    ∃ l : ℝ, 1 < l ∧
      (fun y : Space => l⁻¹ • y) '' K ⊆ fundamentalInterior ∧
      (∀ t < (1 : ℝ), ∀ x : Space,
        NavierStokesR3.ParabolicScaling.velocity l u (t, x) ≠ 0 →
          ∀ i, |x i| ≤ 1 / 4) ∧
      (∀ t < (1 : ℝ), ∀ x : Space,
        NavierStokesR3.ParabolicScaling.pressure l p (t, x) ≠ 0 →
          ∀ i, |x i| ≤ 1 / 4) ∧
      SupportedInCube (1 / 4) (NavierStokesR3.ParabolicScaling.force l f) := by
  have hcompact : IsCompact (K ∪ Prod.snd '' tsupport f) :=
    hc.support_compact.union (hc.force_support.1.image continuous_snd)
  obtain ⟨l, hl, hbound⟩ :=
    NavierStokesR3.ProblemStatement.exists_spatialScale_into_quarterCube hcompact
  have hlpos : 0 < l := lt_trans zero_lt_one hl
  have hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ (1 / 4 : ℝ) := by
    intro x hx
    exact hbound x ((image_mono subset_union_left) hx)
  have hF : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' (Prod.snd '' tsupport f),
      ∀ i, |x i| ≤ (1 / 4 : ℝ) := by
    intro x hx
    exact hbound x ((image_mono subset_union_right) hx)
  refine ⟨l, hl, ?_, compressed_velocity_supported hc hlpos hK,
    compressed_pressure_supported hc hlpos hK, compressed_force_supported hlpos hF⟩
  intro x hx i
  exact (hK x hx i).trans_lt (by norm_num)

end NavierStokes.PeriodicPaper

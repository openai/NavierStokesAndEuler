import NavierStokes.PeriodicLocalization
import NavierStokes.PeriodizeLatticeCover
import NavierStokes.ResidualRegularity
import NavierStokes.R3.ProblemStatement

/-!
# Navier--Stokes equations under spatial periodization

When the velocity, pressure, and force fit strictly within the fundamental
unit cube, their lattice copies are locally disjoint. At every spacetime
point the periodization agrees locally with a single translated field.
Ordinary derivatives, including the nonlinear advection term, therefore
preserve the whole-space equation at its original viscosity.
-/

noncomputable section

namespace NavierStokes.PeriodicLocalization

open ProblemStatement Set Filter
open scoped BigOperators Topology

variable {V : Type*} [NormedAddCommGroup V]

/-- A lattice shift in the negative direction is also a period. -/
theorem periodize_sub_lattice (f : SpaceTime → V) (t : ℝ) (x : Space) (n : Lattice) :
    periodize f (t, x - lattice n) = periodize f (t, x) := by
  simpa only [sub_add_cancel] using
    (periodize_add_lattice f t (x - lattice n) n).symm

/-- A neighborhood of any translated inner cube contains only that copy. -/
theorem periodize_eventuallyEq_translate {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) {z : SpaceTime} (n : Lattice)
    (hz : z.2 - lattice n ∈ innerCube r) :
    periodize f =ᶠ[𝓝 z] translate f n := by
  have hU : (fun w : SpaceTime => w.2 - lattice n) ⁻¹' innerCube r ∈ 𝓝 z :=
    ((isOpen_innerCube r).preimage (continuous_snd.sub continuous_const)).mem_nhds hz
  filter_upwards [hU] with w hw
  rw [← periodize_sub_lattice f w.1 w.2 n]
  exact periodize_eq_on_innerCube hf hw w.1

variable [NormedSpace ℝ V]

/-- Spatial differentiation commutes with a fixed spatial translation,
including at points where the ordinary derivative is totalized. -/
theorem space_fderiv_translate (f : SpaceTime → V) (n : Lattice) (t : ℝ) (x : Space) :
    fderiv ℝ (fun y : Space => translate f n (t, y)) x =
      fderiv ℝ (fun y : Space => f (t, y)) (x - lattice n) := by
  simpa only [translate, sub_eq_add_neg] using
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Space => f (t, y))
      (x := x) (-lattice n))

theorem temporalDerivative_translate (u : VelocityField) (n : Lattice)
    (t : ℝ) (x : Space) :
    temporalDerivative (translate u n) t x = temporalDerivative u t (x - lattice n) := rfl

theorem spatialDerivative_translate (u : VelocityField) (n : Lattice)
    (t : ℝ) (x : Space) :
    spatialDerivative (translate u n) t x = spatialDerivative u t (x - lattice n) :=
  space_fderiv_translate u n t x

theorem spatialDivergence_translate (u : VelocityField) (n : Lattice)
    (t : ℝ) (x : Space) :
    spatialDivergence (translate u n) t x = spatialDivergence u t (x - lattice n) := by
  simp only [spatialDivergence, spatialDerivative_translate]

theorem advection_translate (u : VelocityField) (n : Lattice)
    (t : ℝ) (x : Space) :
    advection (translate u n) t x = advection u t (x - lattice n) := by
  simp only [advection, spatialDerivative_translate, translate]

theorem pressureGradient_translate (p : PressureField) (n : Lattice)
    (t : ℝ) (x : Space) :
    pressureGradient (translate p n) t x = pressureGradient p t (x - lattice n) := by
  simp only [pressureGradient, space_fderiv_translate]

theorem spatialLaplacian_translate (u : VelocityField) (n : Lattice)
    (t : ℝ) (x : Space) :
    spatialLaplacian (translate u n) t x = spatialLaplacian u t (x - lattice n) := by
  unfold spatialLaplacian
  simp only [spatialDerivative_translate]
  apply Finset.sum_congr rfl
  intro i _
  have h := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun y : Space => spatialDerivative u t y (coordinateVector i))
    (x := x) (-lattice n)
  simpa only [sub_eq_add_neg] using
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) h

/-- The viscosity-dependent equation is covariant under spatial translation. -/
theorem residual_translate (ν : ℝ) (u : VelocityField) (p : PressureField)
    (n : Lattice) (t : ℝ) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν (translate u n) (translate p n) t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - lattice n) := by
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    temporalDerivative_translate, advection_translate,
    spatialLaplacian_translate, pressureGradient_translate]

/-- Locality for the equation at arbitrary viscosity. -/
theorem residual_viscosity_congr (ν : ℝ) {u v : VelocityField} {p q : PressureField}
    {z : SpaceTime} (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p z.1 z.2 =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q z.1 z.2 := by
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [ResidualRegularity.temporalDerivative_congr hu,
    ResidualRegularity.advection_congr hu,
    ResidualRegularity.spatialLaplacian_congr hu,
    ResidualRegularity.pressureGradient_congr hp]

/-- Locality of incompressibility, with no time-boundary differentiation. -/
theorem spatialDivergence_congr {u v : VelocityField} {z : SpaceTime}
    (hu : u =ᶠ[𝓝 z] v) : spatialDivergence u z.1 z.2 = spatialDivergence v z.1 z.2 := by
  simp only [spatialDivergence, ResidualRegularity.spatialDerivative_congr hu]

/-- Lattice periodization preserves incompressibility on any set of times,
including a closed initial-time boundary. -/
theorem divergence_free_periodize {r : ℝ} {u : VelocityField} {times : Set ℝ}
    (hu : SupportedInCube r u) (hr : r < 1 / 2)
    (hdiv : ∀ t ∈ times, ∀ x : Space, spatialDivergence u t x = 0) :
    ∀ t ∈ times, ∀ x : Space, spatialDivergence (periodize u) t x = 0 := by
  intro t ht x
  obtain ⟨n, hn⟩ := exists_lattice_near x
  have hx : x - lattice n ∈ innerCube r := by
    intro i
    have := hn i
    linarith
  rw [spatialDivergence_congr (periodize_eventuallyEq_translate hu (z := (t, x)) n hx),
    spatialDivergence_translate]
  exact hdiv t ht (x - lattice n)

/-- The actual lattice sums satisfy the same forced Navier--Stokes equation
at the same viscosity throughout every prescribed set of times. -/
theorem navier_stokes_periodize {r ν : ℝ} {u f : VelocityField} {p : PressureField}
    {times : Set ℝ} (hu : SupportedInCube r u) (hp : SupportedInCube r p)
    (hf : SupportedInCube r f) (hr : r < 1 / 2)
    (hNS : ∀ t ∈ times, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    ∀ t ∈ times, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (periodize u) (periodize p) t x = periodize f (t, x) := by
  intro t ht x
  obtain ⟨n, hn⟩ := exists_lattice_near x
  have hx : x - lattice n ∈ innerCube r := by
    intro i
    have := hn i
    linarith
  have hfu := periodize_eventuallyEq_translate hu (z := (t, x)) n hx
  have hfp := periodize_eventuallyEq_translate hp (z := (t, x)) n hx
  have hff := periodize_eventuallyEq_translate hf (z := (t, x)) n hx
  rw [residual_viscosity_congr ν hfu hfp, residual_translate, hNS t ht]
  exact hff.self_of_nhds.symm

end NavierStokes.PeriodicLocalization

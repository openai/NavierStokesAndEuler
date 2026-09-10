import NavierStokes.PeriodicViscosityUniqueness
import NavierStokes.MaximalLifespan

/-!
# Global exclusion for positive-viscosity periodic solutions

Periodic classical uniqueness identifies any global competitor with a given
pre-singular solution on every compact interval before time one. Uniform
boundedness of the global competitor then contradicts unbounded speed.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.PeriodicViscosity

open ProblemStatement

/-- A smooth periodic solution with unbounded speed at time one excludes every
global smooth periodic solution with the same positive viscosity, force and
zero initial datum. No kinetic-energy assumption is imposed on the competitor. -/
theorem excludes_global_solution {ν : ℝ} (hν : 0 < ν)
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hpu : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (huzero : ∀ x : Space, u (0, x) = 0)
    (hdu : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hNSu : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hblow : SpeedUnboundedAtOne u)
    (hv : ContDiffOn ℝ ∞ v futureDomain)
    (hq : ContDiffOn ℝ ∞ q futureDomain)
    (hpv : UnitSpatialPeriodsOn (Ici (0 : ℝ)) v)
    (hpq : UnitSpatialPeriodsOn (Ici (0 : ℝ)) q)
    (hvzero : ∀ x : Space, v (0, x) = 0)
    (hdv : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t : ℝ, 0 < t → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x = f (t, x)) :
    False := by
  apply MaximalLifespan.unbounded_excludes_continuous_extension hblow
    (hv.continuousOn.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
  · intro t ht x i
    exact hpv t ht.1 x i
  · intro t ht x
    have hsubu : PeriodicUniqueness.slab 0 t ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
    have hsubv : PeriodicUniqueness.slab 0 t ⊆ futureDomain := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have hagree : ∀ r ∈ Icc (0 : ℝ) t, ∀ y : Space, u (r, y) = v (r, y) := by
      apply PeriodicViscosityUniqueness.classical_uniqueness_on_Icc hν
        (hu.mono hsubu) (hv.mono hsubv) (hp.mono hsubu) (hq.mono hsubv)
      · intro r hr y i
        exact hpu r ⟨hr.1, hr.2.trans_lt ht.2⟩ y i
      · intro r hr y i
        exact hpv r hr.1 y i
      · intro r hr y i
        exact hpp r ⟨hr.1, hr.2.trans_lt ht.2⟩ y i
      · intro r hr y i
        exact hpq r hr.1 y i
      · intro r hr y
        exact hdu r ⟨hr.1.le, hr.2.trans ht.2⟩ y
      · intro r hr y
        exact hdv r hr.1.le y
      · intro r hr y
        exact hNSu r ⟨hr.1, hr.2.trans ht.2⟩ y
      · intro r hr y
        exact hNSv r hr.1 y
      · intro y
        exact (huzero y).trans (hvzero y).symm
    exact hagree t ⟨ht.1, le_rfl⟩ x

end NavierStokes.PeriodicViscosity

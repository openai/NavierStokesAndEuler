import NavierStokes.R3.DelayedExtension
import NavierStokes.R3.ViscosityScaling

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open ProblemStatement Set

/-- The affine clock sends time one to itself and starts at `1-l⁻²`. -/
def clock (l t : ℝ) : ℝ := l ^ 2 * (t - 1) + 1

/-- Simultaneous affine time change, spatial dilation, and amplitude change. -/
def pull {V : Type*} [SMul ℝ V] (a l : ℝ) (g : SpaceTime → V) : SpaceTime → V :=
  fun z => a • g (clock l z.1, l • z.2)

def velocity (l : ℝ) (u : VelocityField) : VelocityField :=
  pull l l (zeroBefore u)

def pressure (l : ℝ) (p : PressureField) : PressureField :=
  pull (l ^ 2) l (zeroBefore p)

def force (l : ℝ) (f : VelocityField) : VelocityField :=
  pull (l ^ 3) l f

theorem clock_lt_one {l t : ℝ} (hl : 0 < l) (ht : t < 1) : clock l t < 1 := by
  dsimp [clock]
  nlinarith [sq_pos_of_pos hl]

theorem clock_zero_nonpos {l : ℝ} (hl : 1 ≤ l) : clock l 0 ≤ 0 := by
  dsimp [clock]
  nlinarith

end NavierStokesR3.ParabolicScaling

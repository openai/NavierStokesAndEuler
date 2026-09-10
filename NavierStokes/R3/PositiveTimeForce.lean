import NavierStokes.R3.ProblemStatement
import NavierStokes.SmoothCutoffs

/-!
# A smooth force cutoff separated from initial time

The cutoff equals one throughout `[3/8, 1]`, and its support is contained
in `[1/16, 21/16]`. Thus a force with a fixed compact spatial support can
be extended to a compactly supported force in strictly positive spacetime.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NavierStokesR3.PositiveTimeForce

open ProblemStatement

def timeCutoff (t : ℝ) : ℝ :=
  NavierStokes.SmoothCutoffs.cutoff ((8 / 5 : ℝ) * (t - 11 / 16))

theorem timeCutoff_contDiff : ContDiff ℝ ∞ timeCutoff :=
  NavierStokes.SmoothCutoffs.cutoff_contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem timeCutoff_eq_one {t : ℝ} (ht : t ∈ Icc (3 / 8 : ℝ) 1) :
    timeCutoff t = 1 := by
  apply NavierStokes.SmoothCutoffs.cutoff_one_of_abs_le
  rw [abs_le]
  constructor <;> nlinarith [ht.1, ht.2]

theorem timeCutoff_eq_zero {t : ℝ} (ht : t ∉ Icc (1 / 16 : ℝ) (21 / 16)) :
    timeCutoff t = 0 := by
  apply NavierStokes.SmoothCutoffs.cutoff_zero_of_one_le_abs
  rcases not_and_or.mp ht with h | h
  · have hlt : t < 1 / 16 := lt_of_not_ge h
    have hn : (8 / 5 : ℝ) * (t - 11 / 16) ≤ -1 := by linarith
    exact (by linarith : (1 : ℝ) ≤ -((8 / 5 : ℝ) * (t - 11 / 16))).trans
      (neg_le_abs _)
  · have hgt : 21 / 16 < t := lt_of_not_ge h
    exact (by linarith : (1 : ℝ) ≤ (8 / 5 : ℝ) * (t - 11 / 16)).trans
      (le_abs_self _)

def force (f : VelocityField) : VelocityField :=
  fun z => timeCutoff z.1 • f z

theorem force_contDiff {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (force f) :=
  (timeCutoff_contDiff.comp contDiff_fst).smul hf

theorem force_eq {f : VelocityField} {t : ℝ}
    (ht : t ∈ Icc (3 / 8 : ℝ) 1) (x : Space) : force f (t, x) = f (t, x) := by
  simp only [force, timeCutoff_eq_one ht, one_smul]

theorem force_eq_zero {f : VelocityField} {t : ℝ} {x : Space}
    (hf : f (t, x) = 0) : force f (t, x) = 0 := by
  simp only [force, hf, smul_zero]

theorem force_tsupport_subset {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    tsupport (force f) ⊆ Icc (1 / 16 : ℝ) (21 / 16) ×ˢ K := by
  apply closure_minimal _ (isClosed_Icc.prod hK.isClosed)
  rintro ⟨t, x⟩ hz
  constructor
  · by_contra ht
    exact hz (by simp only [force, timeCutoff_eq_zero ht, zero_smul])
  · by_contra hx
    exact hz (force_eq_zero (hf t x hx))

theorem force_compactPositiveTimeSupport {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    CompactPositiveTimeSupport (force f) := by
  have hs := force_tsupport_subset hK hf
  constructor
  · exact (isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hs
  · intro z hz
    have ht := (hs hz).1.1
    exact ⟨by change 0 < z.1; linarith, mem_univ _⟩

end NavierStokesR3.PositiveTimeForce

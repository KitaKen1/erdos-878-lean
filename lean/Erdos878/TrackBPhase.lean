import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Track B: derivatives of the reciprocal-logarithm phase

These are actual derivatives of `a / log(n*x)` on the positive domain `n*x > 1`.
The same formula is supplied for the difference phase used after Cauchy--Schwarz.
No assertion about cancellation of a finite exponential sum is made in this module.
-/

namespace Erdos878.TrackB
open Set Filter
open scoped Topology
noncomputable section

def reciprocalLogPhase (a n x : ℝ) : ℝ := a / Real.log (n * x)

def reciprocalLogSlope (a n x : ℝ) : ℝ := -a / (x * Real.log (n * x) ^ 2)

def logCurvature (z : ℝ) : ℝ := 1 / z ^ 2 + 2 / z ^ 3

def logCurvatureRate (z : ℝ) : ℝ := 2 / z ^ 3 + 6 / z ^ 4

def reciprocalLogCorrelation (a n₁ n₂ x : ℝ) : ℝ :=
  reciprocalLogPhase a n₁ x - reciprocalLogPhase a n₂ x

theorem hasDerivAt_log_mul (n x : ℝ) (hn : n ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ Real.log (n * y)) (1 / x) x := by
  have h := ((hasDerivAt_id x).const_mul n).log (mul_ne_zero hn hx)
  convert h using 1 <;> first | rfl | (dsimp only [id_eq]; field_simp)

theorem hasDerivAt_reciprocalLogPhase (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    HasDerivAt (reciprocalLogPhase a n) (reciprocalLogSlope a n x) x := by
  have hl : Real.log (n * x) ≠ 0 := (Real.log_pos hnx).ne'
  have h := (hasDerivAt_const x a).div (hasDerivAt_log_mul n x hn.ne' hx.ne') hl
  convert h using 1 <;> first | rfl | (unfold reciprocalLogSlope; ring)

theorem hasDerivAt_reciprocalLogSlope (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    HasDerivAt (reciprocalLogSlope a n)
      (a / x ^ 2 * logCurvature (Real.log (n * x))) x := by
  have hl : Real.log (n * x) ≠ 0 := (Real.log_pos hnx).ne'
  have hden := (hasDerivAt_id x).mul ((hasDerivAt_log_mul n x hn.ne' hx.ne').pow 2)
  have h := (hasDerivAt_const x (-a)).div hden (mul_ne_zero hx.ne' (pow_ne_zero 2 hl))
  convert h using 1 <;> first | rfl |
    (unfold logCurvature; dsimp; field_simp; ring)

/-- The derivative of the actual derivative, rather than just a formal slope expression. -/
theorem hasDerivAt_deriv_reciprocalLogPhase (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    HasDerivAt (deriv (reciprocalLogPhase a n))
      (a / x ^ 2 * logCurvature (Real.log (n * x))) x := by
  apply (hasDerivAt_reciprocalLogSlope a n x hn hx hnx).congr_of_eventuallyEq
  have hprod : ∀ᶠ y in 𝓝 x, 1 < n * y :=
    (continuousAt_const.mul continuousAt_id).eventually_const_lt hnx
  filter_upwards [eventually_gt_nhds hx, hprod] with y hy hny
  exact (hasDerivAt_reciprocalLogPhase a n y hn hy hny).deriv

theorem deriv2_reciprocalLogPhase (a n x : ℝ) (hn : 0 < n)
    (hx : 0 < x) (hnx : 1 < n * x) :
    deriv (deriv (reciprocalLogPhase a n)) x =
      a / x ^ 2 * logCurvature (Real.log (n * x)) :=
  (hasDerivAt_deriv_reciprocalLogPhase a n x hn hx hnx).deriv

theorem deriv2_reciprocalLogCorrelation (a n₁ n₂ x : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hx : 0 < x)
    (hprod₁ : 1 < n₁ * x) (hprod₂ : 1 < n₂ * x) :
    deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x =
      a / x ^ 2 * (logCurvature (Real.log (n₁ * x)) -
        logCurvature (Real.log (n₂ * x))) := by
  have hs := (hasDerivAt_reciprocalLogSlope a n₁ x hn₁ hx hprod₁).sub
    (hasDerivAt_reciprocalLogSlope a n₂ x hn₂ hx hprod₂)
  have heq : deriv (reciprocalLogCorrelation a n₁ n₂) =ᶠ[𝓝 x]
      (fun y ↦ reciprocalLogSlope a n₁ y - reciprocalLogSlope a n₂ y) := by
    have hp₁ : ∀ᶠ y in 𝓝 x, 1 < n₁ * y :=
      (continuousAt_const.mul continuousAt_id).eventually_const_lt hprod₁
    have hp₂ : ∀ᶠ y in 𝓝 x, 1 < n₂ * y :=
      (continuousAt_const.mul continuousAt_id).eventually_const_lt hprod₂
    filter_upwards [eventually_gt_nhds hx, hp₁, hp₂] with y hy h₁ h₂
    exact ((hasDerivAt_reciprocalLogPhase a n₁ y hn₁ hy h₁).sub
      (hasDerivAt_reciprocalLogPhase a n₂ y hn₂ hy h₂)).deriv
  rw [heq.deriv_eq]
  calc
    _ = a / x ^ 2 * logCurvature (Real.log (n₁ * x)) -
        a / x ^ 2 * logCurvature (Real.log (n₂ * x)) := hs.deriv
    _ = _ := by ring

theorem hasDerivAt_logCurvature (z : ℝ) (hz : 0 < z) :
    HasDerivAt logCurvature (-logCurvatureRate z) z := by
  have h₂ := (hasDerivAt_const z (1 : ℝ)).div ((hasDerivAt_id z).pow 2)
    (pow_ne_zero 2 hz.ne')
  have h₃ := (hasDerivAt_const z (2 : ℝ)).div ((hasDerivAt_id z).pow 3)
    (pow_ne_zero 3 hz.ne')
  convert h₂.add h₃ using 1 <;> first | rfl |
    (unfold logCurvatureRate; dsimp; field_simp; ring)

theorem logCurvatureRate_pos (z : ℝ) (hz : 0 < z) : 0 < logCurvatureRate z := by
  unfold logCurvatureRate
  positivity

theorem logCurvature_strictAntiOn : StrictAntiOn logCurvature (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro z hz
    exact (hasDerivAt_logCurvature z hz).continuousAt.continuousWithinAt
  · intro z hz
    have hzpos : 0 < z := interior_subset hz
    rw [(hasDerivAt_logCurvature z hzpos).deriv]
    exact neg_neg_of_pos (logCurvatureRate_pos z hzpos)

end
end Erdos878.TrackB

import Erdos878.TrackBExponentialPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Track B: discrete first-derivative cancellation

The elementary Kusmin--Landau route: reciprocal phase increments lie on a vertical
line, so their total variation telescopes when the increments are monotone.
This file does not assume an exponential-sum estimate as a hypothesis.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

theorem phaseCharacter_add (s t : ℝ) :
    phaseCharacter (s + t) = phaseCharacter s * phaseCharacter t := by
  unfold phaseCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def phaseResolvent (t : ℝ) : ℂ := (1 - phaseCharacter t)⁻¹

def halfCotPhase (t : ℝ) : ℝ := Real.cos (Real.pi * t) / (2 * Real.sin (Real.pi * t))

theorem sin_pi_pos_of_unit (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < Real.sin (Real.pi * t) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht)
    (by nlinarith [Real.pi_pos])

theorem norm_one_sub_phaseCharacter (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ‖1 - phaseCharacter t‖ = 2 * Real.sin (Real.pi * t) := by
  rw [norm_sub_rev]
  unfold phaseCharacter
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [he, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num)
    (sin_pi_pos_of_unit t ht ht1))]

theorem one_sub_phaseCharacter_ne_zero (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    1 - phaseCharacter t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_one_sub_phaseCharacter t ht ht1]
  exact mul_pos (by norm_num) (sin_pi_pos_of_unit t ht ht1)

/-- The real part of the reciprocal increment is exactly one half. -/
theorem phaseResolvent_eq (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    phaseResolvent t = (1 / 2 : ℂ) + (halfCotPhase t : ℂ) * Complex.I := by
  have hs := (sin_pi_pos_of_unit t ht ht1).ne'
  have he : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
  apply (mul_eq_one_iff_inv_eq₀ (one_sub_phaseCharacter_ne_zero t ht ht1)).mp
  unfold phaseCharacter halfCotPhase
  rw [Complex.exp_ofReal_mul_I, he, Real.cos_two_mul, Real.sin_two_mul]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, zero_add, mul_one, sub_zero, zero_sub]
  all_goals field_simp
  all_goals
    have hcircle := Real.sin_sq_add_cos_sq (Real.pi * t)
    have hprod := congrArg (fun r : ℝ => Real.cos (Real.pi * t) * r) hcircle
    nlinarith

theorem halfCotPhase_antitone (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    halfCotPhase t ≤ halfCotPhase s := by
  have hs1 : s < 1 := hst.trans_lt ht
  have ht0 : 0 < t := hs.trans_le hst
  have hsin_s := sin_pi_pos_of_unit s hs hs1
  have hsin_t := sin_pi_pos_of_unit t ht0 ht
  have hd : 0 ≤ Real.sin (Real.pi * t - Real.pi * s) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  unfold halfCotPhase
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem two_mul_le_sin_pi (δ t : ℝ) (hδ : 0 < δ) (hlo : δ ≤ t) (hhi : t ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * t) := by
  have hpi := Real.pi_pos
  have ht0 : 0 < t := hδ.trans_le hlo
  by_cases ht : t ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith)
    have he : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rw [he] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - t)) (by nlinarith) (by nlinarith)
    have he : 2 / Real.pi * (Real.pi * (1 - t)) = 2 * (1 - t) := by field_simp
    rw [he, show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
      Real.sin_pi_sub] at h
    linarith

theorem norm_phaseResolvent_le (δ t : ℝ) (hδ : 0 < δ)
    (hlo : δ ≤ t) (hhi : t ≤ 1 - δ) : ‖phaseResolvent t‖ ≤ 1 / (4 * δ) := by
  have ht0 := hδ.trans_le hlo
  have ht1 : t < 1 := by linarith
  rw [phaseResolvent, norm_inv, norm_one_sub_phaseCharacter t ht0 ht1, ← one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith [two_mul_le_sin_pi δ t hδ hlo hhi]

end
end Erdos878.TrackB

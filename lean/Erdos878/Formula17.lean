import Erdos878FC

/-!
# The original formula (17)

The integer-base surplus bound already gives the required pointwise upper estimate for `f`.
Chebyshev's elementary lower bound supplies `h`. A finite-maximum transfer avoids proving
monotonicity of the iterated-log error envelope or selecting a special maximizing endpoint.
This module concerns the original divergence, not the stronger coefficient-one liminf claim.
-/

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

/-- A finite, rounded version of the prime-counting/product-budget construction. -/
theorem log_div_log_sub_one_le_h
    {X Y : ℕ} (hX : 0 < X) (hY : 1 < Y)
    (hnum : Real.log (X : ℝ) ≤
      (Y : ℝ) * Real.log 2 - Real.log ((Y : ℝ) + 1)) :
    Real.log (X : ℝ) / Real.log (Y : ℝ) - 1 ≤ (h X : ℝ) := by
  have hT : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hL : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  let k := Nat.floor (Real.log (X : ℝ) / Real.log (Y : ℝ))
  have hk : (k : ℝ) ≤ Real.log (X : ℝ) / Real.log (Y : ℝ) :=
    Nat.floor_le (div_nonneg hT hL.le)
  have hkH : k ≤ h X := h_ge_of_chebyshev_pi_lower_of_log_budget hX hY
    (hk.trans (div_le_div_of_nonneg_right hnum hL.le))
    ((le_div_iff₀ hL).mp hk)
  have hfloor := Nat.lt_floor_add_one (Real.log (X : ℝ) / Real.log (Y : ℝ))
  have hkHreal : (k : ℝ) ≤ (h X : ℝ) := by exact_mod_cast hkH
  dsimp [k] at hkHreal
  linarith

/-- A deliberately loose additive constant suffices; no prime number theorem is used. -/
theorem eventually_h_ge_log_div_loglog_add_four :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) / (Real.log (Real.log (X : ℝ)) + 4) - 1 ≤ (h X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let Y : ℕ → ℕ := fun X ↦ Nat.ceil (4 * Real.log (X : ℝ))
  have hYtop : Tendsto (fun X ↦ (Y X : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun X ↦ Nat.le_ceil (4 * Real.log (X : ℝ)))
      (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hsmall : ∀ᶠ y : ℝ in atTop, Real.log (y + 1) ≤ y / 4 := by
    have hlim : Tendsto (fun y : ℝ ↦ Real.log (y + 1) / y) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, pow_one, one_mul, add_neg_cancel_right] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
          (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_gt_atTop (0 : ℝ)] with y hy hypos
    have := (div_le_iff₀ hypos).mp hy
    linarith
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hYtop.eventually hsmall, eventually_gt_atTop (0 : ℕ)] with X hT hsmall hX
  have hTpos : 0 < Real.log (X : ℝ) := by linarith
  have hYlo : 4 * Real.log (X : ℝ) ≤ (Y X : ℝ) := Nat.le_ceil _
  have hYpos : 0 < (Y X : ℝ) := by linarith
  have hYone : 1 < Y X := by exact_mod_cast (show (1 : ℝ) < (Y X : ℝ) by linarith)
  have hYhi : (Y X : ℝ) ≤ 5 * Real.log (X : ℝ) := by
    have hh : (Y X : ℝ) < 4 * Real.log (X : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hnum : Real.log (X : ℝ) ≤
      (Y X : ℝ) * Real.log 2 - Real.log ((Y X : ℝ) + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogtwo hYpos.le]
  have hLY : 0 < Real.log (Y X : ℝ) := Real.log_pos (by exact_mod_cast hYone)
  have hLupper : Real.log (Y X : ℝ) ≤ Real.log (Real.log (X : ℝ)) + 4 := by
    have h5 : Real.log (5 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
      linarith
    calc
      Real.log (Y X : ℝ) ≤ Real.log (5 * Real.log (X : ℝ)) :=
        Real.log_le_log hYpos hYhi
      _ = Real.log 5 + Real.log (Real.log (X : ℝ)) :=
        Real.log_mul (by norm_num) hTpos.ne'
      _ ≤ Real.log (Real.log (X : ℝ)) + 4 := by linarith
  have hdiv : Real.log (X : ℝ) / (Real.log (Real.log (X : ℝ)) + 4) ≤
      Real.log (X : ℝ) / Real.log (Y X : ℝ) :=
    div_le_div_of_nonneg_left hTpos.le hLY hLupper
  exact (sub_le_sub_right hdiv 1).trans (log_div_log_sub_one_le_h hX hYone hnum)

/-- The third logarithm eventually absorbs all fixed error constants. -/
theorem report_gap_ge_log_div_loglog_sq
    {T v : ℝ} (hT : 0 ≤ T) (hv : 4 ≤ v) (hl : 108 ≤ Real.log v) :
    T / v ^ 2 - 1 ≤
      T / (v + 4) - 1 - (T / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2) := by
  have hvpos : 0 < v := by linarith
  have hlv : Real.log v ≤ v := Real.log_le_self hvpos.le
  have hd : 0 < v + 4 := by positivity
  have he : 0 < v + Real.log v := by linarith
  have hden : (v + 4) * (v + Real.log v) ≤ 4 * v ^ 2 := by
    have := mul_le_mul (show v + 4 ≤ 2 * v by linarith)
      (show v + Real.log v ≤ 2 * v by linarith) he.le (by positivity : 0 ≤ 2 * v)
    nlinarith
  have hfrac : 26 * T / v ^ 2 ≤ T * (Real.log v - 4) / ((v + 4) * (v + Real.log v)) := by
    calc
      26 * T / v ^ 2 = T * 104 / (4 * v ^ 2) := by ring
      _ ≤ T * (Real.log v - 4) / ((v + 4) * (v + Real.log v)) := by
        apply div_le_div₀ (mul_nonneg hT (by linarith))
        · exact mul_le_mul_of_nonneg_left (by linarith) hT
        · exact mul_pos hd he
        · exact hden
  have hid : T / (v + 4) - T / (v + Real.log v) =
      T * (Real.log v - 4) / ((v + 4) * (v + Real.log v)) := by
    field_simp [hd.ne', he.ne']
    ring
  have hsmall : T / v ^ 3 ≤ T / v ^ 2 := by
    apply div_le_div_of_nonneg_left hT (by positivity)
    calc
      v ^ 2 = v ^ 2 * 1 := by ring
      _ ≤ v ^ 2 * v := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg v)
      _ = v ^ 3 := by ring
  rw [← hid] at hfrac
  have h24 : 24 * T / v ^ 2 = 24 * (T / v ^ 2) := by ring
  have h26 : 26 * T / v ^ 2 = 26 * (T / v ^ 2) := by ring
  rw [h26] at hfrac
  rw [h24]
  linarith

/-- Pointwise divergence relative to the distinct-prime-factor maximum. -/
theorem tendsto_h_sub_f_div_atTop :
    Tendsto (fun n : ℕ ↦ (h n : ℝ) - (f n : ℝ) / (n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hthird : Tendsto (fun n : ℕ ↦ Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hv
  have hratio : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2) atTop atTop := by
    have hexp := (Real.tendsto_exp_div_pow_atTop 2).comp hv
    refine hexp.congr' ?_
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    simp only [Function.comp_def, Real.exp_log hn]
  have hlower : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2 - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hratio
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [eventually_h_ge_log_div_loglog_add_four,
    eventually_f_div_le_report_bound_of_tight_scalar,
    hlog.eventually (eventually_ge_atTop (0 : ℝ)),
    hv.eventually (eventually_ge_atTop (4 : ℝ)),
    hthird.eventually (eventually_ge_atTop (108 : ℝ))] with n hlow hu hT hV hthird
  exact (report_gap_ge_log_div_loglog_sq hT hV hthird).trans (sub_le_sub hlow hu)

/-- A pointwise deficit tending to infinity survives taking the finite maximum of `f`.
The finitely many small inputs are absorbed using `h(X) → ∞`. -/
theorem tendsto_maximalOrderGap_div_self_of_pointwise
    (hpoint : Tendsto (fun n : ℕ ↦ (h n : ℝ) - (f n : ℝ) / (n : ℝ)) atTop atTop) :
    Tendsto (fun X : ℕ ↦ (maximalOrderGap X : ℝ) / (X : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpoint.eventually (eventually_ge_atTop B))
  have hH : Tendsto (fun X : ℕ ↦ (h X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_h_atTop
  filter_upwards [hH.eventually (eventually_ge_atTop (B + (m N : ℝ))),
    eventually_gt_atTop (0 : ℕ)] with X hHX hX
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hcoef : 0 ≤ (h X : ℝ) - B := by
    have : 0 ≤ (m N : ℝ) := by positivity
    linarith
  have hm : (m X : ℝ) ≤ (X : ℝ) * ((h X : ℝ) - B) := by
    apply maxUpTo_le_of_pointwise_real f X
    intro n hnX
    by_cases hnlarge : N ≤ n ∧ n ≠ 0
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnlarge.2
      have hpn := hN n hnlarge.1
      have hf : (f n : ℝ) ≤ (n : ℝ) * ((h n : ℝ) - B) := by
        have hdiv : (f n : ℝ) / (n : ℝ) ≤ (h n : ℝ) - B := by linarith
        simpa only [mul_comm] using (div_le_iff₀ hnpos).mp hdiv
      have hmono : (h n : ℝ) ≤ (h X : ℝ) := by
        exact_mod_cast (maxUpTo_mono (g := omega) hnX)
      exact hf.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right hmono B) hnpos.le).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hnX) hcoef))
    · have hnN : n ≤ N := by omega
      have hfN : (f n : ℝ) ≤ (m N : ℝ) := by exact_mod_cast f_le_maxUpTo hnN
      have hmcoef : (m N : ℝ) ≤ (h X : ℝ) - B := by linarith
      have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      exact hfN.trans (hmcoef.trans (by nlinarith [mul_le_mul_of_nonneg_right hXone hcoef]))
  have hgap : (maximalOrderGap X : ℝ) = (X : ℝ) * (h X : ℝ) - (m X : ℝ) := by
    rw [maximalOrderGap, Nat.cast_sub (m_le_mul_h X), Nat.cast_mul]
  rw [hgap, le_div_iff₀ hXpos]
  nlinarith

/-- Complete proof of the original formula (17), at natural-number endpoints. -/
theorem original_formula_17_proved : erdos_878.variants.original_formula_17 :=
  original_formula_17_of_bound
    (tendsto_maximalOrderGap_div_self_of_pointwise tendsto_h_sub_f_div_atTop)

end Erdos878

#print axioms Erdos878.eventually_f_div_le_report_bound_of_tight_scalar
#print axioms Erdos878.original_formula_17_proved

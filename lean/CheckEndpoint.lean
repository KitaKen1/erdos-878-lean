import Erdos878.RelaxedBound

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

theorem eventually_report_endpoint_exp_le_nat :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.log (Real.log (n : ℝ)) +
        Real.log (Real.log (Real.log (n : ℝ)))) ≤ (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hTpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
    hlog.eventually (eventually_gt_atTop (0 : ℝ))
  have hv : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hvpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Real.log (n : ℝ)) :=
    hv.eventually (eventually_gt_atTop (0 : ℝ))
  have hsq : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ≤ 1 := by
    have hlim : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (hlim.comp hn).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hTpos, hvpos, hsq] with n hn hnv hsqn
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  have hlogle : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_self (le_of_lt hn)
  have hprod : Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      (Real.log (n : ℝ)) ^ 2 := by
    simpa [pow_two] using
      (mul_le_mul_of_nonneg_left hlogle (le_of_lt hn))
  have hsq' : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hn1 : 1 < (n : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp hn
    have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
    have h := (div_le_iff₀ hnpos).mp hsqn
    simpa using h
  calc
    Real.exp (Real.log (Real.log (n : ℝ)) +
        Real.log (Real.log (Real.log (n : ℝ)))) =
      Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
        rw [Real.exp_add, Real.exp_log hn, Real.exp_log hnv]
    _ ≤ (Real.log (n : ℝ)) ^ 2 := hprod
    _ ≤ (n : ℝ) := hsq'

end Erdos878

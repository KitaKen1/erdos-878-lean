import Erdos878.GoodPair
import Erdos878.PrimeMass

/-!
# The good-pair construction at the report scale

The elementary width and exponent-budget assumptions in `GoodPair` hold uniformly over both
prime windows for all large report parameters. The target may be any `n` with `log n ≥ T/2`.
Thus the statement applies throughout the large part of a block with `T = log X`.
-/

open Classical Filter
open scoped Topology Real

namespace Erdos878

theorem eventually_report_good_pair_width {β δ rho : ℝ}
    (hδ : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      8 * T ^ β ≤ rho * (reportApproximationScale T δ : ℝ) := by
  have hlim : Tendsto (fun T : ℝ ↦ T ^ β / T ^ (1 - δ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_add_div_rpow_zero (a := 1 - δ) (b := β) (C := 0)
      (by linarith) (by linarith))
  filter_upwards [hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < rho / 128)),
    eventually_rpow_div_sixteen_le_reportApproximationScale hδ,
    eventually_gt_atTop (0 : ℝ)] with T hsmall hfloor hT
  have hpowpos : 0 < T ^ (1 - δ) := Real.rpow_pos_of_pos hT _
  have hsmall' := (div_le_iff₀ hpowpos).mp hsmall
  have hscaled := mul_le_mul_of_nonneg_left hfloor hrho.le
  calc
    8 * T ^ β ≤ 8 * (rho / 128 * T ^ (1 - δ)) :=
      mul_le_mul_of_nonneg_left hsmall' (by norm_num)
    _ = rho * (T ^ (1 - δ) / 16) := by ring
    _ ≤ rho * (reportApproximationScale T δ : ℝ) := hscaled

theorem eventually_report_good_pair_budget {β δ : ℝ} (hβ : β < 1) (hδ : δ < 1) :
    ∀ᶠ T : ℝ in atTop,
      ((reportApproximationScale T δ : ℝ) + 1) * T ^ δ + 3 * T ^ β ≤ T / 2 := by
  have hlimβ : Tendsto (fun T : ℝ ↦ T ^ β / T) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_add_div_rpow_zero (a := 1) (b := β) (C := 0)
      (by norm_num) hβ)
  have hlimδ : Tendsto (fun T : ℝ ↦ T ^ δ / T) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_add_div_rpow_zero (a := 1) (b := δ) (C := 0)
      (by norm_num) hδ)
  filter_upwards [hlimβ.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 24)),
    hlimδ.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_gt_atTop (0 : ℝ)] with T hβsmall hδsmall hT
  have hβbound := (div_le_iff₀ hT).mp hβsmall
  have hδbound := (div_le_iff₀ hT).mp hδsmall
  have hMupper : (reportApproximationScale T δ : ℝ) ≤ T ^ (1 - δ) / 8 :=
    Nat.floor_le (div_nonneg (Real.rpow_nonneg hT.le _) (by norm_num))
  have hMprod : (reportApproximationScale T δ : ℝ) * T ^ δ ≤ T / 8 := by
    calc
      (reportApproximationScale T δ : ℝ) * T ^ δ ≤ (T ^ (1 - δ) / 8) * T ^ δ :=
        mul_le_mul_of_nonneg_right hMupper (Real.rpow_pos_of_pos hT _).le
      _ = (T ^ (1 - δ) * T ^ δ) / 8 := by ring
      _ = T / 8 := by rw [← Real.rpow_add hT, sub_add_cancel, Real.rpow_one]
  nlinarith

/-- Uniform construction over both windows, including positive exponents.
The only pair-specific condition is exclusion from the exact bad-pair finset. -/
theorem eventually_exists_positive_power_product_of_report_good_pair
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ p ∈ primeWindow T α β, ∀ q ∈ primeWindow T γ δ, ∀ n : ℕ,
      T / 2 ≤ Real.log (n : ℝ) →
      (p, q) ∉ badPairsAtReportScale T α β γ δ rho →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        (n : ℝ) / Real.exp rho ≤ ((p ^ a * q ^ b : ℕ) : ℝ) ∧ p ^ a * q ^ b ≤ n := by
  have hβ1 : β < 1 := by linarith
  filter_upwards [eventually_report_good_pair_width hδ1 hβδ hrho,
    eventually_report_good_pair_budget hβ1 hδ1,
    eventually_reportApproximationScale_gt_one hδ1,
    eventually_ge_atTop (1 : ℝ)] with T hwidth hbudget hM hT
  intro p hp q hq n hnlog hgood
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hqp : q.Prime := (Finset.mem_filter.mp hq).2.1
  have hLp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
  have hlogratio := primeWindow_log_ratio_gt_one hp hq hT hβγ
  have hpql : Real.log (p : ℝ) < Real.log (q : ℝ) := by
    have hh := (lt_div_iff₀ hLp).mp hlogratio
    simpa using hh
  have hpq : p ≤ q := by
    have hh := (Real.log_lt_log_iff (by exact_mod_cast hpp.pos)
      (by exact_mod_cast hqp.pos)).mp hpql
    exact_mod_cast hh.le
  have hn : 0 < n := by
    by_contra! hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    simp only [hn0, Nat.cast_zero, Real.log_zero] at hnlog
    linarith
  have hpupper := (primeWindow_log_bounds hp hpp.pos).2
  have hqupper := (primeWindow_log_bounds hq hqp.pos).2
  have hwidthp : 8 * Real.log (p : ℝ) ≤
      rho * (reportApproximationScale T δ : ℝ) :=
    (mul_le_mul_of_nonneg_left hpupper (by norm_num)).trans hwidth
  have hbudgetpq : ((reportApproximationScale T δ : ℝ) + 1) * Real.log (q : ℝ) +
      3 * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
    calc
      _ ≤ ((reportApproximationScale T δ : ℝ) + 1) * T ^ δ + 3 * T ^ β :=
        add_le_add (mul_le_mul_of_nonneg_left hqupper (by positivity))
          (mul_le_mul_of_nonneg_left hpupper (by norm_num))
      _ ≤ T / 2 := hbudget
      _ ≤ Real.log (n : ℝ) := hnlog
  apply exists_positive_power_product_of_good_pair hpp.one_lt hpq hn
    (by omega : 0 < reportApproximationScale T δ) hrho hwidthp hbudgetpq
  intro r h hh
  apply hgood
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, ⟨r, h, hh⟩⟩

end Erdos878

#print axioms Erdos878.eventually_exists_positive_power_product_of_report_good_pair

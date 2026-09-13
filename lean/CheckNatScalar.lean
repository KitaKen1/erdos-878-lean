import CheckScalar

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

theorem eventually_tight_report_scalar_bound_on_nat :
    ∀ᶠ n : ℕ in atTop,
      tightReportScalar (Real.log (n : ℝ))
        (Real.log (Real.log (n : ℝ))) ≤
        24 * Real.log (n : ℝ) /
          (Real.log (Real.log (n : ℝ))) ^ 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hs := hv.eventually eventually_tight_report_scalar_bound
  have hTpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
    hlog.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hs, hTpos] with n hn hnp
  simpa [Real.exp_log hnp] using hn

end Erdos878

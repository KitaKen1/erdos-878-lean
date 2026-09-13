import Erdos878.MultiWindowParameters
import Erdos878.AdjustableDyadicTrackA

/-!
# Analytic inputs for all windows at once

The deep estimates already exist for one fixed report-window pair.  Since the number `k` of
pairs is fixed before the endpoint tends to infinity, finite products of eventual statements
and finite sums of convergent functions make all those estimates simultaneous.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

def multiWindowBadPairWeight (k : ℕ) (rho T : ℝ) : ℝ :=
  ∑ i : Fin k, pairReciprocalWeight
    (badPairsAtReportScale T
      (multiWindowAlpha k i) (multiWindowBeta k i)
      (multiWindowGamma k i) (multiWindowDelta k i) rho)

/-- The sum of the bad-pair reciprocal weights over every one of the fixed finitely many
multi-window pairs tends to zero. -/
theorem tendsto_multiWindowBadPairWeight_zero (k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (multiWindowBadPairWeight k rho) atTop (𝓝 0) := by
  unfold multiWindowBadPairWeight
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k))
    (fun i _ ↦ by
      rcases multiWindow_report_parameter_conditions i with
        ⟨hα, _, hβ, hβγ, _, hδ0, hδ1, hβδ⟩
      exact tendsto_badPairWeight_zero_of_report_scale_default
        hα hβ hβγ hδ0 hδ1 hβδ hrho)
  simpa using hsum

/-- Logarithmic-endpoint form used by the integer blocks. -/
theorem tendsto_multiWindowBadPairWeight_log_zero (k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (fun X : ℕ ↦ multiWindowBadPairWeight k rho (Real.log (X : ℝ)))
      atTop (𝓝 0) := by
  exact (tendsto_multiWindowBadPairWeight_zero k hrho).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Every left and right reciprocal mass has the same sharp main coefficient `w`, and all
`2k` inequalities hold simultaneously for large endpoints. -/
theorem eventually_all_multiWindow_endpointMass_ge
    (k : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ X : ℕ in atTop, ∀ i : Fin k,
      (1 - eta) * multiWindowWidth k * Real.log (Real.log (X : ℝ)) ≤
          reportPrimeWindowEndpointMass X
            (multiWindowAlpha k i) (multiWindowBeta k i) ∧
      (1 - eta) * multiWindowWidth k * Real.log (Real.log (X : ℝ)) ≤
          reportPrimeWindowEndpointMass X
            (multiWindowGamma k i) (multiWindowDelta k i) := by
  rw [Filter.eventually_all]
  intro i
  rcases multiWindow_report_parameter_conditions i with
    ⟨hα, hαβ, hβ, hβγ, hγδ, _, hδ1, _⟩
  have hβ1 : multiWindowBeta k i < 1 :=
    hβγ.trans_lt (hγδ.trans hδ1)
  have hγ : 0 < multiWindowGamma k i := hβ.trans_le hβγ
  filter_upwards
      [eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
        hα hαβ hβ1 heta,
       eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
        hγ hγδ hδ1 heta] with X hleft hright
  constructor
  · simpa [multiWindow_left_width] using hleft
  · simpa [multiWindow_right_width] using hright

/-- All left and right reciprocal masses tend to infinity, uniformly in the finite index only
in the logical sense that their eventual statements may be intersected. -/
theorem all_multiWindow_endpointMass_tendsto_atTop (k : ℕ) :
    (∀ i : Fin k,
      Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X
        (multiWindowAlpha k i) (multiWindowBeta k i)) atTop atTop) ∧
    (∀ i : Fin k,
      Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X
        (multiWindowGamma k i) (multiWindowDelta k i)) atTop atTop) := by
  constructor <;> intro i
  · rcases multiWindow_report_parameter_conditions i with
      ⟨hα, hαβ, hβ, hβγ, hγδ, _, hδ1, _⟩
    exact tendsto_reportPrimeWindowEndpointMass_atTop_of_lt
      hα hαβ (hβγ.trans_lt (hγδ.trans hδ1))
  · rcases multiWindow_report_parameter_conditions i with
      ⟨_, _, hβ, hβγ, hγδ, _, hδ1, _⟩
    exact tendsto_reportPrimeWindowEndpointMass_atTop_of_lt
      (hβ.trans_le hβγ) hγδ hδ1

end

end Erdos878

#print axioms Erdos878.tendsto_multiWindowBadPairWeight_zero
#print axioms Erdos878.eventually_all_multiWindow_endpointMass_ge
#print axioms Erdos878.all_multiWindow_endpointMass_tendsto_atTop

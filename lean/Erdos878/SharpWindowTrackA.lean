import Erdos878.FixedLoss
import Erdos878.PrimeReciprocalAbel

/-!
# Sharp report-window mass inside Track A

This module feeds the Mertens-quality report-window estimate into the already verified density-one
Track-A shell.  It improves both the admissible window condition (`a < b` instead of `2a < b`)
and the explicit fixed-loss constant.  It does not claim the conjectural sharp coefficient `1/2`:
the remaining losses come from the divisor-count threshold, the use of two disjoint windows, and
the good-pair packing step.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

/- Quantitative closure using the true widths of the two prime windows. -/
theorem exists_density_one_F_div_scale_ge_of_sharp_window_mass
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hαβ : α < β) (hβγ : β ≤ γ) (hγδ : γ < δ)
    (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        min (β - α) (δ - γ) / (4 * Real.exp rho) ≤
          (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  have hβ : 0 < β := hα.trans hαβ
  have hγ : 0 < γ := hβ.trans_le hβγ
  have hδ0 : 0 ≤ δ := (hγ.trans hγδ).le
  have hβ1 : β < 1 := by linarith
  have hwidth : 0 < min (β - α) (δ - γ) := by
    rw [lt_min_iff]
    exact ⟨sub_pos.mpr hαβ, sub_pos.mpr hγδ⟩
  rcases exists_density_one_dyadicTrackA_F_lower_of_mass
      hα hβ hβγ hδ0 hδ1 hβδ hrho
      (tendsto_reportPrimeWindowEndpointMass_atTop_of_lt hα hαβ hβ1)
      (tendsto_reportPrimeWindowEndpointMass_atTop_of_lt hγ hγδ hδ1) with
    ⟨A, hA, hFA⟩
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf bound
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hmass₁ := eventually_reportPrimeWindowEndpointMass_ge_half_main hα hαβ hβ1
  have hmass₂ := eventually_reportPrimeWindowEndpointMass_ge_half_main hγ hγδ hδ1
  have hXtop := tendsto_dyadicReportEndpoint_log_atTop
  have hmass₁n := hXtop.eventually hmass₁
  have hmass₂n := hXtop.eventually hmass₂
  have hNat : ∀ᶠ n : ℕ in atTop, n ∈ A →
      min (β - α) (δ - γ) / (4 * Real.exp rho) ≤
        (F n : ℝ) / scale n := by
    filter_upwards [hFA, hmass₁n, hmass₂n, eventually_scale_pos,
      eventually_gt_atTop (1 : ℕ)] with n hFn hm₁ hm₂ hscale hn
    intro hnA
    let X : ℕ := dyadicReportEndpoint (Nat.log 2 n)
    have hFlow := hFn hnA
    dsimp only at hFlow
    have hnX : n < X := by
      simpa [X, dyadicReportEndpoint] using
        (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n)
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hlognpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hlogle : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log hnpos
      exact_mod_cast hnX.le
    have hllle : Real.log (Real.log (n : ℝ)) ≤
        Real.log (Real.log (X : ℝ)) := Real.log_le_log hlognpos hlogle
    have hlln : 0 < Real.log (Real.log (n : ℝ)) := by
      unfold scale at hscale
      rwa [mul_pos_iff_of_pos_left hnpos] at hscale
    have hllX : 0 < Real.log (Real.log (X : ℝ)) := hlln.trans_le hllle
    have hm₁' : min (β - α) (δ - γ) / 4 *
        Real.log (Real.log (X : ℝ)) ≤
          reportPrimeWindowEndpointMass X α β / 2 := by
      calc
        min (β - α) (δ - γ) / 4 * Real.log (Real.log (X : ℝ)) ≤
            (β - α) / 4 * Real.log (Real.log (X : ℝ)) := by
          gcongr
          exact min_le_left _ _
        _ = ((β - α) / 2 * Real.log (Real.log (X : ℝ))) / 2 := by ring
        _ ≤ reportPrimeWindowEndpointMass X α β / 2 := by
          exact div_le_div_of_nonneg_right (by simpa [X] using hm₁) (by norm_num)
    have hm₂' : min (β - α) (δ - γ) / 4 *
        Real.log (Real.log (X : ℝ)) ≤
          reportPrimeWindowEndpointMass X γ δ / 2 := by
      calc
        min (β - α) (δ - γ) / 4 * Real.log (Real.log (X : ℝ)) ≤
            (δ - γ) / 4 * Real.log (Real.log (X : ℝ)) := by
          gcongr
          exact min_le_right _ _
        _ = ((δ - γ) / 2 * Real.log (Real.log (X : ℝ))) / 2 := by ring
        _ ≤ reportPrimeWindowEndpointMass X γ δ / 2 := by
          exact div_le_div_of_nonneg_right (by simpa [X] using hm₂) (by norm_num)
    have hmin : min (β - α) (δ - γ) / 4 * Real.log (Real.log (X : ℝ)) ≤
        min (reportPrimeWindowEndpointMass X α β / 2)
          (reportPrimeWindowEndpointMass X γ δ / 2) := le_min hm₁' hm₂'
    have hcoarse :
        (min (β - α) (δ - γ) / 4 * Real.log (Real.log (n : ℝ))) *
            (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
      calc
        (min (β - α) (δ - γ) / 4 * Real.log (Real.log (n : ℝ))) *
              (n : ℝ) / Real.exp rho ≤
            (min (β - α) (δ - γ) / 4 * Real.log (Real.log (X : ℝ))) *
              (n : ℝ) / Real.exp rho := by
          gcongr
        _ ≤ min (reportPrimeWindowEndpointMass X α β / 2)
              (reportPrimeWindowEndpointMass X γ δ / 2) * (n : ℝ) /
              Real.exp rho := by gcongr
        _ ≤ (F n : ℝ) := by simpa [X] using hFlow
    apply (le_div_iff₀ hscale).2
    calc
      min (β - α) (δ - γ) / (4 * Real.exp rho) * scale n =
          (min (β - α) (δ - γ) / 4 * Real.log (Real.log (n : ℝ))) *
            (n : ℝ) / Real.exp rho := by
        unfold scale
        ring
      _ ≤ (F n : ℝ) := hcoarse
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcoe.eventually hNat] with n hn
  exact hn n.property

/- A clean explicit specialization.  The old dyadic-square estimate gave `1 / (1024 e)`;
the sharp-window route gives `1 / (16 e)` with equally elementary rational parameters. -/
theorem exists_density_one_F_div_scale_ge_one_div_sixteen_exp :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        1 / (16 * Real.exp 1) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  have h := exists_density_one_F_div_scale_ge_of_sharp_window_mass
    (α := (1 / 12 : ℝ)) (β := (1 / 3 : ℝ))
    (γ := (1 / 3 : ℝ)) (δ := (7 / 12 : ℝ)) (rho := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hcoef :
      min ((1 / 3 : ℝ) - 1 / 12) (7 / 12 - 1 / 3) /
          (4 * Real.exp 1) = 1 / (16 * Real.exp 1) := by
    rw [show (1 / 3 : ℝ) - 1 / 12 = 1 / 4 by norm_num,
      show (7 / 12 : ℝ) - 1 / 3 = 1 / 4 by norm_num, min_self]
    field_simp
    norm_num
  rw [hcoef] at h
  exact h

/- The present two-window geometry has a genuine coefficient ceiling.  If the first window ends
before the second starts and `β + δ < 1`, their common usable width is strictly below `1/3`. -/
theorem two_window_min_width_lt_one_third
    {α β γ δ : ℝ} (hα : 0 < α) (hβγ : β ≤ γ) (hβδ : β + δ < 1) :
    min (β - α) (δ - γ) < 1 / 3 := by
  have hleft : min (β - α) (δ - γ) ≤ β - α := min_le_left _ _
  have hright : min (β - α) (δ - γ) ≤ δ - γ := min_le_right _ _
  linarith

/- Consequently even after sending the logarithmic approximation loss `rho` toward zero, the
coefficient delivered by this exact density shell stays below `1/12`.  Reaching `1/2` therefore
requires a different packing/counting argument, not merely sharper prime-distribution input. -/
theorem sharp_window_trackA_coefficient_lt_one_twelfth
    {α β γ δ rho : ℝ} (hα : 0 < α) (hβγ : β ≤ γ)
    (hβδ : β + δ < 1) (hrho : 0 ≤ rho) :
    min (β - α) (δ - γ) / (4 * Real.exp rho) < 1 / 12 := by
  have hwidth := two_window_min_width_lt_one_third hα hβγ hβδ
  have hexp : 1 ≤ Real.exp rho := by
    simpa using Real.exp_monotone hrho
  have hden : 0 < 4 * Real.exp rho := mul_pos (by norm_num) (Real.exp_pos rho)
  apply (div_lt_iff₀ hden).2
  nlinarith

end

end Erdos878

#print axioms Erdos878.exists_density_one_F_div_scale_ge_of_sharp_window_mass
#print axioms Erdos878.exists_density_one_F_div_scale_ge_one_div_sixteen_exp
#print axioms Erdos878.sharp_window_trackA_coefficient_lt_one_twelfth

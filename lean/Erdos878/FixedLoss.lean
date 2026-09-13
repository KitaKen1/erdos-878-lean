import Erdos878.ReportWindowMass

/-!
# An unconditional fixed-loss answer to the first question

The square-tail estimate gives a positive multiple of `log log X` in each report window.  This
file transfers that estimate from the dyadic report endpoint back to the integer `n`, intersects
the resulting density-one set with the already proved density-one set on which `f = o(scale)`,
and closes the official fixed-loss FC target.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

/- The dyadic endpoint attached to `n` tends to infinity. -/
theorem tendsto_dyadicReportEndpoint_log_atTop :
    Tendsto (fun n : ℕ ↦ dyadicReportEndpoint (Nat.log 2 n)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  exact hendpoint.comp hlog

/- Quantitative Track-A closure.  The first window contributes `α/64` after the divisor-count
threshold is halved.  The hypothesis `α ≤ γ` lets the same lower bound be used for the second
window. -/
theorem exists_density_one_F_div_scale_ge_of_two_mul_lt
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (h2αβ : 2 * α < β) (hβγ : β ≤ γ)
    (hαγ : α ≤ γ) (hγ : 0 < γ) (h2γδ : 2 * γ < δ)
    (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        α / (64 * Real.exp rho) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  rcases exists_density_one_dyadicTrackA_F_lower_of_two_mul_lt
      hα h2αβ hβγ hγ h2γδ hδ1 hβδ hrho with ⟨A, hA, hFA⟩
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf b
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hmass₁ := eventually_reportPrimeWindowEndpointMass_ge_loglog
    hα h2αβ (show β < 1 by linarith)
  have hmass₂ := eventually_reportPrimeWindowEndpointMass_ge_loglog
    hγ h2γδ hδ1
  have hXtop := tendsto_dyadicReportEndpoint_log_atTop
  have hmass₁n := hXtop.eventually hmass₁
  have hmass₂n := hXtop.eventually hmass₂
  have hNat : ∀ᶠ n : ℕ in atTop, n ∈ A →
      α / (64 * Real.exp rho) ≤ (F n : ℝ) / scale n := by
    filter_upwards [hFA, hmass₁n, hmass₂n, eventually_scale_pos,
      eventually_gt_atTop (1 : ℕ)] with n hFn hm₁ hm₂ hscale hn
    intro hnA
    let X : ℕ := dyadicReportEndpoint (Nat.log 2 n)
    have hFlow := hFn hnA
    dsimp only at hFlow
    have hn0 : n ≠ 0 := by omega
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
    have hm₁' : α / 64 * Real.log (Real.log (X : ℝ)) ≤
        reportPrimeWindowEndpointMass X α β / 2 := by
      calc
        α / 64 * Real.log (Real.log (X : ℝ)) =
            (α / 32 * Real.log (Real.log (X : ℝ))) / 2 := by ring
        _ ≤ reportPrimeWindowEndpointMass X α β / 2 := by
          exact div_le_div_of_nonneg_right (by simpa [X] using hm₁) (by norm_num)
    have hm₂' : α / 64 * Real.log (Real.log (X : ℝ)) ≤
        reportPrimeWindowEndpointMass X γ δ / 2 := by
      calc
        α / 64 * Real.log (Real.log (X : ℝ)) ≤
            γ / 64 * Real.log (Real.log (X : ℝ)) := by gcongr
        _ = (γ / 32 * Real.log (Real.log (X : ℝ))) / 2 := by ring
        _ ≤ reportPrimeWindowEndpointMass X γ δ / 2 := by
          exact div_le_div_of_nonneg_right (by simpa [X] using hm₂) (by norm_num)
    have hmin : α / 64 * Real.log (Real.log (X : ℝ)) ≤
        min (reportPrimeWindowEndpointMass X α β / 2)
          (reportPrimeWindowEndpointMass X γ δ / 2) := le_min hm₁' hm₂'
    have hcoarse :
        (α / 64 * Real.log (Real.log (n : ℝ))) * (n : ℝ) / Real.exp rho ≤
          (F n : ℝ) := by
      calc
        (α / 64 * Real.log (Real.log (n : ℝ))) * (n : ℝ) / Real.exp rho ≤
            (α / 64 * Real.log (Real.log (X : ℝ))) * (n : ℝ) / Real.exp rho := by
              gcongr
        _ ≤ min (reportPrimeWindowEndpointMass X α β / 2)
              (reportPrimeWindowEndpointMass X γ δ / 2) * (n : ℝ) /
              Real.exp rho := by gcongr
        _ ≤ (F n : ℝ) := by simpa [X] using hFlow
    apply (le_div_iff₀ hscale).2
    calc
      α / (64 * Real.exp rho) * scale n =
          (α / 64 * Real.log (Real.log (n : ℝ))) * (n : ℝ) / Real.exp rho := by
            unfold scale
            ring
      _ ≤ (F n : ℝ) := hcoarse
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcoe.eventually hNat] with n hn
  exact hn n.property

/- Closes Question 1 using the concrete two-window parameters. -/
theorem erdos_878_first_question : erdos_878.parts.i := by
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with ⟨S, hS, hfS⟩
  rcases exists_density_one_F_div_scale_ge_of_two_mul_lt
      (α := (1 / 16 : ℝ)) (β := (1 / 4 : ℝ))
      (γ := (1 / 4 : ℝ)) (δ := (2 / 3 : ℝ)) (rho := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) with
    ⟨T, hT, hFT⟩
  let I : Set ℕ := S ∩ T
  have hI : I.HasDensity 1 := by
    simpa [I] using hasDensity_one_inter_of_hasDensity_one hS hT
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hcoe : Tendsto (fun n : I ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hIinf b
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : I)] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hfI : (fun n : I ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : I ↦ scale (n : ℕ)) := by
    have hmap := tendsto_inter_subtype_to_left (S := S) (T := T) hIinf
    simpa [I, Function.comp_def] using hfS.comp_tendsto hmap
  have hFI : ∀ᶠ n : I in atTop,
      (1 / 16 : ℝ) / (64 * Real.exp 1) ≤
        (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    have hmap := tendsto_inter_subtype_to_right (S := S) (T := T) hIinf
    simpa [I, Function.comp_def] using hmap.eventually hFT
  have hscaleI : ∀ᶠ n : I in atTop, 0 < scale (n : ℕ) :=
    hcoe.eventually eventually_scale_pos
  exact proposed_first_question_fixed_loss_of_components I hI hfI
    (by positivity) hscaleI hFI

end

end Erdos878

#print axioms Erdos878.exists_density_one_F_div_scale_ge_of_two_mul_lt
#print axioms Erdos878.erdos_878_first_question

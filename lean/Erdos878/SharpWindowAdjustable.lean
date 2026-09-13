import Erdos878.AdjustableDyadicTrackA
import Erdos878.SharpWindowTrackA

/-!
# Sharp report-window mass with adjustable normal-order losses

This module combines the adjustable Chebyshev threshold `1 - epsilon` with an arbitrary relative
Mertens loss `1 - eta`.  The resulting density-one coefficient can approach the geometric width
of the two-window construction.  The construction still has a strict `1/3` ceiling, so it does
not prove the separate coefficient-`1/2` conjecture.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

theorem exists_density_one_F_div_scale_ge_of_sharp_window_mass_adjustable
    {alpha beta gamma delta rho epsilon eta : Real}
    (halpha : 0 < alpha) (halphabeta : alpha < beta) (hbetagamma : beta ≤ gamma)
    (hgammadelta : gamma < delta) (hdelta1 : delta < 1)
    (hbetadelta : beta + delta < 1) (hrho : 0 < rho)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ A : Set Nat, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        (1 - epsilon) * (1 - eta) * min (beta - alpha) (delta - gamma) /
            Real.exp rho ≤ (F (n : Nat) : Real) / scale (n : Nat) := by
  have hbeta : 0 < beta := halpha.trans halphabeta
  have hgamma : 0 < gamma := hbeta.trans_le hbetagamma
  have hdelta0 : 0 ≤ delta := (hgamma.trans hgammadelta).le
  have hbeta1 : beta < 1 := by linarith
  have hwidth : 0 < min (beta - alpha) (delta - gamma) := by
    rw [lt_min_iff]
    exact ⟨sub_pos.mpr halphabeta, sub_pos.mpr hgammadelta⟩
  have honeepsilon : 0 < 1 - epsilon := sub_pos.mpr hepsilon1
  have honeeta : 0 < 1 - eta := sub_pos.mpr heta1
  let c : Real := (1 - epsilon) * (1 - eta)
  have hc : 0 < c := mul_pos honeepsilon honeeta
  rcases exists_density_one_dyadicTrackA_F_lower_of_mass_adjustable
      halpha hbeta hbetagamma hdelta0 hdelta1 hbetadelta hrho hepsilon0
      (tendsto_reportPrimeWindowEndpointMass_atTop_of_lt
        halpha halphabeta hbeta1)
      (tendsto_reportPrimeWindowEndpointMass_atTop_of_lt
        hgamma hgammadelta hdelta1) with
    ⟨A, hA, hFA⟩
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A => (n : Nat)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf bound
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans (show a ≤ (n : Nat) from hn)
  have hmass1 :=
    eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
      halpha halphabeta hbeta1 heta0
  have hmass2 :=
    eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
      hgamma hgammadelta hdelta1 heta0
  have hXtop := tendsto_dyadicReportEndpoint_log_atTop
  have hmass1n := hXtop.eventually hmass1
  have hmass2n := hXtop.eventually hmass2
  have hNat : ∀ᶠ n : Nat in atTop, n ∈ A →
      c * min (beta - alpha) (delta - gamma) / Real.exp rho ≤
        (F n : Real) / scale n := by
    filter_upwards [hFA, hmass1n, hmass2n, eventually_scale_pos,
      eventually_gt_atTop (1 : Nat)] with n hFn hm1 hm2 hscale hn
    intro hnA
    let X : Nat := dyadicReportEndpoint (Nat.log 2 n)
    have hFlow := hFn hnA
    dsimp only at hFlow
    have hnX : n < X := by
      simpa [X, dyadicReportEndpoint] using
        (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : Nat)) n)
    have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hlognpos : 0 < Real.log (n : Real) := Real.log_pos (by exact_mod_cast hn)
    have hlogle : Real.log (n : Real) ≤ Real.log (X : Real) := by
      apply Real.log_le_log hnpos
      exact_mod_cast hnX.le
    have hllle : Real.log (Real.log (n : Real)) ≤
        Real.log (Real.log (X : Real)) := Real.log_le_log hlognpos hlogle
    have hlln : 0 < Real.log (Real.log (n : Real)) := by
      unfold scale at hscale
      rwa [mul_pos_iff_of_pos_left hnpos] at hscale
    have hllX : 0 < Real.log (Real.log (X : Real)) := hlln.trans_le hllle
    have hm1' : c * min (beta - alpha) (delta - gamma) *
        Real.log (Real.log (X : Real)) ≤
          (1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta := by
      calc
        c * min (beta - alpha) (delta - gamma) *
              Real.log (Real.log (X : Real)) ≤
            c * (beta - alpha) * Real.log (Real.log (X : Real)) := by
          gcongr
          exact min_le_left _ _
        _ = (1 - epsilon) *
            ((1 - eta) * (beta - alpha) * Real.log (Real.log (X : Real))) := by
          dsimp [c]
          ring
        _ ≤ (1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta := by
          exact mul_le_mul_of_nonneg_left (by simpa [X] using hm1) honeepsilon.le
    have hm2' : c * min (beta - alpha) (delta - gamma) *
        Real.log (Real.log (X : Real)) ≤
          (1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta := by
      calc
        c * min (beta - alpha) (delta - gamma) *
              Real.log (Real.log (X : Real)) ≤
            c * (delta - gamma) * Real.log (Real.log (X : Real)) := by
          gcongr
          exact min_le_right _ _
        _ = (1 - epsilon) *
            ((1 - eta) * (delta - gamma) * Real.log (Real.log (X : Real))) := by
          dsimp [c]
          ring
        _ ≤ (1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta := by
          exact mul_le_mul_of_nonneg_left (by simpa [X] using hm2) honeepsilon.le
    have hmin : c * min (beta - alpha) (delta - gamma) *
          Real.log (Real.log (X : Real)) ≤
        min ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
          ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) :=
      le_min hm1' hm2'
    have hcoarse :
        (c * min (beta - alpha) (delta - gamma) *
            Real.log (Real.log (n : Real))) * (n : Real) / Real.exp rho ≤
          (F n : Real) := by
      calc
        (c * min (beta - alpha) (delta - gamma) *
              Real.log (Real.log (n : Real))) * (n : Real) / Real.exp rho ≤
            (c * min (beta - alpha) (delta - gamma) *
              Real.log (Real.log (X : Real))) * (n : Real) / Real.exp rho := by
          gcongr
        _ ≤ min ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
              ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) *
              (n : Real) / Real.exp rho := by gcongr
        _ ≤ (F n : Real) := by simpa [X] using hFlow
    apply (le_div_iff₀ hscale).2
    calc
      (c * min (beta - alpha) (delta - gamma) / Real.exp rho) * scale n =
          (c * min (beta - alpha) (delta - gamma) *
            Real.log (Real.log (n : Real))) * (n : Real) / Real.exp rho := by
        unfold scale
        ring
      _ ≤ (F n : Real) := hcoarse
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcoe.eventually hNat] with n hn
  simpa [c] using hn n.property

/- A simple explicit improvement over `1 / (16 e)`. -/
theorem exists_density_one_F_div_scale_ge_nine_div_sixtyfour_exp :
    ∃ A : Set Nat, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        9 / (64 * Real.exp 1) ≤ (F (n : Nat) : Real) / scale (n : Nat) := by
  have h := exists_density_one_F_div_scale_ge_of_sharp_window_mass_adjustable
    (alpha := (1 / 12 : Real)) (beta := (1 / 3 : Real))
    (gamma := (1 / 3 : Real)) (delta := (7 / 12 : Real))
    (rho := (1 : Real)) (epsilon := (1 / 4 : Real)) (eta := (1 / 4 : Real))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcoef :
      (1 - (1 / 4 : Real)) * (1 - 1 / 4) *
          min ((1 / 3 : Real) - 1 / 12) (7 / 12 - 1 / 3) / Real.exp 1 =
        9 / (64 * Real.exp 1) := by
    rw [show (1 / 3 : Real) - 1 / 12 = 1 / 4 by norm_num,
      show (7 / 12 : Real) - 1 / 3 = 1 / 4 by norm_num, min_self]
    field_simp
    norm_num
  rw [hcoef] at h
  exact h

/- The improved `F` estimate and the already proved almost-all estimate for `f` hold on one
common density-one set.  This is the quantitative data behind the exact first-question claim. -/
theorem exists_density_one_first_question_data_nine_div_sixtyfour_exp :
    ∃ I : Set Nat, I.HasDensity 1 ∧
      (fun n : I => (f (n : Nat) : Real)) =o[atTop]
        (fun n : I => scale (n : Nat)) ∧
      ∀ᶠ n : I in atTop,
        9 / (64 * Real.exp 1) ≤ (F (n : Nat) : Real) / scale (n : Nat) := by
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with ⟨S, hS, hfS⟩
  rcases exists_density_one_F_div_scale_ge_nine_div_sixtyfour_exp with ⟨T, hT, hFT⟩
  let I : Set Nat := S ∩ T
  have hI : I.HasDensity 1 := by
    simpa [I] using hasDensity_one_inter_of_hasDensity_one hS hT
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hfI : (fun n : I => (f (n : Nat) : Real)) =o[atTop]
      (fun n : I => scale (n : Nat)) := by
    have hmap := tendsto_inter_subtype_to_left (S := S) (T := T) hIinf
    simpa [I, Function.comp_def] using hfS.comp_tendsto hmap
  have hFI : ∀ᶠ n : I in atTop,
      9 / (64 * Real.exp 1) ≤ (F (n : Nat) : Real) / scale (n : Nat) := by
    have hmap := tendsto_inter_subtype_to_right (S := S) (T := T) hIinf
    simpa [I, Function.comp_def] using hmap.eventually hFT
  exact ⟨I, hI, hfI, hFI⟩

/- Exact FC-like first-question statement, now closed through the improved adjustable-window
route rather than only through the older square-tail constant. -/
theorem erdos_878_first_question_via_adjustable_windows : erdos_878.parts.i := by
  rcases exists_density_one_first_question_data_nine_div_sixtyfour_exp with
    ⟨I, hI, hfI, hFI⟩
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hcoe : Tendsto (fun n : I => (n : Nat)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hIinf bound
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : I)] with n hn
    exact hba.le.trans (show a ≤ (n : Nat) from hn)
  have hscaleI : ∀ᶠ n : I in atTop, 0 < scale (n : Nat) :=
    hcoe.eventually eventually_scale_pos
  exact proposed_first_question_fixed_loss_of_components I hI hfI
    (by positivity) hscaleI hFI

/- Even after both adjustable losses tend to zero, the present two-window geometry remains
strictly below `1/3`. -/
theorem adjustable_sharp_window_coefficient_lt_one_third
    {alpha beta gamma delta rho epsilon eta : Real}
    (halpha : 0 < alpha) (hbetagamma : beta ≤ gamma)
    (hbetadelta : beta + delta < 1) (hrho : 0 ≤ rho)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (1 - epsilon) * (1 - eta) * min (beta - alpha) (delta - gamma) /
        Real.exp rho < 1 / 3 := by
  let w : Real := min (beta - alpha) (delta - gamma)
  let c : Real := (1 - epsilon) * (1 - eta)
  have hwlt : w < 1 / 3 := by
    exact two_window_min_width_lt_one_third halpha hbetagamma hbetadelta
  have hc0 : 0 ≤ c := mul_nonneg (sub_nonneg.mpr hepsilon1) (sub_nonneg.mpr heta1)
  have hc1 : c ≤ 1 := by
    have h1e : 1 - epsilon ≤ 1 := by linarith
    have h1eta : 1 - eta ≤ 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hepsilon1) (sub_nonneg.mpr heta1)]
  have hexp : 1 ≤ Real.exp rho := by simpa using Real.exp_monotone hrho
  have hexppos : 0 < Real.exp rho := Real.exp_pos rho
  by_cases hw0 : 0 ≤ w
  · have hnum : c * w ≤ w := by nlinarith
    have hwexp : w ≤ w * Real.exp rho := by nlinarith
    have hdiv : c * w / Real.exp rho ≤ w := by
      apply (div_le_iff₀ hexppos).2
      exact hnum.trans hwexp
    simpa [c, w, mul_assoc] using hdiv.trans_lt hwlt
  · have hwneg : w < 0 := lt_of_not_ge hw0
    have hnum : c * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hwneg.le
    have hdiv : c * w / Real.exp rho ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hexppos.le
    have hthird : (0 : Real) < 1 / 3 := by norm_num
    simpa [c, w, mul_assoc] using hdiv.trans_lt hthird

end

end Erdos878

#print axioms Erdos878.exists_density_one_F_div_scale_ge_of_sharp_window_mass_adjustable
#print axioms Erdos878.exists_density_one_F_div_scale_ge_nine_div_sixtyfour_exp
#print axioms Erdos878.exists_density_one_first_question_data_nine_div_sixtyfour_exp
#print axioms Erdos878.erdos_878_first_question_via_adjustable_windows
#print axioms Erdos878.adjustable_sharp_window_coefficient_lt_one_third

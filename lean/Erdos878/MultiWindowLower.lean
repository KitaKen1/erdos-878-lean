import Erdos878.MultiWindowPacking

/-!
# Density-one lower bounds from the combined multi-window packing

This file connects the local packing to the dyadic exceptional set.  It retains the sum of the
window contributions until after the single call to the packing theorem, and only then replaces
each divisor count by its adjustable reciprocal-mass lower bound.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

/-- Outside the one finite-union exceptional set, the combined packing is bounded below by the
sum of all adjustable endpoint masses. -/
theorem eventually_multiWindow_F_lower_off_exception
    (k : ℕ) {rho epsilon : ℝ} (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      n ∉ multiWindowExceptionalSet k rho epsilon →
      let X := dyadicReportEndpoint (Nat.log 2 n)
      (∑ i : Fin k,
          min
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowAlpha k i) (multiWindowBeta k i))
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowGamma k i) (multiWindowDelta k i))) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hscale : Tendsto
      (fun b : ℕ ↦ Real.log (dyadicReportEndpoint b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hendpoint)
  have hpacking := hscale.eventually (eventually_multiWindow_F_lower k hrho)
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  filter_upwards [hlog.eventually hpacking, eventually_ge_atTop (2 : ℕ)] with n hpack hn
  intro hnot
  let b := Nat.log 2 n
  let X := dyadicReportEndpoint b
  let T := Real.log (X : ℝ)
  have hn0 : n ≠ 0 := by omega
  have hnX : n < X := by
    simpa [X, b, dyadicReportEndpoint] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hnIcc : n ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨by omega, hnX.le⟩
  have hpowR : (((2 ^ b : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.pow_log_le_self 2 hn0)
  have hloglo := Real.log_le_log
    (by positivity : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ)) hpowR
  rw [show (((2 ^ b : ℕ) : ℝ)) = (2 : ℝ) ^ b by norm_num,
    Real.log_pow] at hloglo
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcoef : (((b + 1 : ℕ) : ℝ)) ≤ 2 * (b : ℝ) := by
    exact_mod_cast (show b + 1 ≤ 2 * b by
      have hb : 1 ≤ b := by
        by_contra hb0
        have hbzero : b = 0 := by omega
        have hnlt : n < 2 := by
          simpa [b, hbzero] using Nat.lt_pow_succ_log_self
            (by norm_num : 1 < (2 : ℕ)) n
        omega
      omega)
  have hscaleHalf : T / 2 ≤ Real.log (n : ℝ) := by
    dsimp [T, X]
    rw [dyadicReportEndpoint, Nat.cast_pow, Real.log_pow]
    calc
      ((b + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) / 2 ≤
          (2 * (b : ℝ)) * Real.log (2 : ℝ) / 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef hlog2.le) (by norm_num)
      _ = (b : ℝ) * Real.log (2 : ℝ) := by ring
      _ ≤ Real.log (n : ℝ) := by simpa [mul_comm] using hloglo
  have hnotBad : ∀ i : Fin k, n ∉ divisibleBySomePairUpTo n
      (badPairsAtReportScale T
        (multiWindowAlpha k i) (multiWindowBeta k i)
        (multiWindowGamma k i) (multiWindowDelta k i) rho) := by
    intro i hbad
    have hsingle :=
      not_mem_single_exception_of_not_mem_multiWindowExceptionalSet hnot i
    have hnotPair : n ∉ dyadicReportPairExceptionalSet
        (multiWindowAlpha k i) (multiWindowBeta k i)
        (multiWindowGamma k i) (multiWindowDelta k i) rho := by
      intro hmem
      exact hsingle (Set.mem_union_left _ hmem)
    apply hnotPair
    refine ⟨hn0, ?_⟩
    change n ∈ dyadicReportBadIntegers b
      (multiWindowAlpha k i) (multiWindowBeta k i)
      (multiWindowGamma k i) (multiWindowDelta k i) rho
    unfold dyadicReportBadIntegers
    exact divisibleBySomePairUpTo_mono
      (badPairsAtReportScale T
        (multiWindowAlpha k i) (multiWindowBeta k i)
        (multiWindowGamma k i) (multiWindowDelta k i) rho) hnX.le hbad
  have hbase :
      (∑ i : Fin k,
          min
            (divisorCount
              (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)) n)
            (divisorCount
              (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)) n)) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
    simpa [T, X, b] using hpack n hn0 hscaleHalf hnotBad
  have hcounts : ∀ i : Fin k,
      min
          ((1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowAlpha k i) (multiWindowBeta k i))
          ((1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowGamma k i) (multiWindowDelta k i)) ≤
        min
          (divisorCount
            (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)) n)
          (divisorCount
            (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)) n) := by
    intro i
    have hsingle :=
      not_mem_single_exception_of_not_mem_multiWindowExceptionalSet hnot i
    have hnotLow : n ∉ dyadicReportLowDivisorExceptionalSetAdjustable
        (multiWindowAlpha k i) (multiWindowBeta k i)
        (multiWindowGamma k i) (multiWindowDelta k i) epsilon := by
      intro hmem
      exact hsingle (Set.mem_union_right _ hmem)
    have hnotBlock : n ∉ dyadicReportLowDivisorIntegersAdjustable b
        (multiWindowAlpha k i) (multiWindowBeta k i)
        (multiWindowGamma k i) (multiWindowDelta k i) epsilon := by
      intro hmem
      apply hnotLow
      exact ⟨hn0, by simpa [b] using hmem⟩
    have hcountLeft :
        (1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowAlpha k i) (multiWindowBeta k i) ≤
          divisorCount (reportPrimeWindowInEndpoint X
            (multiWindowAlpha k i) (multiWindowBeta k i)) n := by
      apply le_of_not_gt
      intro hlt
      apply hnotBlock
      unfold dyadicReportLowDivisorIntegersAdjustable
        reportLowDivisorIntegersUpToAdjustable
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
    have hcountRight :
        (1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowGamma k i) (multiWindowDelta k i) ≤
          divisorCount (reportPrimeWindowInEndpoint X
            (multiWindowGamma k i) (multiWindowDelta k i)) n := by
      apply le_of_not_gt
      intro hlt
      apply hnotBlock
      unfold dyadicReportLowDivisorIntegersAdjustable
        reportLowDivisorIntegersUpToAdjustable
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
    apply min_le_min
    · exact hcountLeft.trans (divisorCount_mono Finset.inter_subset_left n)
    · exact hcountRight.trans (divisorCount_mono Finset.inter_subset_left n)
  dsimp only
  change (∑ i : Fin k,
      min
        ((1 - epsilon) * reportPrimeWindowEndpointMass X
          (multiWindowAlpha k i) (multiWindowBeta k i))
        ((1 - epsilon) * reportPrimeWindowEndpointMass X
          (multiWindowGamma k i) (multiWindowDelta k i))) *
      (n : ℝ) / Real.exp rho ≤ (F n : ℝ)
  calc
    (∑ i : Fin k,
        min
          ((1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowAlpha k i) (multiWindowBeta k i))
          ((1 - epsilon) * reportPrimeWindowEndpointMass X
            (multiWindowGamma k i) (multiWindowDelta k i))) *
        (n : ℝ) / Real.exp rho ≤
      (∑ i : Fin k,
        min
          (divisorCount
            (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)) n)
          (divisorCount
            (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)) n)) *
        (n : ℝ) / Real.exp rho := by
          have hsum :
              (∑ i : Fin k,
                min
                  ((1 - epsilon) * reportPrimeWindowEndpointMass X
                    (multiWindowAlpha k i) (multiWindowBeta k i))
                  ((1 - epsilon) * reportPrimeWindowEndpointMass X
                    (multiWindowGamma k i) (multiWindowDelta k i))) ≤
                ∑ i : Fin k,
                  min
                    (divisorCount
                      (primeWindow T
                        (multiWindowAlpha k i) (multiWindowBeta k i)) n)
                    (divisorCount
                      (primeWindow T
                        (multiWindowGamma k i) (multiWindowDelta k i)) n) := by
            exact Finset.sum_le_sum (fun i _ ↦ hcounts i)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsum (by positivity)) (Real.exp_pos rho).le
    _ ≤ (F n : ℝ) := hbase

/-- Fixed-parameter density-one lower bound.  Its coefficient approaches `1/2` when the number
of window pairs grows and the three losses tend to zero. -/
theorem exists_density_one_F_div_scale_ge_multiWindow
    (k : ℕ) {rho epsilon eta : ℝ}
    (hrho : 0 < rho) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        (1 - epsilon) * (1 - eta) * (k : ℝ) * multiWindowWidth k /
            Real.exp rho ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  let A : Set ℕ := (multiWindowExceptionalSet k rho epsilon)ᶜ
  have hA : A.HasDensity 1 := by
    exact multiWindowExceptionalSet_compl_hasDensity_one k hrho hepsilon0
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf bound
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hmasses : ∀ᶠ n : ℕ in atTop, ∀ i : Fin k,
      (1 - eta) * multiWindowWidth k *
            Real.log (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) ≤
          reportPrimeWindowEndpointMass (dyadicReportEndpoint (Nat.log 2 n))
            (multiWindowAlpha k i) (multiWindowBeta k i) ∧
      (1 - eta) * multiWindowWidth k *
            Real.log (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) ≤
          reportPrimeWindowEndpointMass (dyadicReportEndpoint (Nat.log 2 n))
            (multiWindowGamma k i) (multiWindowDelta k i) := by
    exact hlog.eventually
      (hendpoint.eventually (eventually_all_multiWindow_endpointMass_ge k heta0))
  have hNat : ∀ᶠ n : ℕ in atTop, n ∈ A →
      (1 - epsilon) * (1 - eta) * (k : ℝ) * multiWindowWidth k /
          Real.exp rho ≤ (F n : ℝ) / scale n := by
    filter_upwards [eventually_multiWindow_F_lower_off_exception k hrho,
      hmasses, eventually_scale_pos, eventually_gt_atTop (1 : ℕ)]
      with n hF hmass hscale hn
    intro hnA
    have hnot : n ∉ multiWindowExceptionalSet k rho epsilon := hnA
    let X := dyadicReportEndpoint (Nat.log 2 n)
    have hnX : n < X := by
      simpa [X, dyadicReportEndpoint] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hlognpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hlogle : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log hnpos
      exact_mod_cast hnX.le
    have hllle : Real.log (Real.log (n : ℝ)) ≤
        Real.log (Real.log (X : ℝ)) := Real.log_le_log hlognpos hlogle
    have honeepsilon : 0 < 1 - epsilon := sub_pos.mpr hepsilon1
    have honeeta : 0 < 1 - eta := sub_pos.mpr heta1
    let c : ℝ := (1 - epsilon) * (1 - eta) * multiWindowWidth k
    have hc : 0 < c := mul_pos (mul_pos honeepsilon honeeta) (multiWindowWidth_pos k)
    have hterm : ∀ i : Fin k,
        c * Real.log (Real.log (X : ℝ)) ≤
          min
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowAlpha k i) (multiWindowBeta k i))
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowGamma k i) (multiWindowDelta k i)) := by
      intro i
      apply le_min
      · calc
          c * Real.log (Real.log (X : ℝ)) =
              (1 - epsilon) *
                ((1 - eta) * multiWindowWidth k *
                  Real.log (Real.log (X : ℝ))) := by
                    dsimp [c]
                    ring
          _ ≤ (1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowAlpha k i) (multiWindowBeta k i) :=
            mul_le_mul_of_nonneg_left (by simpa [X] using (hmass i).1)
              honeepsilon.le
      · calc
          c * Real.log (Real.log (X : ℝ)) =
              (1 - epsilon) *
                ((1 - eta) * multiWindowWidth k *
                  Real.log (Real.log (X : ℝ))) := by
                    dsimp [c]
                    ring
          _ ≤ (1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowGamma k i) (multiWindowDelta k i) :=
            mul_le_mul_of_nonneg_left (by simpa [X] using (hmass i).2)
              honeepsilon.le
    have hsum : (k : ℝ) * (c * Real.log (Real.log (X : ℝ))) ≤
        ∑ i : Fin k,
          min
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowAlpha k i) (multiWindowBeta k i))
            ((1 - epsilon) * reportPrimeWindowEndpointMass X
              (multiWindowGamma k i) (multiWindowDelta k i)) := by
      calc
        (k : ℝ) * (c * Real.log (Real.log (X : ℝ))) =
            ∑ _i : Fin k, c * Real.log (Real.log (X : ℝ)) := by simp
        _ ≤ ∑ i : Fin k,
            min
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowAlpha k i) (multiWindowBeta k i))
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowGamma k i) (multiWindowDelta k i)) :=
          Finset.sum_le_sum (fun i _ ↦ hterm i)
    have hsumN :
        (k : ℝ) * (c * Real.log (Real.log (n : ℝ))) ≤
          ∑ i : Fin k,
            min
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowAlpha k i) (multiWindowBeta k i))
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowGamma k i) (multiWindowDelta k i)) := by
      calc
        (k : ℝ) * (c * Real.log (Real.log (n : ℝ))) ≤
            (k : ℝ) * (c * Real.log (Real.log (X : ℝ))) := by
              gcongr
        _ ≤ _ := hsum
    apply (le_div_iff₀ hscale).2
    calc
      ((1 - epsilon) * (1 - eta) * (k : ℝ) * multiWindowWidth k /
          Real.exp rho) * scale n =
        ((k : ℝ) * (c * Real.log (Real.log (n : ℝ)))) *
          (n : ℝ) / Real.exp rho := by
            unfold scale
            dsimp [c]
            ring
      _ ≤ (∑ i : Fin k,
            min
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowAlpha k i) (multiWindowBeta k i))
              ((1 - epsilon) * reportPrimeWindowEndpointMass X
                (multiWindowGamma k i) (multiWindowDelta k i))) *
          (n : ℝ) / Real.exp rho := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsumN hnpos.le) (Real.exp_pos rho).le
      _ ≤ (F n : ℝ) := by simpa [X] using hF hnot
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcoe.eventually hNat] with n hn
  exact hn n.property

end

end Erdos878

#print axioms Erdos878.eventually_multiWindow_F_lower_off_exception
#print axioms Erdos878.exists_density_one_F_div_scale_ge_multiWindow

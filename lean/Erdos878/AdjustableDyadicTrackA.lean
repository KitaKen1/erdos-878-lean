import Erdos878.DyadicDivisorNormalOrder
import Erdos878.SharpThresholdNormalOrder

/-!
# Dyadic Track A with an adjustable divisor-count threshold

This is the two-window and density-one continuation of `SharpThresholdNormalOrder`.  The stable
Track-A API uses half of each reciprocal prime mass; here that fixed half is replaced by
`(1 - epsilon)` for every fixed `epsilon > 0`.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

noncomputable section

def reportLowDivisorIntegersUpToAdjustable
    (X : Nat) (alpha beta gamma delta epsilon : Real) : Finset Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
      divisorCount (reportPrimeWindowInEndpoint X alpha beta) n <
        (1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)) ∪
    ((Finset.Icc 1 X).filter (fun n =>
      divisorCount (reportPrimeWindowInEndpoint X gamma delta) n <
        (1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta))

/- Divergence of the two reciprocal masses makes the adjustable low-count set negligible. -/
theorem tendsto_reportLowDivisorExceptionalRatioAdjustable_zero_of_mass
    {alpha beta gamma delta epsilon : Real} (hepsilon : 0 < epsilon)
    (hmass1 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X alpha beta)
      atTop atTop)
    (hmass2 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X gamma delta)
      atTop atTop) :
    Tendsto (fun X : Nat =>
      ((reportLowDivisorIntegersUpToAdjustable
        X alpha beta gamma delta epsilon).card : Real) / (X : Real))
      atTop (nhds 0) := by
  unfold reportLowDivisorIntegersUpToAdjustable reportPrimeWindowEndpointMass
  exact
    tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_adjustable
      (fun X => reportPrimeWindowInEndpoint X alpha beta)
      (fun X => reportPrimeWindowInEndpoint X gamma delta)
      hepsilon
      (fun X p hp => (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2.1)
      (fun X p hp => (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2.1)
      (fun X => Finset.inter_subset_right)
      (fun X => Finset.inter_subset_right)
      hmass1 hmass2

def dyadicReportLowDivisorIntegersAdjustable
    (k : Nat) (alpha beta gamma delta epsilon : Real) : Finset Nat :=
  reportLowDivisorIntegersUpToAdjustable
    (dyadicReportEndpoint k) alpha beta gamma delta epsilon

def dyadicReportLowDivisorExceptionalSetAdjustable
    (alpha beta gamma delta epsilon : Real) : Set Nat :=
  dyadicBlockExceptionalSet
    (fun k => dyadicReportLowDivisorIntegersAdjustable
      k alpha beta gamma delta epsilon)

/- Sampling at powers of two and geometric stitching produce one density-zero set. -/
theorem dyadicReportLowDivisorExceptionalSetAdjustable_hasDensity_zero_of_mass
    {alpha beta gamma delta epsilon : Real} (hepsilon : 0 < epsilon)
    (hmass1 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X alpha beta)
      atTop atTop)
    (hmass2 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X gamma delta)
      atTop atTop) :
    (dyadicReportLowDivisorExceptionalSetAdjustable
      alpha beta gamma delta epsilon).HasDensity 0 := by
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : Nat))).comp
      (tendsto_add_atTop_nat 1)
  have hratio :=
    (tendsto_reportLowDivisorExceptionalRatioAdjustable_zero_of_mass
      hepsilon hmass1 hmass2).comp hendpoint
  simpa [dyadicReportLowDivisorExceptionalSetAdjustable,
    dyadicReportLowDivisorIntegersAdjustable, Function.comp_def] using
      dyadicBlockExceptionalSet_hasDensity_zero_of_endpoint_ratio
        (fun k => dyadicReportLowDivisorIntegersAdjustable
          k alpha beta gamma delta epsilon) hratio

def dyadicTrackAExceptionalSetAdjustable
    (alpha beta gamma delta rho epsilon : Real) : Set Nat :=
  dyadicReportPairExceptionalSet alpha beta gamma delta rho ∪
    dyadicReportLowDivisorExceptionalSetAdjustable alpha beta gamma delta epsilon

/- Bad pairs and adjustable low divisor counts may be removed simultaneously. -/
theorem dyadicTrackAExceptionalSetAdjustable_hasDensity_zero_of_mass
    {alpha beta gamma delta rho epsilon : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetagamma : beta ≤ gamma)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1) (hbetadelta : beta + delta < 1)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon)
    (hmass1 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X alpha beta)
      atTop atTop)
    (hmass2 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X gamma delta)
      atTop atTop) :
    (dyadicTrackAExceptionalSetAdjustable
      alpha beta gamma delta rho epsilon).HasDensity 0 := by
  unfold dyadicTrackAExceptionalSetAdjustable
  exact hasDensity_zero_union
    (dyadicReportPairExceptionalSet_hasDensity_zero
      halpha hbeta hbetagamma hdelta0 hdelta1 hbetadelta hrho)
    (dyadicReportLowDivisorExceptionalSetAdjustable_hasDensity_zero_of_mass
      hepsilon hmass1 hmass2)

/- Outside the combined exceptional set, the adjustable portions of both masses give a
pointwise lower bound for `F`. -/
theorem eventually_F_lower_off_dyadicTrackA_adjustable_exception
    {alpha beta gamma delta rho epsilon : Real}
    (hbetagamma : beta ≤ gamma) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hbetadelta : beta + delta < 1) (hrho : 0 < rho) :
    ∀ᶠ n : Nat in atTop,
      n ∉ dyadicTrackAExceptionalSetAdjustable alpha beta gamma delta rho epsilon →
      let X := dyadicReportEndpoint (Nat.log 2 n)
      min
          ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
          ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) *
          (n : Real) / Real.exp rho ≤ (F n : Real) := by
  filter_upwards
      [eventually_F_lower_off_dyadic_report_exception
        (α := alpha) hbetagamma hdelta0 hdelta1 hbetadelta hrho,
       eventually_ge_atTop (1 : Nat)] with n hF hn
  intro hnot
  let k := Nat.log 2 n
  let X := dyadicReportEndpoint k
  have hn0 : n ≠ 0 := by omega
  have hnX : n < X := by
    simpa [X, k, dyadicReportEndpoint] using
      Nat.lt_pow_succ_log_self (by norm_num) n
  have hnIcc : n ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hn, hnX.le⟩
  have hnotPair : n ∉ dyadicReportPairExceptionalSet alpha beta gamma delta rho := by
    intro hmem
    exact hnot (Set.mem_union_left _ hmem)
  have hnotLow : n ∉
      dyadicReportLowDivisorExceptionalSetAdjustable alpha beta gamma delta epsilon := by
    intro hmem
    exact hnot (Set.mem_union_right _ hmem)
  have hnotBlock : n ∉
      dyadicReportLowDivisorIntegersAdjustable k alpha beta gamma delta epsilon := by
    intro hmem
    apply hnotLow
    exact ⟨hn0, by simpa [k] using hmem⟩
  have hcount1 :
      (1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta ≤
        divisorCount (reportPrimeWindowInEndpoint X alpha beta) n := by
    apply le_of_not_gt
    intro hlt
    apply hnotBlock
    unfold dyadicReportLowDivisorIntegersAdjustable
      reportLowDivisorIntegersUpToAdjustable
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
  have hcount2 :
      (1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta ≤
        divisorCount (reportPrimeWindowInEndpoint X gamma delta) n := by
    apply le_of_not_gt
    intro hlt
    apply hnotBlock
    unfold dyadicReportLowDivisorIntegersAdjustable
      reportLowDivisorIntegersUpToAdjustable
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
  have hcountFull1 :
      (1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta ≤
        divisorCount (reportPrimeWindow X alpha beta) n :=
    hcount1.trans (divisorCount_mono Finset.inter_subset_left n)
  have hcountFull2 :
      (1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta ≤
        divisorCount (reportPrimeWindow X gamma delta) n :=
    hcount2.trans (divisorCount_mono Finset.inter_subset_left n)
  have hmin := min_le_min hcountFull1 hcountFull2
  have hbase : min
        (divisorCount (reportPrimeWindow X alpha beta) n)
        (divisorCount (reportPrimeWindow X gamma delta) n) *
        (n : Real) / Real.exp rho ≤ (F n : Real) := by
    simpa [reportPrimeWindow, X, k] using hF hnotPair
  dsimp only
  change min
      ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
      ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) *
      (n : Real) / Real.exp rho ≤ (F n : Real)
  calc
    min
        ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
        ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) *
        (n : Real) / Real.exp rho ≤
      min (divisorCount (reportPrimeWindow X alpha beta) n)
          (divisorCount (reportPrimeWindow X gamma delta) n) *
          (n : Real) / Real.exp rho := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hmin (by positivity)) (Real.exp_pos rho).le
    _ ≤ (F n : Real) := hbase

/- Density-one closure of the adjustable two-window construction. -/
theorem exists_density_one_dyadicTrackA_F_lower_of_mass_adjustable
    {alpha beta gamma delta rho epsilon : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetagamma : beta ≤ gamma)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1) (hbetadelta : beta + delta < 1)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon)
    (hmass1 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X alpha beta)
      atTop atTop)
    (hmass2 : Tendsto (fun X : Nat => reportPrimeWindowEndpointMass X gamma delta)
      atTop atTop) :
    ∃ A : Set Nat, A.HasDensity 1 ∧
      ∀ᶠ n : Nat in atTop, n ∈ A →
        let X := dyadicReportEndpoint (Nat.log 2 n)
        min
            ((1 - epsilon) * reportPrimeWindowEndpointMass X alpha beta)
            ((1 - epsilon) * reportPrimeWindowEndpointMass X gamma delta) *
            (n : Real) / Real.exp rho ≤ (F n : Real) := by
  let S := dyadicTrackAExceptionalSetAdjustable
    alpha beta gamma delta rho epsilon
  refine ⟨Sᶜ, ?_, ?_⟩
  · exact compl_hasDensity_one_of_hasDensity_zero
      (dyadicTrackAExceptionalSetAdjustable_hasDensity_zero_of_mass
        halpha hbeta hbetagamma hdelta0 hdelta1 hbetadelta hrho hepsilon
        hmass1 hmass2)
  · filter_upwards [eventually_F_lower_off_dyadicTrackA_adjustable_exception
      (alpha := alpha) hbetagamma hdelta0 hdelta1 hbetadelta hrho] with n hn hmem
    exact hn hmem

end

end Erdos878

#print axioms Erdos878.tendsto_reportLowDivisorExceptionalRatioAdjustable_zero_of_mass
#print axioms Erdos878.dyadicTrackAExceptionalSetAdjustable_hasDensity_zero_of_mass
#print axioms Erdos878.eventually_F_lower_off_dyadicTrackA_adjustable_exception
#print axioms Erdos878.exists_density_one_dyadicTrackA_F_lower_of_mass_adjustable

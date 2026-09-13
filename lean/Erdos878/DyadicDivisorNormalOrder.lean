import Erdos878.GeometricBlockDensity

/-!
# Dyadic normal order for the two report windows

This file packages the second-moment part of Track A in the same fixed-block language as the
bad-pair estimate.  Intersecting each window with its integer endpoint makes containment
automatic; the only analytic inputs are divergence of the two reciprocal prime-window masses.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

noncomputable section

def reportPrimeWindow (X : ℕ) (a b : ℝ) : Finset ℕ :=
  primeWindow (Real.log (X : ℝ)) a b

def reportPrimeWindowInEndpoint (X : ℕ) (a b : ℝ) : Finset ℕ :=
  reportPrimeWindow X a b ∩ Finset.Icc 1 X

def reportPrimeWindowEndpointMass (X : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ reportPrimeWindowInEndpoint X a b, ((p : ℝ)⁻¹)

theorem divisorCount_mono {R S : Finset ℕ} (hRS : R ⊆ S) (n : ℕ) :
    divisorCount R n ≤ divisorCount S n := by
  unfold divisorCount
  exact_mod_cast Finset.card_le_card (by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hRS hp'.1, hp'.2⟩)

def reportLowDivisorIntegersUpTo
    (X : ℕ) (α β γ δ : ℝ) : Finset ℕ :=
  ((Finset.Icc 1 X).filter (fun n ↦
      divisorCount (reportPrimeWindowInEndpoint X α β) n <
        reportPrimeWindowEndpointMass X α β / 2)) ∪
    ((Finset.Icc 1 X).filter (fun n ↦
      divisorCount (reportPrimeWindowInEndpoint X γ δ) n <
        reportPrimeWindowEndpointMass X γ δ / 2))

/- This is the exact global-endpoint normal-order interface furnished by the sharp finite
second-moment estimate in `UnionBound`. -/
theorem tendsto_reportLowDivisorExceptionalRatio_zero_of_mass
    {α β γ δ : ℝ}
    (hmass₁ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X α β)
      atTop atTop)
    (hmass₂ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X γ δ)
      atTop atTop) :
    Tendsto (fun X : ℕ ↦
      ((reportLowDivisorIntegersUpTo X α β γ δ).card : ℝ) / (X : ℝ))
      atTop (nhds 0) := by
  have hμ₁ := hmass₁.eventually (eventually_gt_atTop (0 : ℝ))
  have hμ₂ := hmass₂.eventually (eventually_gt_atTop (0 : ℝ))
  have hinvμ₁ := hmass₁.inv_tendsto_atTop
  have hinvμ₂ := hmass₂.inv_tendsto_atTop
  unfold reportLowDivisorIntegersUpTo reportPrimeWindowEndpointMass
  exact
    tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
      (fun X ↦ reportPrimeWindowInEndpoint X α β)
      (fun X ↦ reportPrimeWindowInEndpoint X γ δ)
      (fun X p hp ↦ (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2.1)
      (fun X p hp ↦ (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2.1)
      (fun X ↦ Finset.inter_subset_right)
      (fun X ↦ Finset.inter_subset_right)
      hμ₁ hμ₂ hinvμ₁ hinvμ₂

def dyadicReportLowDivisorIntegers
    (k : ℕ) (α β γ δ : ℝ) : Finset ℕ :=
  reportLowDivisorIntegersUpTo (dyadicReportEndpoint k) α β γ δ

def dyadicReportLowDivisorExceptionalSet
    (α β γ δ : ℝ) : Set ℕ :=
  dyadicBlockExceptionalSet
    (fun k ↦ dyadicReportLowDivisorIntegers k α β γ δ)

/- The global endpoint ratio may be sampled on powers of two and geometrically stitched into one
fixed density-zero subset of the natural numbers. -/
theorem dyadicReportLowDivisorExceptionalSet_hasDensity_zero_of_mass
    {α β γ δ : ℝ}
    (hmass₁ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X α β)
      atTop atTop)
    (hmass₂ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X γ δ)
      atTop atTop) :
    (dyadicReportLowDivisorExceptionalSet α β γ δ).HasDensity 0 := by
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hratio := (tendsto_reportLowDivisorExceptionalRatio_zero_of_mass
    hmass₁ hmass₂).comp hendpoint
  simpa [dyadicReportLowDivisorExceptionalSet, dyadicReportLowDivisorIntegers,
    Function.comp_def] using
      dyadicBlockExceptionalSet_hasDensity_zero_of_endpoint_ratio
        (fun k ↦ dyadicReportLowDivisorIntegers k α β γ δ) hratio

def dyadicTrackAExceptionalSet
    (α β γ δ rho : ℝ) : Set ℕ :=
  dyadicReportPairExceptionalSet α β γ δ rho ∪
    dyadicReportLowDivisorExceptionalSet α β γ δ

/- Bad pairs and atypically small divisor counts can be removed simultaneously. -/
theorem dyadicTrackAExceptionalSet_hasDensity_zero_of_mass
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmass₁ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X α β)
      atTop atTop)
    (hmass₂ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X γ δ)
      atTop atTop) :
    (dyadicTrackAExceptionalSet α β γ δ rho).HasDensity 0 := by
  unfold dyadicTrackAExceptionalSet
  exact hasDensity_zero_union
    (dyadicReportPairExceptionalSet_hasDensity_zero
      hα hβ hβγ hδ0 hδ1 hβδ hrho)
    (dyadicReportLowDivisorExceptionalSet_hasDensity_zero_of_mass
      hmass₁ hmass₂)

/- Outside the combined exceptional set, the two reciprocal masses give a direct pointwise lower
bound for `F`.  Thus all remaining sharp-coefficient work is analytic: estimate these masses. -/
theorem eventually_F_lower_off_dyadicTrackA_exception
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      n ∉ dyadicTrackAExceptionalSet α β γ δ rho →
      let X := dyadicReportEndpoint (Nat.log 2 n)
      min (reportPrimeWindowEndpointMass X α β / 2)
          (reportPrimeWindowEndpointMass X γ δ / 2) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  filter_upwards
      [eventually_F_lower_off_dyadic_report_exception
        (α := α) hβγ hδ0 hδ1 hβδ hrho,
       eventually_ge_atTop (1 : ℕ)] with n hF hn
  intro hnot
  let k := Nat.log 2 n
  let X := dyadicReportEndpoint k
  have hn0 : n ≠ 0 := by omega
  have hnX : n < X := by
    simpa [X, k, dyadicReportEndpoint] using
      Nat.lt_pow_succ_log_self (by norm_num) n
  have hnIcc : n ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hn, hnX.le⟩
  have hnotPair : n ∉ dyadicReportPairExceptionalSet α β γ δ rho := by
    intro hmem
    exact hnot (Set.mem_union_left _ hmem)
  have hnotLow : n ∉ dyadicReportLowDivisorExceptionalSet α β γ δ := by
    intro hmem
    exact hnot (Set.mem_union_right _ hmem)
  have hnotBlock : n ∉ dyadicReportLowDivisorIntegers k α β γ δ := by
    intro hmem
    apply hnotLow
    exact ⟨hn0, by simpa [k] using hmem⟩
  have hcount₁ : reportPrimeWindowEndpointMass X α β / 2 ≤
      divisorCount (reportPrimeWindowInEndpoint X α β) n := by
    apply le_of_not_gt
    intro hlt
    apply hnotBlock
    unfold dyadicReportLowDivisorIntegers reportLowDivisorIntegersUpTo
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
  have hcount₂ : reportPrimeWindowEndpointMass X γ δ / 2 ≤
      divisorCount (reportPrimeWindowInEndpoint X γ δ) n := by
    apply le_of_not_gt
    intro hlt
    apply hnotBlock
    unfold dyadicReportLowDivisorIntegers reportLowDivisorIntegersUpTo
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnIcc, hlt⟩)
  have hcountFull₁ : reportPrimeWindowEndpointMass X α β / 2 ≤
      divisorCount (reportPrimeWindow X α β) n :=
    hcount₁.trans (divisorCount_mono Finset.inter_subset_left n)
  have hcountFull₂ : reportPrimeWindowEndpointMass X γ δ / 2 ≤
      divisorCount (reportPrimeWindow X γ δ) n :=
    hcount₂.trans (divisorCount_mono Finset.inter_subset_left n)
  have hmin := min_le_min hcountFull₁ hcountFull₂
  have hbase : min
        (divisorCount (reportPrimeWindow X α β) n)
        (divisorCount (reportPrimeWindow X γ δ) n) *
        (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
    simpa [reportPrimeWindow, X, k] using hF hnotPair
  dsimp only
  change min (reportPrimeWindowEndpointMass X α β / 2)
      (reportPrimeWindowEndpointMass X γ δ / 2) * (n : ℝ) / Real.exp rho ≤ (F n : ℝ)
  calc
    min (reportPrimeWindowEndpointMass X α β / 2)
          (reportPrimeWindowEndpointMass X γ δ / 2) * (n : ℝ) / Real.exp rho ≤
        min (divisorCount (reportPrimeWindow X α β) n)
          (divisorCount (reportPrimeWindow X γ δ) n) * (n : ℝ) /
            Real.exp rho := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hmin (by positivity)) (Real.exp_pos rho).le
    _ ≤ (F n : ℝ) := hbase

/- Density-one closure of the preceding two results.  This is the completed probabilistic and
combinatorial Track-A shell; the two `hmass` premises are precisely the remaining number-theory
lemma, and sharper asymptotics for those masses determine the final constant. -/
theorem exists_density_one_dyadicTrackA_F_lower_of_mass
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmass₁ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X α β)
      atTop atTop)
    (hmass₂ : Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X γ δ)
      atTop atTop) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : ℕ in atTop, n ∈ A →
        let X := dyadicReportEndpoint (Nat.log 2 n)
        min (reportPrimeWindowEndpointMass X α β / 2)
            (reportPrimeWindowEndpointMass X γ δ / 2) *
            (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  let S := dyadicTrackAExceptionalSet α β γ δ rho
  refine ⟨Sᶜ, ?_, ?_⟩
  · exact compl_hasDensity_one_of_hasDensity_zero
      (dyadicTrackAExceptionalSet_hasDensity_zero_of_mass
        hα hβ hβγ hδ0 hδ1 hβδ hrho hmass₁ hmass₂)
  · filter_upwards [eventually_F_lower_off_dyadicTrackA_exception
      (α := α) hβγ hδ0 hδ1 hβδ hrho] with n hn hmem
    exact hn hmem

end

end Erdos878

#print axioms Erdos878.dyadicReportLowDivisorExceptionalSet_hasDensity_zero_of_mass
#print axioms Erdos878.dyadicTrackAExceptionalSet_hasDensity_zero_of_mass
#print axioms Erdos878.eventually_F_lower_off_dyadicTrackA_exception
#print axioms Erdos878.exists_density_one_dyadicTrackA_F_lower_of_mass

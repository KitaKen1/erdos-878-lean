import Erdos878.ReportLowerBound
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Density zero from dyadic block estimates

This module removes a false monotonicity requirement from the moving bad-pair strategy.  An
integer `n` is assigned to the unique block with index `Nat.log 2 n`; the report scale is fixed
on that whole block.  A geometric summation shows that exceptional proportions tending to zero
at block endpoints imply natural density zero for the resulting single set of integers.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

/-- Geometric summation preserves a vanishing endpoint ratio. -/
theorem tendsto_dyadic_card_partialSum_ratio_zero
    (a : ℕ → ℕ)
    (h : Tendsto (fun k : ℕ ↦ (a k : ℝ) / (2 : ℝ) ^ k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ ↦
      ((∑ i ∈ Finset.range (k + 1), a i : ℕ) : ℝ) / (2 : ℝ) ^ k)
      atTop (nhds 0) := by
  have hf : (fun k : ℕ ↦ (a k : ℝ)) =o[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
    apply (Asymptotics.isLittleO_iff_tendsto (fun k hk ↦
      (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0) hk).elim)).2
    exact h
  have hgsum : Tendsto (fun n : ℕ ↦
      ∑ i ∈ Finset.range n, (2 : ℝ) ^ i) atTop atTop := by
    have hp : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hs : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n - 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hp
    convert hs using 1
    funext n
    have hgeom := geom_sum_mul (2 : ℝ) n
    norm_num at hgeom ⊢
    exact hgeom
  have hsum : (fun n : ℕ ↦ ∑ i ∈ Finset.range n, (a i : ℝ)) =o[atTop]
      (fun n : ℕ ↦ ∑ i ∈ Finset.range n, (2 : ℝ) ^ i) :=
    hf.sum_range (fun i ↦ by positivity) hgsum
  have hsum' : (fun k : ℕ ↦ ∑ i ∈ Finset.range (k + 1), (a i : ℝ)) =o[atTop]
      (fun k : ℕ ↦ ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i) := by
    simpa [Function.comp_def] using hsum.comp_tendsto (tendsto_add_atTop_nat 1)
  have hbig : (fun k : ℕ ↦ ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i) =O[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
    apply Asymptotics.isBigO_iff.2
    refine ⟨2, Filter.Eventually.of_forall (fun k ↦ ?_)⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ by positivity)),
      abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k)]
    have hgeom := geom_sum_mul (2 : ℝ) (k + 1)
    norm_num at hgeom
    rw [hgeom, pow_succ]
    linarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
  have hlittle : (fun k : ℕ ↦ ∑ i ∈ Finset.range (k + 1), (a i : ℝ)) =o[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := hsum'.trans_isBigO hbig
  simpa only [Nat.cast_sum] using hlittle.tendsto_div_nhds_zero

/-- The fixed set obtained by testing each integer against the exceptional filter assigned to
its own dyadic block. -/
def dyadicBlockExceptionalSet (E : ℕ → Finset ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ n ∈ E (Nat.log 2 n)}

theorem dyadicBlockExceptionalSet_hasDensity_zero
    (E : ℕ → Finset ℕ)
    (hE : Tendsto (fun k : ℕ ↦ ((E k).card : ℝ) / (2 : ℝ) ^ k)
      atTop (nhds 0)) :
    (dyadicBlockExceptionalSet E).HasDensity 0 := by
  let U : ℕ → Finset ℕ := fun X ↦
    (Finset.range (Nat.log 2 X + 1)).biUnion E
  have hcover : ∀ X : ℕ,
      dyadicBlockExceptionalSet E ∩ Set.Icc 1 X ⊆ (U X : Set ℕ) := by
    intro X n hn
    have hnS : n ≠ 0 ∧ n ∈ E (Nat.log 2 n) := hn.1
    have hlog : Nat.log 2 n ≤ Nat.log 2 X := Nat.log_mono_right hn.2.2
    unfold U
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨Nat.log 2 n, Finset.mem_range.mpr (by omega), hnS.2⟩
  have hsum := tendsto_dyadic_card_partialSum_ratio_zero
    (fun k ↦ (E k).card) hE
  have hlog : Tendsto (fun X : ℕ ↦ Nat.log 2 X) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hright : Tendsto (fun X : ℕ ↦
      ((∑ i ∈ Finset.range (Nat.log 2 X + 1), (E i).card : ℕ) : ℝ) /
        (2 : ℝ) ^ (Nat.log 2 X)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hsum.comp hlog
  have hbound : Tendsto (fun X : ℕ ↦ ((U X).card : ℝ) / (X : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
      have hcardNat : (U X).card ≤
          ∑ i ∈ Finset.range (Nat.log 2 X + 1), (E i).card := by
        unfold U
        exact Finset.card_biUnion_le
      have hcard : ((U X).card : ℝ) ≤
          ((∑ i ∈ Finset.range (Nat.log 2 X + 1), (E i).card : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 hX.ne'
      have hpowR : (2 : ℝ) ^ Nat.log 2 X ≤ (X : ℝ) := by exact_mod_cast hpow
      calc
        ((U X).card : ℝ) / (X : ℝ) ≤
            ((∑ i ∈ Finset.range (Nat.log 2 X + 1), (E i).card : ℕ) : ℝ) /
              (X : ℝ) := div_le_div_of_nonneg_right hcard (by positivity)
        _ ≤ ((∑ i ∈ Finset.range (Nat.log 2 X + 1), (E i).card : ℕ) : ℝ) /
              (2 : ℝ) ^ Nat.log 2 X := by
          apply div_le_div_of_nonneg_left
          · positivity
          · positivity
          · exact hpowR
    · exact hright
  exact hasDensity_zero_of_Icc_filter_cover
    (dyadicBlockExceptionalSet E) U hcover hbound

def dyadicReportEndpoint (k : ℕ) : ℕ := 2 ^ (k + 1)

theorem dyadicBlockExceptionalSet_hasDensity_zero_of_endpoint_ratio
    (E : ℕ → Finset ℕ)
    (hE : Tendsto (fun k : ℕ ↦ ((E k).card : ℝ) /
      (dyadicReportEndpoint k : ℝ)) atTop (nhds 0)) :
    (dyadicBlockExceptionalSet E).HasDensity 0 := by
  have htwo := hE.const_mul 2
  apply dyadicBlockExceptionalSet_hasDensity_zero E
  convert htwo using 1
  · funext k
    rw [dyadicReportEndpoint, Nat.cast_pow, pow_succ]
    field_simp
    ring
  · norm_num

noncomputable def dyadicReportBadIntegers
    (k : ℕ) (α β γ δ rho : ℝ) : Finset ℕ :=
  divisibleBySomePairUpTo (dyadicReportEndpoint k)
    (badPairsAtReportScale (Real.log (dyadicReportEndpoint k : ℝ)) α β γ δ rho)

theorem divisibleBySomePairUpTo_mono
    (pairs : Finset (ℕ × ℕ)) {X Y : ℕ} (hXY : X ≤ Y) :
    divisibleBySomePairUpTo X pairs ⊆ divisibleBySomePairUpTo Y pairs := by
  intro n hn
  unfold divisibleBySomePairUpTo at hn ⊢
  rw [Finset.mem_biUnion] at hn ⊢
  obtain ⟨pq, hpq, hn⟩ := hn
  refine ⟨pq, hpq, ?_⟩
  unfold divisibleUpTo at hn ⊢
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr (by
    have hnX := Finset.mem_range.mp hn.1
    omega), hn.2⟩

/- On every sufficiently late dyadic block, avoiding its fixed endpoint exception gives the
report lower bound.  The logarithmic scale condition loses only a factor two: if
`2^k ≤ n < 2^(k+1)` and `k ≥ 1`, then `log(2^(k+1))/2 ≤ log n`. -/
theorem eventually_F_lower_on_dyadic_report_block
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      2 ^ k ≤ n → n < dyadicReportEndpoint k →
      n ∉ dyadicReportBadIntegers k α β γ δ rho →
      min
          (divisorCount
            (primeWindow (Real.log (dyadicReportEndpoint k : ℝ)) α β) n)
          (divisorCount
            (primeWindow (Real.log (dyadicReportEndpoint k : ℝ)) γ δ) n) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hscale : Tendsto
      (fun k : ℕ ↦ Real.log (dyadicReportEndpoint k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hendpoint)
  filter_upwards
      [hscale.eventually
        (eventually_F_lower_of_report_nonexceptional hβγ hδ0 hδ1 hβδ hrho),
       eventually_ge_atTop (1 : ℕ)] with k hreport hk
  intro n hkn hnX hnonexceptional
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ k := by positivity
    omega
  have hpowR : (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hloglo := Real.log_le_log
    (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hpowR
  rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num,
    Real.log_pow] at hloglo
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcoef : (((k + 1 : ℕ) : ℝ)) ≤ 2 * (k : ℝ) := by
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  have hscaleHalf : Real.log (dyadicReportEndpoint k : ℝ) / 2 ≤
      Real.log (n : ℝ) := by
    rw [dyadicReportEndpoint, Nat.cast_pow, Real.log_pow]
    calc
      ((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) / 2 ≤
          (2 * (k : ℝ)) * Real.log (2 : ℝ) / 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef hlog2.le) (by norm_num)
      _ = (k : ℝ) * Real.log (2 : ℝ) := by ring
      _ ≤ Real.log (n : ℝ) := by simpa [mul_comm] using hloglo
  apply hreport n hn0 hscaleHalf
  intro hnexceptional
  apply hnonexceptional
  exact divisibleBySomePairUpTo_mono
    (badPairsAtReportScale (Real.log (dyadicReportEndpoint k : ℝ)) α β γ δ rho)
    (Nat.le_of_lt hnX) hnexceptional

def dyadicReportPairExceptionalSet
    (α β γ δ rho : ℝ) : Set ℕ :=
  dyadicBlockExceptionalSet (fun k ↦ dyadicReportBadIntegers k α β γ δ rho)

/- The report's proved reciprocal bad-pair estimate now gives one fixed density-zero exceptional
set without any monotonicity assumption on the moving windows or approximation cutoff. -/
theorem dyadicReportPairExceptionalSet_hasDensity_zero
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    (dyadicReportPairExceptionalSet α β γ δ rho).HasDensity 0 := by
  let X : ℕ → ℕ := dyadicReportEndpoint
  let E : ℕ → Finset ℕ := fun k ↦ dyadicReportBadIntegers k α β γ δ rho
  have hX : Tendsto X atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hratioEndpoint : Tendsto (fun k : ℕ ↦ ((E k).card : ℝ) / (X k : ℝ))
      atTop (nhds 0) := by
    have hbase := tendsto_badPairExceptionalRatio_zero_of_log_report_scale_default
      hα hβ hβγ hδ0 hδ1 hβδ hrho
    simpa [E, X, dyadicReportBadIntegers, Function.comp_def] using hbase.comp hX
  have hratio : Tendsto (fun k : ℕ ↦ ((E k).card : ℝ) / (2 : ℝ) ^ k)
      atTop (nhds 0) := by
    have htwo := hratioEndpoint.const_mul 2
    convert htwo using 1
    · funext k
      dsimp [E, X, dyadicReportEndpoint]
      rw [Nat.cast_pow, pow_succ]
      field_simp
      ring
    · norm_num
  simpa [dyadicReportPairExceptionalSet, E] using
    dyadicBlockExceptionalSet_hasDensity_zero E hratio

/- Each integer is now assigned to its own dyadic block.  Outside the single density-zero bad-pair
set, the report lower bound therefore holds eventually with no moving-family monotonicity premise. -/
theorem eventually_F_lower_off_dyadic_report_exception
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      n ∉ dyadicReportPairExceptionalSet α β γ δ rho →
      min
          (divisorCount
            (primeWindow
              (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) α β) n)
          (divisorCount
            (primeWindow
              (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) γ δ) n) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hblocks := eventually_F_lower_on_dyadic_report_block
    (α := α) hβγ hδ0 hδ1 hβδ hrho
  filter_upwards [hlog.eventually hblocks, eventually_ge_atTop (1 : ℕ)] with n hblock hn
  intro hnotexceptional
  have hn0 : n ≠ 0 := by omega
  apply hblock n (Nat.pow_log_le_self 2 hn0)
      (Nat.lt_pow_succ_log_self (by norm_num) n)
  intro hnexceptional
  apply hnotexceptional
  exact ⟨hn0, hnexceptional⟩

end Erdos878

#print axioms Erdos878.dyadicReportPairExceptionalSet_hasDensity_zero
#print axioms Erdos878.eventually_F_lower_off_dyadic_report_exception

import Erdos878.UnionBound

/-!
# Adjustable normal-order threshold

The original Track-A normal-order layer used the convenient threshold `mu / 2`.  Chebyshev's
inequality actually permits the threshold `(1 - epsilon) * mu` for every fixed positive
`epsilon`.  This module records that stronger interface without changing the stable half-mean
API in `UnionBound`.

The price is the expected factor `epsilon ^ (-2)` in the exceptional-set bound.  Since the
reciprocal prime mass tends to infinity, that factor is harmless for every fixed positive
`epsilon`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos878

noncomputable section

/- Finite Chebyshev with a relative, rather than absolute, deficit. -/
theorem card_filter_lt_one_sub_mul_le_of_sum_sq_le
    {alpha : Type*} [DecidableEq alpha] (U : Finset alpha) (Z : alpha -> Real)
    {mu epsilon V : Real} (hmu : 0 < mu) (hepsilon : 0 < epsilon)
    (hvar : ∑ x ∈ U, (Z x - mu) ^ 2 ≤ V) :
    (((U.filter (fun x => Z x < (1 - epsilon) * mu)).card : Nat) : Real) *
        (epsilon * mu) ^ 2 ≤ V := by
  have h := card_filter_lt_le_of_sum_sq_le U Z
    (μ := mu) (t := epsilon * mu) (V := V) (mul_pos hepsilon hmu) hvar
  simpa [sub_mul] using h

/- Normalized finite form of the adjustable Chebyshev estimate. -/
theorem exceptionalRatio_lt_one_sub_mul_le_of_sum_sq_le
    {alpha : Type*} [DecidableEq alpha] (U : Finset alpha) (Z : alpha -> Real)
    (X : Nat) {mu epsilon V : Real} (hmu : 0 < mu) (hepsilon : 0 < epsilon)
    (hX : 0 < X) (hvar : ∑ x ∈ U, (Z x - mu) ^ 2 ≤ V) :
    (((U.filter (fun x => Z x < (1 - epsilon) * mu)).card : Nat) : Real) /
        (X : Real) ≤ V / ((epsilon * mu) ^ 2 * (X : Real)) := by
  have hcard := card_filter_lt_one_sub_mul_le_of_sum_sq_le
    U Z hmu hepsilon hvar
  have het : 0 < epsilon * mu := mul_pos hepsilon hmu
  have hetSq : 0 < (epsilon * mu) ^ 2 := sq_pos_of_pos het
  have hXreal : 0 < (X : Real) := by exact_mod_cast hX
  apply (div_le_iff₀ hXreal).2
  have hcard' :
      (((U.filter (fun x => Z x < (1 - epsilon) * mu)).card : Nat) : Real) ≤
        V / (epsilon * mu) ^ 2 := by
    exact (le_div_iff₀ hetSq).2 hcard
  calc
    (((U.filter (fun x => Z x < (1 - epsilon) * mu)).card : Nat) : Real) ≤
        V / (epsilon * mu) ^ 2 := hcard'
    _ = (V / ((epsilon * mu) ^ 2 * (X : Real))) * (X : Real) := by
      field_simp [ne_of_gt hetSq, ne_of_gt hXreal]

/- The sharp prime-family variance estimate with an adjustable relative deficit. -/
theorem exceptionalRatio_divisorCount_lt_one_sub_mul_le_of_primeReciprocal_sharp
    (R : Finset Nat) (X : Nat) {epsilon : Real}
    (hprime : ∀ p ∈ R, Nat.Prime p) (hX : 0 < X) (hepsilon : 0 < epsilon)
    (hmu : 0 < ∑ p ∈ R, ((p : Real)⁻¹)) :
    (((((Finset.Icc 1 X).filter (fun n =>
        divisorCount R n < (1 - epsilon) *
          (∑ p ∈ R, ((p : Real)⁻¹)))).card : Nat) : Real) / (X : Real)) ≤
      ((X : Real) * (∑ p ∈ R, ((p : Real)⁻¹)) +
        2 * (∑ p ∈ R, ((p : Real)⁻¹)) * (R.card : Real)) /
        ((epsilon * (∑ p ∈ R, ((p : Real)⁻¹))) ^ 2 * (X : Real)) := by
  exact exceptionalRatio_lt_one_sub_mul_le_of_sum_sq_le
    (Finset.Icc 1 X) (divisorCount R) X hmu hepsilon hX
      (sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp R X hprime hX)

/- Algebraic form exposing the two quantities which vanish for a moving prime window. -/
theorem exceptionalRatio_divisorCount_lt_one_sub_mul_le_of_primeReciprocal_sharp_additive
    (R : Finset Nat) (X : Nat) {epsilon : Real}
    (hprime : ∀ p ∈ R, Nat.Prime p) (hX : 0 < X) (hepsilon : 0 < epsilon)
    (hmu : 0 < ∑ p ∈ R, ((p : Real)⁻¹)) :
    (((((Finset.Icc 1 X).filter (fun n =>
        divisorCount R n < (1 - epsilon) *
          (∑ p ∈ R, ((p : Real)⁻¹)))).card : Nat) : Real) / (X : Real)) ≤
      (1 / epsilon ^ 2) * (∑ p ∈ R, ((p : Real)⁻¹))⁻¹ +
        (2 / epsilon ^ 2) *
          ((R.card : Real) /
            ((∑ p ∈ R, ((p : Real)⁻¹)) * (X : Real))) := by
  have hbase :=
    exceptionalRatio_divisorCount_lt_one_sub_mul_le_of_primeReciprocal_sharp
      R X hprime hX hepsilon hmu
  calc
    (((((Finset.Icc 1 X).filter (fun n =>
        divisorCount R n < (1 - epsilon) *
          (∑ p ∈ R, ((p : Real)⁻¹)))).card : Nat) : Real) / (X : Real)) ≤
      ((X : Real) * (∑ p ∈ R, ((p : Real)⁻¹)) +
        2 * (∑ p ∈ R, ((p : Real)⁻¹)) * (R.card : Real)) /
        ((epsilon * (∑ p ∈ R, ((p : Real)⁻¹))) ^ 2 * (X : Real)) := hbase
    _ = (1 / epsilon ^ 2) * (∑ p ∈ R, ((p : Real)⁻¹))⁻¹ +
        (2 / epsilon ^ 2) *
          ((R.card : Real) /
            ((∑ p ∈ R, ((p : Real)⁻¹)) * (X : Real))) := by
      field_simp [ne_of_gt hepsilon, ne_of_gt hmu,
        ne_of_gt (show (0 : Real) < (X : Real) by exact_mod_cast hX)]

/- For a prime family contained in `[1, X]`, divergence of reciprocal mass alone makes the
adjustable exceptional proportion tend to zero. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_adjustable
    (R : Nat -> Finset Nat) {epsilon : Real} (hepsilon : 0 < epsilon)
    (hprime : ∀ X : Nat, ∀ p ∈ R X, Nat.Prime p)
    (hsub : ∀ X : Nat, R X ⊆ Finset.Icc 1 X)
    (hmass : Tendsto (fun X : Nat => ∑ p ∈ R X, ((p : Real)⁻¹)) atTop atTop) :
    Tendsto (fun X : Nat =>
      (((((Finset.Icc 1 X).filter (fun n =>
          divisorCount (R X) n < (1 - epsilon) *
            (∑ p ∈ R X, ((p : Real)⁻¹)))).card : Nat) : Real) / (X : Real)))
      atTop (nhds 0) := by
  have hmu : ∀ᶠ X : Nat in atTop, 0 < ∑ p ∈ R X, ((p : Real)⁻¹) :=
    hmass.eventually (eventually_gt_atTop (0 : Real))
  have hinvmu : Tendsto
      (fun X : Nat => (∑ p ∈ R X, ((p : Real)⁻¹))⁻¹) atTop (nhds 0) :=
    hmass.inv_tendsto_atTop
  have hcard : Tendsto (fun X : Nat =>
      ((R X).card : Real) /
        ((∑ p ∈ R X, ((p : Real)⁻¹)) * (X : Real))) atTop (nhds 0) :=
    tendsto_card_div_mass_mul_X_zero_of_subset_Icc R hsub hmu hinvmu
  have hupper : ∀ᶠ X : Nat in atTop,
      (((((Finset.Icc 1 X).filter (fun n =>
          divisorCount (R X) n < (1 - epsilon) *
            (∑ p ∈ R X, ((p : Real)⁻¹)))).card : Nat) : Real) / (X : Real)) ≤
        (1 / epsilon ^ 2) * (∑ p ∈ R X, ((p : Real)⁻¹))⁻¹ +
          (2 / epsilon ^ 2) *
            (((R X).card : Real) /
              ((∑ p ∈ R X, ((p : Real)⁻¹)) * (X : Real))) := by
    filter_upwards [eventually_gt_atTop (0 : Nat), hmu] with X hX hmuX
    exact exceptionalRatio_divisorCount_lt_one_sub_mul_le_of_primeReciprocal_sharp_additive
      (R X) X (hprime X) hX hepsilon hmuX
  have hfirst : Tendsto (fun X : Nat =>
      (1 / epsilon ^ 2) * (∑ p ∈ R X, ((p : Real)⁻¹))⁻¹) atTop (nhds 0) := by
    simpa only [one_div, mul_zero] using hinvmu.const_mul ((epsilon ^ 2)⁻¹)
  have hsecond : Tendsto (fun X : Nat =>
      (2 / epsilon ^ 2) *
        (((R X).card : Real) /
          ((∑ p ∈ R X, ((p : Real)⁻¹)) * (X : Real)))) atTop (nhds 0) := by
    simpa using hcard.const_mul (2 / epsilon ^ 2)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X => by positivity)
  · exact hupper
  · simpa only [add_zero] using hfirst.add hsecond

/- Two adjustable prime windows may be removed simultaneously. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_adjustable
    (R1 R2 : Nat -> Finset Nat) {epsilon : Real} (hepsilon : 0 < epsilon)
    (hprime1 : ∀ X : Nat, ∀ p ∈ R1 X, Nat.Prime p)
    (hprime2 : ∀ X : Nat, ∀ p ∈ R2 X, Nat.Prime p)
    (hsub1 : ∀ X : Nat, R1 X ⊆ Finset.Icc 1 X)
    (hsub2 : ∀ X : Nat, R2 X ⊆ Finset.Icc 1 X)
    (hmass1 : Tendsto (fun X : Nat => ∑ p ∈ R1 X, ((p : Real)⁻¹)) atTop atTop)
    (hmass2 : Tendsto (fun X : Nat => ∑ p ∈ R2 X, ((p : Real)⁻¹)) atTop atTop) :
    Tendsto (fun X : Nat =>
      (((((Finset.Icc 1 X).filter (fun n =>
          divisorCount (R1 X) n < (1 - epsilon) *
            (∑ p ∈ R1 X, ((p : Real)⁻¹)))) ∪
        ((Finset.Icc 1 X).filter (fun n =>
          divisorCount (R2 X) n < (1 - epsilon) *
            (∑ p ∈ R2 X, ((p : Real)⁻¹))))).card : Nat) : Real) / (X : Real))
      atTop (nhds 0) := by
  have h1 := tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_adjustable
    R1 hepsilon hprime1 hsub1 hmass1
  have h2 := tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_adjustable
    R2 hepsilon hprime2 hsub2 hmass2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with X hX
    have hcardNat := Finset.card_union_le
      ((Finset.Icc 1 X).filter (fun n =>
        divisorCount (R1 X) n < (1 - epsilon) *
          (∑ p ∈ R1 X, ((p : Real)⁻¹))))
      ((Finset.Icc 1 X).filter (fun n =>
        divisorCount (R2 X) n < (1 - epsilon) *
          (∑ p ∈ R2 X, ((p : Real)⁻¹))))
    have hcardReal :
        (((((Finset.Icc 1 X).filter (fun n =>
            divisorCount (R1 X) n < (1 - epsilon) *
              (∑ p ∈ R1 X, ((p : Real)⁻¹)))) ∪
          ((Finset.Icc 1 X).filter (fun n =>
            divisorCount (R2 X) n < (1 - epsilon) *
              (∑ p ∈ R2 X, ((p : Real)⁻¹))))).card : Nat) : Real) ≤
          ((((Finset.Icc 1 X).filter (fun n =>
            divisorCount (R1 X) n < (1 - epsilon) *
              (∑ p ∈ R1 X, ((p : Real)⁻¹)))).card : Nat) : Real) +
          ((((Finset.Icc 1 X).filter (fun n =>
            divisorCount (R2 X) n < (1 - epsilon) *
              (∑ p ∈ R2 X, ((p : Real)⁻¹)))).card : Nat) : Real) := by
      exact_mod_cast hcardNat
    exact div_le_div_of_nonneg_right hcardReal (by positivity)
  · simpa only [add_zero, add_div] using h1.add h2

end

end Erdos878

#print axioms Erdos878.card_filter_lt_one_sub_mul_le_of_sum_sq_le
#print axioms Erdos878.exceptionalRatio_divisorCount_lt_one_sub_mul_le_of_primeReciprocal_sharp_additive
#print axioms Erdos878.tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_adjustable
#print axioms Erdos878.tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_adjustable

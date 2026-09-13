import Erdos878.TrackBPowerWindow
import Erdos878FC

/-!
# Track B: pack selected phase-window primes below the maximal-order endpoint

This module connects the new analytic prime family to the existing finite
`multipleBelow` and `maxUpTo f` machinery. The remaining hypotheses are stated
as explicit product and endpoint budgets.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

theorem goodPrime_family_prime {P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hS : S ⊆ logSquaredGoodPrimes P t) : ∀ p ∈ S, p.Prime := by
  intro p hp
  exact (mem_filter.mp (hS hp)).2

theorem goodPrime_family_product_le {P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hS : S ⊆ logSquaredGoodPrimes P t) :
    Erdos878.primeProduct S ≤ (16*P)^S.card := by
  apply Erdos878.primeProduct_le_pow_card
  intro p hp
  exact (mem_Ioc.mp (mem_filter.mp (mem_filter.mp (hS hp)).1).1).2

/-- If the packed multiple is above the common upper edge of the phase powers,
all selected phase exponents survive inside `Nat.log p (multipleBelow X S)`. -/
theorem phaseExponent_le_log_multipleBelow {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Erdos878.multipleBelow X S : ℝ)) :
    ∀ p ∈ S, phaseExponent t p ≤ Nat.log p (Erdos878.multipleBelow X S) := by
  intro p hp
  have hprime := goodPrime_family_prime hS p hp
  apply Nat.le_log_of_pow_le hprime.one_lt
  exact_mod_cast (goodPrime_phaseExponent_power_bounds P t hscale ht (hS hp)).2.trans hmultiple

/-- Complete finite Track-B packing step. The analytic phase-window lower bound
is now turned into a lower bound for the actual finite maximum. -/
theorem card_mul_exp_le_maxUpTo_f_of_goodPrime_family
    {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hprod : Erdos878.primeProduct S ≤ X)
    (hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Erdos878.multipleBelow X S : ℝ)) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) := by
  have hprime := goodPrime_family_prime hS
  have hexponents := phaseExponent_le_log_multipleBelow hscale ht hS hmultiple
  have hphase := sum_phaseExponent_power_lower hscale ht hS
  have hsum : (∑ p ∈ S, ((p : ℝ)^phaseExponent t p)) ≤
      ∑ p ∈ S, ((p ^ Nat.log p (Erdos878.multipleBelow X S) : ℕ) : ℝ) := by
    apply sum_le_sum
    intro p hp
    exact_mod_cast Nat.pow_le_pow_right (hprime p hp).pos (hexponents p hp)
  have hmaxNat := Erdos878.sum_primePower_le_maxUpTo_f_of_selected_primes S hprime hprod
  have hmax : (∑ p ∈ S,
      ((p ^ Nat.log p (Erdos878.multipleBelow X S) : ℕ) : ℝ)) ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) := by
    exact_mod_cast hmaxNat
  exact hphase.trans (hsum.trans hmax)

/-- The product hypothesis can be discharged from the uniform endpoint `p ≤ 16P`. -/
theorem card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_power_budget
    {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hbudget : (16*P)^S.card ≤ X)
    (hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Erdos878.multipleBelow X S : ℝ)) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) := by
  apply card_mul_exp_le_maxUpTo_f_of_goodPrime_family hscale ht hS
    ((goodPrime_family_product_le hS).trans hbudget) hmultiple

/-- A single additive budget discharges both the product bound and the lower
bound for the packed multiple. This is the finite interface for the eventual
parameter calculation. -/
theorem card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_additive_budget
    {X P : ℕ} {t : ℝ} {S : Finset ℕ}
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t)
    (hS : S ⊆ logSquaredGoodPrimes P t)
    (hbudget : Real.exp (t - 1/Real.log (P : ℝ)) +
      (((16*P)^S.card : ℕ) : ℝ) ≤ (X : ℝ)) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) := by
  have hprime := goodPrime_family_prime hS
  have hprodNat := goodPrime_family_product_le hS
  have hprod : Erdos878.primeProduct S ≤ X := by
    have hpowReal : ((((16*P)^S.card : ℕ) : ℝ)) ≤ (X : ℝ) :=
      hbudget.trans' (le_add_of_nonneg_left (Real.exp_pos _).le)
    exact hprodNat.trans (by exact_mod_cast hpowReal)
  have hgapNat := Erdos878.multipleBelow_add_primeProduct_gt X hprime
  have hgap : (X : ℝ) < (Erdos878.multipleBelow X S : ℝ) +
      (Erdos878.primeProduct S : ℝ) := by exact_mod_cast hgapNat
  have hprodReal : (Erdos878.primeProduct S : ℝ) ≤
      (((16*P)^S.card : ℕ) : ℝ) := by exact_mod_cast hprodNat
  have hmultiple : Real.exp (t - 1/Real.log (P : ℝ)) ≤
      (Erdos878.multipleBelow X S : ℝ) := by linarith
  exact card_mul_exp_le_maxUpTo_f_of_goodPrime_family hscale ht hS hprod hmultiple

end
end Erdos878.TrackB

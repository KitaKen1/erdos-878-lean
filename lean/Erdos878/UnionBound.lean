/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
/- Keep this module independent of `Mathlib.NumberTheory.SelbergSieve`: the LeanPool
   Brun--Titchmarsh input used by `Upstream` defines a same-named structure, so importing the
   umbrella `Mathlib` here creates a declaration collision when the two modules are combined. -/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite divisibility union bound

The bad-prime-pair strategy for Erdős Problem 878 needs no independence assumption.  This file
formalizes the exact finite union bound: the number of positive integers at most `X` divisible
by at least one product from a finite family is bounded by `X` times the corresponding
reciprocal weight.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos878

/-- Positive multiples of `d` not exceeding `X`. -/
def divisibleUpTo (X d : ℕ) : Finset ℕ :=
  (Finset.range X.succ).filter fun n ↦ n ≠ 0 ∧ d ∣ n

/-- Positive integers at most `X` divisible by the product of at least one pair in `pairs`. -/
def divisibleBySomePairUpTo (X : ℕ) (pairs : Finset (ℕ × ℕ)) : Finset ℕ :=
  pairs.biUnion fun pq ↦ divisibleUpTo X (pq.1 * pq.2)

/- When the pair family itself varies with the integer being tested, this is the corresponding
   variable-family exceptional set.  Monotonicity of the family lets us dominate it by the fixed
   family at the endpoint `X`; this is the bookkeeping interface needed before a density theorem
   can consume a scale-dependent bad-pair construction. -/
def divisibleBySomeVariablePairUpTo (X : ℕ)
    (pairs : ℕ → Finset (ℕ × ℕ)) : Finset ℕ :=
  (Finset.range X.succ).filter fun n ↦
    ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n

theorem divisibleBySomeVariablePairUpTo_subset_fixed
    (X : ℕ) (pairs : ℕ → Finset (ℕ × ℕ))
    (hmono : ∀ ⦃n m : ℕ⦄, n ≤ m → pairs n ⊆ pairs m) :
    divisibleBySomeVariablePairUpTo X pairs ⊆
      divisibleBySomePairUpTo X (pairs X) := by
  intro n hn
  have hnrange : n ∈ Finset.range X.succ := (Finset.mem_filter.mp hn).1
  have hdata : ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n :=
    (Finset.mem_filter.mp hn).2
  rcases hdata with ⟨pq, hpq, hn0, hdiv⟩
  have hle : n ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hnrange)
  have hpqX : pq ∈ pairs X := hmono hle hpq
  unfold divisibleBySomePairUpTo
  rw [Finset.mem_biUnion]
  refine ⟨pq, hpqX, ?_⟩
  exact Finset.mem_filter.mpr ⟨hnrange, hn0, hdiv⟩

theorem card_divisibleBySomeVariablePairUpTo_le
    (X : ℕ) (pairs : ℕ → Finset (ℕ × ℕ))
    (hmono : ∀ ⦃n m : ℕ⦄, n ≤ m → pairs n ⊆ pairs m) :
    (divisibleBySomeVariablePairUpTo X pairs).card ≤
      (divisibleBySomePairUpTo X (pairs X)).card := by
  exact Finset.card_le_card (divisibleBySomeVariablePairUpTo_subset_fixed X pairs hmono)

/-- The reciprocal weight `∑ 1/(pq)` of a finite family of pairs. -/
noncomputable def pairReciprocalWeight (pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pq ∈ pairs, (((pq.1 * pq.2 : ℕ) : ℝ)⁻¹)

/-- The reciprocal weight of a Cartesian family of pairs factors into the two marginal
reciprocal sums.  This is the algebraic reduction used before summing the bad-pair parameters. -/
theorem pairReciprocalWeight_product (P Q : Finset ℕ) :
    pairReciprocalWeight (P.product Q) =
      (∑ p ∈ P, ((p : ℝ)⁻¹)) * (∑ q ∈ Q, ((q : ℝ)⁻¹)) := by
  classical
  unfold pairReciprocalWeight
  change (∑ pq ∈ P ×ˢ Q, (((pq.1 * pq.2 : ℕ) : ℝ)⁻¹)) = _
  rw [Finset.sum_product]
  simp only [Nat.cast_mul, mul_inv]
  rw [Finset.sum_mul_sum]

/-- Reciprocal pair weights are nonnegative, including pairs containing zero (whose real inverse
is defined as zero). -/
theorem pairReciprocalWeight_nonneg (pairs : Finset (ℕ × ℕ)) :
    0 ≤ pairReciprocalWeight pairs := by
  unfold pairReciprocalWeight
  positivity

/- A finite Chebyshev counting lemma. The later prime-window argument can supply the
   square-sum bound by counting divisibility intersections; this lemma itself is purely finite
   and does not assume independence or a probability measure. -/
theorem card_filter_lt_le_of_sum_sq_le
    {α : Type*} [DecidableEq α] (U : Finset α) (Z : α → ℝ)
    {μ t V : ℝ} (ht : 0 < t)
    (hvar : ∑ x ∈ U, (Z x - μ) ^ 2 ≤ V) :
    (((U.filter (fun x ↦ Z x < μ - t)).card : ℕ) : ℝ) * t ^ 2 ≤ V := by
  let B : Finset α := U.filter (fun x ↦ Z x < μ - t)
  have hpoint : ∀ x ∈ B, t ^ 2 ≤ (Z x - μ) ^ 2 := by
    intro x hx
    have hlt : Z x < μ - t := (Finset.mem_filter.mp hx).2
    have hle : t ≤ μ - Z x := by linarith
    have ht0 : 0 ≤ t := ht.le
    have hdiff0 : 0 ≤ μ - Z x := by linarith
    nlinarith
  calc
    (((B.card : ℕ) : ℝ) * t ^ 2) = ∑ x ∈ B, t ^ 2 := by simp
    _ ≤ ∑ x ∈ B, (Z x - μ) ^ 2 := by
      exact Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
    _ ≤ ∑ x ∈ U, (Z x - μ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro x hxU hxB; positivity)
    _ ≤ V := hvar

theorem card_filter_lt_half_le_of_sum_sq_le
    {α : Type*} [DecidableEq α] (U : Finset α) (Z : α → ℝ)
    {μ V : ℝ} (hμ : 0 < μ)
    (hvar : ∑ x ∈ U, (Z x - μ) ^ 2 ≤ V) :
    (((U.filter (fun x ↦ Z x < μ / 2)).card : ℕ) : ℝ) * μ ^ 2 / 4 ≤ V := by
  have h := card_filter_lt_le_of_sum_sq_le U Z (μ := μ) (t := μ / 2) (V := V)
    (by linarith) hvar
  convert h using 1
  all_goals ring_nf

/- A finite centered-moment inequality.  It isolates the algebra needed to turn a first-moment
   lower bound and a raw second-moment upper bound into the square-sum input for Chebyshev. -/
theorem sum_sq_sub_le_of_sum_le_of_sum_sq_le
    {α : Type*} [DecidableEq α] (U : Finset α) (Z : α → ℝ)
    {μ L M : ℝ} (hμ : 0 ≤ μ)
    (hfirst : L ≤ ∑ x ∈ U, Z x)
    (hsecond : ∑ x ∈ U, (Z x : ℝ) ^ 2 ≤ M) :
    ∑ x ∈ U, (Z x - μ) ^ 2 ≤
      M - 2 * μ * L + (U.card : ℝ) * μ ^ 2 := by
  have hmul : 2 * μ * L ≤ 2 * μ * (∑ x ∈ U, Z x) := by
    gcongr
  calc
    ∑ x ∈ U, (Z x - μ) ^ 2 =
        (∑ x ∈ U, (Z x : ℝ) ^ 2) -
            2 * μ * (∑ x ∈ U, Z x) + (U.card : ℝ) * μ ^ 2 := by
      calc
        ∑ x ∈ U, (Z x - μ) ^ 2 =
            ∑ x ∈ U, (Z x ^ 2 - 2 * μ * Z x + μ ^ 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (∑ x ∈ U, Z x ^ 2) -
              (∑ x ∈ U, 2 * μ * Z x) + (∑ _x ∈ U, μ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (∑ x ∈ U, (Z x : ℝ) ^ 2) -
              2 * μ * (∑ x ∈ U, Z x) + (U.card : ℝ) * μ ^ 2 := by
          rw [← Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ M - 2 * μ * L + (U.card : ℝ) * μ ^ 2 := by
      linarith

/- The number of members of a finite integer family which divide n.  For a prime window this
   is the random variable whose first and second moments are estimated in the density-one step. -/
noncomputable def divisorCount (R : Finset ℕ) (n : ℕ) : ℝ :=
  ((R.filter (fun p ↦ p ∣ n)).card : ℝ)

/- A weighted companion for the divisor count.  The weight is attached to the candidate prime
   itself, so a later prime-power argument can take `w p = p^r` (or a normalized version) before
   doing any asymptotic estimate.  Keeping this as a separate definition avoids pretending that
   the unweighted second moment already controls the prime-power sizes. -/
noncomputable def weightedDivisorCount (R : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ R, if p ∣ n then w p else 0

/- The off-diagonal weighted pair count used in the exact second-moment expansion. -/
noncomputable def weightedDistinctPairDivisorCount
    (R : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ R, ∑ q ∈ R.erase p,
    if p ∣ n ∧ q ∣ n then w p * w q else 0

theorem divisorCount_eq_sum_indicators (R : Finset ℕ) (n : ℕ) :
    divisorCount R n = ∑ p ∈ R, if p ∣ n then (1 : ℝ) else 0 := by
  unfold divisorCount
  exact (Finset.sum_boole (fun p : ℕ ↦ p ∣ n) R).symm

theorem weightedDivisorCount_eq_sum_indicators
    (R : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) :
    weightedDivisorCount R w n = ∑ p ∈ R, if p ∣ n then w p else 0 := by
  rfl

/- The off-diagonal part of the divisor-count square.  Using `R.erase p` makes the
   exclusion of the diagonal explicit, which is convenient when the second moment is
   later expanded into pair-intersection counts. -/
noncomputable def distinctPairDivisorCount (R : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ R, ∑ q ∈ R.erase p, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0

theorem divisorCount_sq_eq_add_distinctPairDivisorCount
    (R : Finset ℕ) (n : ℕ) :
    divisorCount R n ^ 2 = divisorCount R n + distinctPairDivisorCount R n := by
  classical
  let I : ℕ → ℝ := fun p ↦ if p ∣ n then (1 : ℝ) else 0
  have hcount : divisorCount R n = ∑ p ∈ R, I p := by
    exact divisorCount_eq_sum_indicators R n
  have hbool (p : ℕ) : I p * I p = I p := by
    by_cases hp : p ∣ n <;> simp [I, hp]
  rw [hcount, pow_two, Finset.sum_mul_sum]
  unfold distinctPairDivisorCount
  calc
    (∑ x ∈ R, ∑ x_1 ∈ R, I x * I x_1) =
        ∑ p ∈ R, (I p * I p + ∑ q ∈ R.erase p, I p * I q) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hsplit := Finset.sum_erase_add R (fun q ↦ I p * I q) hp
      calc
        (∑ x ∈ R, I p * I x) =
            (∑ x ∈ R.erase p, I p * I x) + I p * I p := hsplit.symm
        _ = I p * I p + ∑ x ∈ R.erase p, I p * I x := by
          rw [add_comm]
    _ = ∑ p ∈ R, (I p + ∑ q ∈ R.erase p,
          if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hbool]
      apply congrArg (fun z ↦ I p + z)
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hpdiv : p ∣ n <;> by_cases hqdiv : q ∣ n <;> simp [I, hpdiv, hqdiv]
    _ = (∑ p ∈ R, I p) +
          ∑ p ∈ R, ∑ q ∈ R.erase p,
            if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_add_distrib]

private theorem card_Icc_filter_dvd_eq_div (X p : ℕ) :
    ((Finset.Icc 1 X).filter (fun n ↦ p ∣ n)).card = X / p := by
  have hset :
      (Finset.Icc 1 X).filter (fun n ↦ p ∣ n) = divisibleUpTo X p := by
    ext n
    simp [divisibleUpTo]
    omega
  rw [hset]
  exact Nat.card_multiples' X p

theorem card_Icc_filter_dvd_pair_eq_div_mul
    (X p q : ℕ) (hcop : Nat.Coprime p q) :
    ((Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ q ∣ n)).card = X / (p * q) := by
  have hset :
      (Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ q ∣ n) =
        divisibleUpTo X (p * q) := by
    ext n
    simp [divisibleUpTo]
    constructor
    · rintro ⟨⟨hn1, hnX⟩, hpn, hqn⟩
      exact ⟨by omega, by omega, hcop.mul_dvd_of_dvd_of_dvd hpn hqn⟩
    · rintro ⟨hnlt, hn0, hpq⟩
      rcases hpq with ⟨k, rfl⟩
      have hn0' : p * q * k ≠ 0 := hn0
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hn0', by omega⟩, ?_, ?_⟩
      · exact ⟨q * k, by simp [Nat.mul_assoc]⟩
      · exact ⟨p * k, by simp [Nat.mul_left_comm, Nat.mul_comm]⟩
  rw [hset]
  exact Nat.card_multiples' X (p * q)

/- Distinct members of a finite prime family are automatically coprime. -/
theorem prime_family_coprime_erase
    (R : Finset ℕ) (hprime : ∀ p ∈ R, p.Prime) :
    ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q := by
  intro p hp q hq
  have hpq : p ≠ q := by
    intro heq
    exact (Finset.mem_erase.mp hq).1 heq.symm
  exact (Nat.coprime_primes (hprime p hp)
    (hprime q (Finset.mem_erase.mp hq).2)).2 hpq

/- Exact first-moment identity on the positive interval.  It uses only finite sums and the
   multiples count; no asymptotic or independence assumption is hidden here. -/
theorem sum_divisorCount_Icc_eq
    (R : Finset ℕ) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n =
      ∑ p ∈ R, ((X / p : ℕ) : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n =
        ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ R, if p ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact divisorCount_eq_sum_indicators R n
    _ = ∑ p ∈ R, ∑ n ∈ Finset.Icc 1 X, if p ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ R, (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_boole (fun n : ℕ ↦ p ∣ n) (Finset.Icc 1 X)
    _ = ∑ p ∈ R, ((X / p : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [card_Icc_filter_dvd_eq_div]

/- Exact weighted first-moment identity.  The floor `X / p` is retained explicitly; this is
   important when the weights are large prime powers, since replacing the floor by `X/p` too early
   would erase the finite error term needed by a later variance estimate. -/
theorem sum_weightedDivisorCount_Icc_eq
    (R : Finset ℕ) (w : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n =
      ∑ p ∈ R, ((X / p : ℕ) : ℝ) * w p := by
  calc
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n =
        ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ R, if p ∣ n then w p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact weightedDivisorCount_eq_sum_indicators R w n
    _ = ∑ p ∈ R, ∑ n ∈ Finset.Icc 1 X, if p ∣ n then w p else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ R, (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n)).card : ℝ) * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        (∑ n ∈ Finset.Icc 1 X, if p ∣ n then w p else 0) =
            ∑ n ∈ Finset.Icc 1 X,
              (if p ∣ n then (1 : ℝ) else 0) * w p := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hpn : p ∣ n <;> simp [hpn]
        _ = (∑ n ∈ Finset.Icc 1 X, if p ∣ n then (1 : ℝ) else 0) * w p := by
          rw [Finset.sum_mul]
        _ = (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n)).card : ℝ) * w p := by
          rw [Finset.sum_boole]
    _ = ∑ p ∈ R, ((X / p : ℕ) : ℝ) * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [card_Icc_filter_dvd_eq_div]

/- The weighted square expands into a diagonal prime-power term and an off-diagonal pair term.
   No positivity assumption on `w` is needed for this exact algebraic identity. -/
theorem weightedDivisorCount_sq_eq_add_weightedDistinctPairDivisorCount
    (R : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) :
    weightedDivisorCount R w n ^ 2 =
      (∑ p ∈ R, if p ∣ n then (w p) ^ 2 else 0) +
        weightedDistinctPairDivisorCount R w n := by
  classical
  let I : ℕ → ℝ := fun p ↦ if p ∣ n then w p else 0
  have hcount : weightedDivisorCount R w n = ∑ p ∈ R, I p := by
    exact weightedDivisorCount_eq_sum_indicators R w n
  have hdiag (p : ℕ) : I p * I p = if p ∣ n then (w p) ^ 2 else 0 := by
    by_cases hp : p ∣ n <;> simp [I, hp, pow_two]
  rw [hcount, pow_two, Finset.sum_mul_sum]
  unfold weightedDistinctPairDivisorCount
  calc
    (∑ x ∈ R, ∑ x_1 ∈ R, I x * I x_1) =
        ∑ p ∈ R, (I p * I p + ∑ q ∈ R.erase p, I p * I q) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hsplit := Finset.sum_erase_add R (fun q ↦ I p * I q) hp
      calc
        (∑ x ∈ R, I p * I x) =
            (∑ x ∈ R.erase p, I p * I x) + I p * I p := hsplit.symm
        _ = I p * I p + ∑ x ∈ R.erase p, I p * I x := by rw [add_comm]
    _ = ∑ p ∈ R,
          ((if p ∣ n then (w p) ^ 2 else 0) +
            ∑ q ∈ R.erase p,
              if p ∣ n ∧ q ∣ n then w p * w q else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      · exact hdiag p
      · apply Finset.sum_congr rfl
        intro q hq
        by_cases hpdiv : p ∣ n <;> by_cases hqdiv : q ∣ n <;>
          simp [I, hpdiv, hqdiv]
    _ = (∑ p ∈ R, if p ∣ n then (w p) ^ 2 else 0) +
          ∑ p ∈ R, ∑ q ∈ R.erase p,
            if p ∣ n ∧ q ∣ n then w p * w q else 0 := by
      rw [Finset.sum_add_distrib]

/- Exact weighted off-diagonal moment on `1 ≤ n ≤ X`.  The only arithmetic hypothesis is the
   coprimality of distinct candidates, which is automatic for a prime family. -/
theorem sum_weightedDistinctPairDivisorCount_Icc_eq
    (R : Finset ℕ) (w : ℕ → ℝ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, weightedDistinctPairDivisorCount R w n =
      ∑ p ∈ R, ∑ q ∈ R.erase p,
        ((X / (p * q) : ℕ) : ℝ) * (w p * w q) := by
  classical
  unfold weightedDistinctPairDivisorCount
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ R, ∑ q ∈ R.erase p,
        if p ∣ n ∧ q ∣ n then w p * w q else 0) =
        (∑ p ∈ R, ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ R.erase p,
          if p ∣ n ∧ q ∣ n then w p * w q else 0) := by
      rw [Finset.sum_comm]
    _ = (∑ p ∈ R, ∑ q ∈ R.erase p, ∑ n ∈ Finset.Icc 1 X,
          if p ∣ n ∧ q ∣ n then w p * w q else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = (∑ p ∈ R, ∑ q ∈ R.erase p,
          (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ q ∣ n)).card : ℝ) *
            (w p * w q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      calc
        (∑ n ∈ Finset.Icc 1 X,
            if p ∣ n ∧ q ∣ n then w p * w q else 0) =
            ∑ n ∈ Finset.Icc 1 X,
              (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) * (w p * w q) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hpdiv : p ∣ n <;> by_cases hqdiv : q ∣ n <;>
            simp [hpdiv, hqdiv]
        _ = (∑ n ∈ Finset.Icc 1 X,
              if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) * (w p * w q) := by
          rw [Finset.sum_mul]
        _ = (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ q ∣ n)).card : ℝ) *
              (w p * w q) := by
          rw [Finset.sum_boole]
    _ = ∑ p ∈ R, ∑ q ∈ R.erase p,
        ((X / (p * q) : ℕ) : ℝ) * (w p * w q) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [card_Icc_filter_dvd_pair_eq_div_mul X p q (hcop p hp q hq)]

/- Exact weighted second moment.  This is the finite kernel for a prime-power-weighted
   Chebyshev argument; later estimates may safely replace the displayed floors by real quotients
   only after supplying nonnegativity of the chosen weights. -/
theorem sum_weightedDivisorCount_sq_Icc_eq
    (R : Finset ℕ) (w : ℕ → ℝ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n ^ 2 =
      (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
        ∑ p ∈ R, ∑ q ∈ R.erase p,
          ((X / (p * q) : ℕ) : ℝ) * (w p * w q) := by
  calc
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n ^ 2 =
        ∑ n ∈ Finset.Icc 1 X,
          ((∑ p ∈ R, if p ∣ n then (w p) ^ 2 else 0) +
            weightedDistinctPairDivisorCount R w n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact weightedDivisorCount_sq_eq_add_weightedDistinctPairDivisorCount R w n
    _ = (∑ n ∈ Finset.Icc 1 X,
          ∑ p ∈ R, if p ∣ n then (w p) ^ 2 else 0) +
        ∑ n ∈ Finset.Icc 1 X, weightedDistinctPairDivisorCount R w n := by
      rw [Finset.sum_add_distrib]
    _ = (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
        ∑ p ∈ R, ∑ q ∈ R.erase p,
          ((X / (p * q) : ℕ) : ℝ) * (w p * w q) := by
      rw [sum_weightedDistinctPairDivisorCount_Icc_eq R w X hcop]
      have hdiag := sum_weightedDivisorCount_Icc_eq R (fun p ↦ (w p) ^ 2) X
      simpa [weightedDivisorCount] using hdiag

/- Upper-bound form of the weighted second moment.  Nonnegative weights permit each floor count
   to be replaced by its real quotient, while the exact diagonal term is left untouched. -/
theorem sum_weightedDivisorCount_sq_Icc_le
    (R : Finset ℕ) (w : ℕ → ℝ) (X : ℕ)
    (hw : ∀ p ∈ R, 0 ≤ w p)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n ^ 2 ≤
      (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
        (X : ℝ) * ∑ p ∈ R, ∑ q ∈ R.erase p,
          (((p * q : ℕ) : ℝ)⁻¹) * (w p * w q) := by
  have hpair :
      (∑ p ∈ R, ∑ q ∈ R.erase p,
          ((X / (p * q) : ℕ) : ℝ) * (w p * w q)) ≤
        ∑ p ∈ R, ∑ q ∈ R.erase p,
          ((X : ℝ) * (((p * q : ℕ) : ℝ)⁻¹)) * (w p * w q) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    have hfloor : ((X / (p * q) : ℕ) : ℝ) ≤
        (X : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
    have hprod : 0 ≤ w p * w q :=
      mul_nonneg (hw p hp) (hw q (Finset.mem_erase.mp hq).2)
    have hmul := mul_le_mul_of_nonneg_right hfloor hprod
    calc
      ((X / (p * q) : ℕ) : ℝ) * (w p * w q) ≤
          ((X : ℝ) / ((p * q : ℕ) : ℝ)) * (w p * w q) := hmul
      _ = ((X : ℝ) * (((p * q : ℕ) : ℝ)⁻¹)) * (w p * w q) := by
        rw [div_eq_mul_inv]
  have hsq := sum_weightedDivisorCount_sq_Icc_eq R w X hcop
  calc
    ∑ n ∈ Finset.Icc 1 X, weightedDivisorCount R w n ^ 2 =
        (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
          ∑ p ∈ R, ∑ q ∈ R.erase p,
            ((X / (p * q) : ℕ) : ℝ) * (w p * w q) := hsq
    _ ≤ (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
          ∑ p ∈ R, ∑ q ∈ R.erase p,
            ((X : ℝ) * (((p * q : ℕ) : ℝ)⁻¹)) * (w p * w q) :=
      add_le_add_right hpair _
    _ = (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
          (X : ℝ) * ∑ p ∈ R, ∑ q ∈ R.erase p,
            (((p * q : ℕ) : ℝ)⁻¹) * (w p * w q) := by
      congr 1
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/- Weighted centered-moment package.  The first-moment term is kept in its exact floor form and
   the second moment uses the nonnegative-weight upper bound above.  This is the direct finite
   Chebyshev input for prime-power weights; any asymptotic choice of `μ` is deliberately left to
   the caller. -/
theorem sum_weightedDivisorCount_centered_sq_Icc_le
    (R : Finset ℕ) (w : ℕ → ℝ) (X : ℕ) {μ : ℝ}
    (hμ : 0 ≤ μ) (hw : ∀ p ∈ R, 0 ≤ w p)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount R w n - μ) ^ 2 ≤
      ((∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
          (X : ℝ) * ∑ p ∈ R, ∑ q ∈ R.erase p,
            (((p * q : ℕ) : ℝ)⁻¹) * (w p * w q)) -
        2 * μ * (∑ p ∈ R, ((X / p : ℕ) : ℝ) * w p) +
        (Finset.Icc 1 X).card * μ ^ 2 := by
  exact sum_sq_sub_le_of_sum_le_of_sum_sq_le
    (Finset.Icc 1 X) (weightedDivisorCount R w)
    (μ := μ)
    (L := ∑ p ∈ R, ((X / p : ℕ) : ℝ) * w p)
    (M := (∑ p ∈ R, ((X / p : ℕ) : ℝ) * (w p) ^ 2) +
      (X : ℝ) * ∑ p ∈ R, ∑ q ∈ R.erase p,
        (((p * q : ℕ) : ℝ)⁻¹) * (w p * w q))
    hμ
    (by rw [sum_weightedDivisorCount_Icc_eq R w X])
    (sum_weightedDivisorCount_sq_Icc_le R w X hw hcop)

/- The complementary floor error is at most one per prime.  This lower estimate is the finite
input needed when the target mean is the reciprocal-prime mass rather than the floored first
moment. -/
theorem sum_divisorCount_Icc_ge_reciprocal_sub_card
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) :
    (X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) - (R.card : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X, divisorCount R n := by
  rw [sum_divisorCount_Icc_eq]
  have hterm : ∀ p ∈ R,
      (X : ℝ) * ((p : ℝ)⁻¹) - 1 ≤ ((X / p : ℕ) : ℝ) := by
    intro p hp
    have hpPrime := hprime p hp
    have hpPos : 0 < p := hpPrime.pos
    have hdiv : X < (X / p + 1) * p := by
      calc
        X = X / p * p + X % p := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod X p).symm
        _ < X / p * p + p := by
          exact Nat.add_lt_add_left (Nat.mod_lt _ hpPos) _
        _ = (X / p + 1) * p := by ring
    have hdivReal : (X : ℝ) < (((X / p + 1 : ℕ) : ℝ) * (p : ℝ)) := by
      exact_mod_cast hdiv
    have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpPos
    have hquot : (X : ℝ) / (p : ℝ) < ((X / p : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hpReal).2
      simpa [Nat.cast_add, mul_add, add_comm, add_left_comm, add_assoc] using hdivReal
    have hquot' : (X : ℝ) / (p : ℝ) - 1 ≤ ((X / p : ℕ) : ℝ) := by
      linarith
    simpa [div_eq_mul_inv] using hquot'
  calc
    (X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) - (R.card : ℝ) =
        ∑ p ∈ R, ((X : ℝ) * ((p : ℝ)⁻¹) - 1) := by
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.mul_sum]
    _ ≤ ∑ p ∈ R, ((X / p : ℕ) : ℝ) := by
      exact Finset.sum_le_sum (fun p hp ↦ hterm p hp)

/- Exact second-moment off-diagonal identity.  The coprimality hypothesis is isolated here;
   the analytic work in the prime-window argument is reduced to supplying it and estimating the
   resulting finite reciprocal pair sum. -/
theorem sum_distinctPairDivisorCount_Icc_eq
    (R : Finset ℕ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, distinctPairDivisorCount R n =
      ∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ) := by
  classical
  unfold distinctPairDivisorCount
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ R, ∑ q ∈ R.erase p,
        if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) =
        (∑ p ∈ R, ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ R.erase p,
          if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = (∑ p ∈ R, ∑ q ∈ R.erase p, ∑ n ∈ Finset.Icc 1 X,
          if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = (∑ p ∈ R, ∑ q ∈ R.erase p,
          (((Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ q ∣ n)).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_boole (fun n : ℕ ↦ p ∣ n ∧ q ∣ n) (Finset.Icc 1 X)
    _ = (∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [card_Icc_filter_dvd_pair_eq_div_mul X p q (hcop p hp q hq)]

/- Combining the diagonal and off-diagonal identities gives an exact finite second-moment
   formula.  This is the point at which the analytic proof only has to estimate two explicit
   reciprocal sums; no probabilistic independence is hidden in the statement. -/
theorem sum_divisorCount_sq_Icc_eq
    (R : Finset ℕ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n ^ 2 =
      (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
        ∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ) := by
  calc
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n ^ 2 =
        ∑ n ∈ Finset.Icc 1 X,
          (divisorCount R n + distinctPairDivisorCount R n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact divisorCount_sq_eq_add_distinctPairDivisorCount R n
    _ = (∑ n ∈ Finset.Icc 1 X, divisorCount R n) +
          ∑ n ∈ Finset.Icc 1 X, distinctPairDivisorCount R n := by
      rw [Finset.sum_add_distrib]
    _ = (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          ∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ) := by
      rw [sum_divisorCount_Icc_eq, sum_distinctPairDivisorCount_Icc_eq R X hcop]

/- The reciprocal weight of the ordered off-diagonal pairs in a finite family. -/
noncomputable def distinctPairReciprocalWeight (R : Finset ℕ) : ℝ :=
  ∑ p ∈ R, ∑ q ∈ R.erase p, (((p * q : ℕ) : ℝ)⁻¹)

/- The ordered off-diagonal reciprocal weight is bounded by the square of the full reciprocal
mass.  Keeping this diagonal contribution is the key cancellation needed for a genuine
Chebyshev variance estimate (an upper bound by the off-diagonal weight alone would be too weak). -/
theorem distinctPairReciprocalWeight_le_reciprocal_sq (R : Finset ℕ) :
    distinctPairReciprocalWeight R ≤ (∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 := by
  unfold distinctPairReciprocalWeight
  calc
    (∑ p ∈ R, ∑ q ∈ R.erase p, (((p * q : ℕ) : ℝ)⁻¹)) ≤
        ∑ p ∈ R, ∑ q ∈ R, (((p * q : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (by intro q hq _; positivity)
    _ = (∑ p ∈ R, ((p : ℝ)⁻¹)) * (∑ q ∈ R, ((q : ℝ)⁻¹)) := by
      simp_rw [Nat.cast_mul, mul_inv]
      rw [Finset.sum_mul_sum]
    _ = (∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 := by ring

theorem sum_distinctPairDivisorCount_Icc_le_reciprocalWeight
    (R : Finset ℕ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, distinctPairDivisorCount R n ≤
      (X : ℝ) * distinctPairReciprocalWeight R := by
  calc
    ∑ n ∈ Finset.Icc 1 X, distinctPairDivisorCount R n =
        ∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ) :=
      sum_distinctPairDivisorCount_Icc_eq R X hcop
    _ ≤ ∑ p ∈ R, ∑ q ∈ R.erase p,
          (X : ℝ) / ((p * q : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact Nat.cast_div_le
    _ = (X : ℝ) * distinctPairReciprocalWeight R := by
      unfold distinctPairReciprocalWeight
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

theorem sum_divisorCount_sq_Icc_le_reciprocalWeight
    (R : Finset ℕ) (X : ℕ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n ^ 2 ≤
      (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
        (X : ℝ) * distinctPairReciprocalWeight R := by
  calc
    ∑ n ∈ Finset.Icc 1 X, divisorCount R n ^ 2 =
        (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          ∑ p ∈ R, ∑ q ∈ R.erase p, ((X / (p * q) : ℕ) : ℝ) :=
      sum_divisorCount_sq_Icc_eq R X hcop
    _ = (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          ∑ n ∈ Finset.Icc 1 X, distinctPairDivisorCount R n := by
      rw [sum_distinctPairDivisorCount_Icc_eq R X hcop]
    _ ≤ (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          (X : ℝ) * distinctPairReciprocalWeight R := by
      exact add_le_add_right
        (sum_distinctPairDivisorCount_Icc_le_reciprocalWeight R X hcop) _

/- Centered-moment form consumed by the two-window Chebyshev lemma.  The first moment is exact,
   while the second moment is bounded by the reciprocal off-diagonal weight above. -/
theorem sum_divisorCount_centered_sq_Icc_le_reciprocalWeight
    (R : Finset ℕ) (X : ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hcop : ∀ p ∈ R, ∀ q ∈ R.erase p, Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
      (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          (X : ℝ) * distinctPairReciprocalWeight R -
        2 * μ * (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
        (Finset.Icc 1 X).card * μ ^ 2 := by
  apply sum_sq_sub_le_of_sum_le_of_sum_sq_le (Finset.Icc 1 X) (divisorCount R)
    (μ := μ) (L := ∑ p ∈ R, ((X / p : ℕ) : ℝ))
    (M := (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
      (X : ℝ) * distinctPairReciprocalWeight R) hμ
  · rw [sum_divisorCount_Icc_eq]
  · exact sum_divisorCount_sq_Icc_le_reciprocalWeight R X hcop

theorem sum_divisorCount_centered_sq_Icc_le_reciprocalWeight_of_prime_family
    (R : Finset ℕ) (X : ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hprime : ∀ p ∈ R, p.Prime) :
    ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
      (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
          (X : ℝ) * distinctPairReciprocalWeight R -
        2 * μ * (∑ p ∈ R, ((X / p : ℕ) : ℝ)) +
        (Finset.Icc 1 X).card * μ ^ 2 := by
  exact sum_divisorCount_centered_sq_Icc_le_reciprocalWeight R X hμ
    (prime_family_coprime_erase R hprime)

/- Combining the exact first moment, its one-unit floor error, and the off-diagonal estimate gives
an explicit centered-moment bound in terms of the reciprocal-prime mean.  This is still finite:
the only inputs are primality and `X > 0`. -/
theorem sum_divisorCount_centered_sq_Icc_le_primeReciprocal_explicit
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hX : 0 < X) :
    ∑ n ∈ Finset.Icc 1 X,
        (divisorCount R n - ∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 ≤
      (X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        (X : ℝ) * distinctPairReciprocalWeight R +
        2 * (∑ p ∈ R, ((p : ℝ)⁻¹)) * (R.card : ℝ) := by
  let μ : ℝ := ∑ p ∈ R, ((p : ℝ)⁻¹)
  let L : ℝ := ∑ p ∈ R, ((X / p : ℕ) : ℝ)
  let P : ℝ := distinctPairReciprocalWeight R
  have hμ : 0 ≤ μ := by
    unfold μ
    apply Finset.sum_nonneg
    intro p hp
    have hpPos : 0 < p := (hprime p hp).pos
    positivity
  have hcenter := sum_divisorCount_centered_sq_Icc_le_reciprocalWeight_of_prime_family
    R X hμ hprime
  have hLupper : L ≤ (X : ℝ) * μ := by
    unfold L μ
    calc
      ∑ p ∈ R, ((X / p : ℕ) : ℝ) ≤
          ∑ p ∈ R, (X : ℝ) / (p : ℝ) := by
        exact Finset.sum_le_sum (fun p hp ↦ Nat.cast_div_le)
      _ = (X : ℝ) * ∑ p ∈ R, ((p : ℝ)⁻¹) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
  have hLlower : (X : ℝ) * μ - (R.card : ℝ) ≤ L := by
    have hfloor := sum_divisorCount_Icc_ge_reciprocal_sub_card R X hprime
    rw [sum_divisorCount_Icc_eq] at hfloor
    simpa [L] using hfloor
  have he_nonneg : 0 ≤ (X : ℝ) * μ - L := sub_nonneg.mpr hLupper
  have he_le_card : (X : ℝ) * μ - L ≤ (R.card : ℝ) := by linarith
  have hcardIcc : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
    rw [Nat.card_Icc]
    rw [Nat.add_sub_cancel]
  have hbase :
      ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
        L + (X : ℝ) * P - 2 * μ * L + (X : ℝ) * μ ^ 2 := by
    simpa [L, P, hcardIcc] using hcenter
  have hidentity :
      L + (X : ℝ) * P - 2 * μ * L + (X : ℝ) * μ ^ 2 =
        (X : ℝ) * μ + (X : ℝ) * P - (X : ℝ) * μ ^ 2 +
          (2 * μ - 1) * ((X : ℝ) * μ - L) := by
    ring
  have hcoef : (2 * μ - 1) * ((X : ℝ) * μ - L) ≤ 2 * μ * (R.card : ℝ) := by
    by_cases hhalf : 2 * μ ≤ 1
    · have hnonpos : 2 * μ - 1 ≤ 0 := by linarith
      have htarget : 0 ≤ 2 * μ * (R.card : ℝ) := by positivity
      simpa [mul_comm] using
        (mul_nonpos_of_nonneg_of_nonpos he_nonneg hnonpos).trans htarget
    · have hcoefpos : 0 ≤ 2 * μ - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left he_le_card hcoefpos
      have hcardnonneg : 0 ≤ (R.card : ℝ) := by positivity
      have hcoefle : 2 * μ - 1 ≤ 2 * μ := by linarith
      exact hmul.trans (mul_le_mul_of_nonneg_right hcoefle hcardnonneg)
  have hμsq : 0 ≤ (X : ℝ) * μ ^ 2 := by positivity
  rw [hidentity] at hbase
  calc
    ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
        (X : ℝ) * μ + (X : ℝ) * P - (X : ℝ) * μ ^ 2 +
          (2 * μ - 1) * ((X : ℝ) * μ - L) := hbase
    _ ≤ (X : ℝ) * μ + (X : ℝ) * P + 2 * μ * (R.card : ℝ) := by
      linarith

/- Sharper finite variance bound.  The preceding explicit estimate retained `X * P` for a
transparent off-diagonal majorant; here `P ≤ μ²` cancels that term, leaving the expected
`O(X μ + μ |R|)` scale needed for an almost-all conclusion when the reciprocal mass grows. -/
theorem sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hX : 0 < X) :
    ∑ n ∈ Finset.Icc 1 X,
        (divisorCount R n - ∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 ≤
      (X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        2 * (∑ p ∈ R, ((p : ℝ)⁻¹)) * (R.card : ℝ) := by
  let μ : ℝ := ∑ p ∈ R, ((p : ℝ)⁻¹)
  let L : ℝ := ∑ p ∈ R, ((X / p : ℕ) : ℝ)
  let P : ℝ := distinctPairReciprocalWeight R
  have hμ : 0 ≤ μ := by
    unfold μ
    apply Finset.sum_nonneg
    intro p hp
    have hpPos : 0 < p := (hprime p hp).pos
    positivity
  have hcenter := sum_divisorCount_centered_sq_Icc_le_reciprocalWeight_of_prime_family
    R X hμ hprime
  have hLupper : L ≤ (X : ℝ) * μ := by
    unfold L μ
    calc
      ∑ p ∈ R, ((X / p : ℕ) : ℝ) ≤
          ∑ p ∈ R, (X : ℝ) / (p : ℝ) := by
        exact Finset.sum_le_sum (fun p hp ↦ Nat.cast_div_le)
      _ = (X : ℝ) * ∑ p ∈ R, ((p : ℝ)⁻¹) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
  have hLlower : (X : ℝ) * μ - (R.card : ℝ) ≤ L := by
    have hfloor := sum_divisorCount_Icc_ge_reciprocal_sub_card R X hprime
    rw [sum_divisorCount_Icc_eq] at hfloor
    simpa [L] using hfloor
  have he_nonneg : 0 ≤ (X : ℝ) * μ - L := sub_nonneg.mpr hLupper
  have he_le_card : (X : ℝ) * μ - L ≤ (R.card : ℝ) := by linarith
  have hcardIcc : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
    rw [Nat.card_Icc]
    rw [Nat.add_sub_cancel]
  have hbase :
      ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
        L + (X : ℝ) * P - 2 * μ * L + (X : ℝ) * μ ^ 2 := by
    simpa [L, P, hcardIcc] using hcenter
  have hidentity :
      L + (X : ℝ) * P - 2 * μ * L + (X : ℝ) * μ ^ 2 =
        (X : ℝ) * μ + (X : ℝ) * P - (X : ℝ) * μ ^ 2 +
          (2 * μ - 1) * ((X : ℝ) * μ - L) := by
    ring
  have hcoef : (2 * μ - 1) * ((X : ℝ) * μ - L) ≤ 2 * μ * (R.card : ℝ) := by
    by_cases hhalf : 2 * μ ≤ 1
    · have hnonpos : 2 * μ - 1 ≤ 0 := by linarith
      have htarget : 0 ≤ 2 * μ * (R.card : ℝ) := by positivity
      simpa [mul_comm] using
        (mul_nonpos_of_nonneg_of_nonpos he_nonneg hnonpos).trans htarget
    · have hcoefpos : 0 ≤ 2 * μ - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left he_le_card hcoefpos
      have hcardnonneg : 0 ≤ (R.card : ℝ) := by positivity
      have hcoefle : 2 * μ - 1 ≤ 2 * μ := by linarith
      exact hmul.trans (mul_le_mul_of_nonneg_right hcoefle hcardnonneg)
  have hP : P ≤ μ ^ 2 := by
    simpa [P, μ] using distinctPairReciprocalWeight_le_reciprocal_sq R
  have hcancel : (X : ℝ) * P - (X : ℝ) * μ ^ 2 ≤ 0 := by
    have hdiff : P - μ ^ 2 ≤ 0 := sub_nonpos.mpr hP
    simpa [mul_sub] using mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
  rw [hidentity] at hbase
  calc
    ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤
        (X : ℝ) * μ + (X : ℝ) * P - (X : ℝ) * μ ^ 2 +
          (2 * μ - 1) * ((X : ℝ) * μ - L) := hbase
    _ ≤ (X : ℝ) * μ + 2 * μ * (R.card : ℝ) := by linarith

/- Named Track-A specialization of the finite Chebyshev step.  Once an analytic argument bounds
   the centered square sum for a prime window, this theorem immediately bounds the exceptional
   integers whose window divisor count is below half its target mean. -/
theorem card_filter_divisorCount_lt_half_le_of_sum_sq_le
    (R : Finset ℕ) (X : ℕ) {μ V : ℝ} (hμ : 0 < μ)
    (hvar : ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤ V) :
    (((((Finset.Icc 1 X).filter (fun n ↦ divisorCount R n < μ / 2)).card : ℕ) : ℝ) * μ ^ 2 / 4) ≤ V := by
  exact card_filter_lt_half_le_of_sum_sq_le (Finset.Icc 1 X) (divisorCount R) hμ hvar

/- The preceding finite estimate in normalized form.  This is the exact interface needed when
the moment calculation is performed on `Icc 1 X` but the conclusion is phrased as a density
ratio. -/
theorem exceptionalRatio_divisorCount_lt_half_le_of_sum_sq_le
    (R : Finset ℕ) (X : ℕ) {μ V : ℝ} (hμ : 0 < μ) (hX : 0 < X)
    (hvar : ∑ n ∈ Finset.Icc 1 X, (divisorCount R n - μ) ^ 2 ≤ V) :
    ((((Finset.Icc 1 X).filter (fun n ↦ divisorCount R n < μ / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤ 4 * V / (μ ^ 2 * (X : ℝ)) := by
  have hcard := card_filter_divisorCount_lt_half_le_of_sum_sq_le R X hμ hvar
  have hμsq : 0 < μ ^ 2 := sq_pos_of_pos hμ
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  apply (div_le_iff₀ hXreal).2
  have hcard' : ((((Finset.Icc 1 X).filter
      (fun n ↦ divisorCount R n < μ / 2)).card : ℕ) : ℝ) ≤ 4 * V / μ ^ 2 := by
    apply (le_div_iff₀ hμsq).2
    nlinarith [hcard]
  calc
    ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount R n < μ / 2)).card : ℕ) : ℝ) ≤ 4 * V / μ ^ 2 := hcard'
    _ = (4 * V / (μ ^ 2 * (X : ℝ))) * (X : ℝ) := by
      field_simp [ne_of_gt hμsq, ne_of_gt hXreal]

/- The preceding explicit moment estimate can be fed directly into the normalized Chebyshev
bound.  This is the finite density formula that the analytic window estimates must eventually
make tend to zero. -/
theorem exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_explicit
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hX : 0 < X)
    (hμ : 0 < ∑ p ∈ R, ((p : ℝ)⁻¹)) :
    ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount R n < (∑ p ∈ R, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      4 * ((X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        (X : ℝ) * distinctPairReciprocalWeight R +
        2 * (∑ p ∈ R, ((p : ℝ)⁻¹)) * (R.card : ℝ)) /
        ((∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 * (X : ℝ)) := by
  exact exceptionalRatio_divisorCount_lt_half_le_of_sum_sq_le R X hμ hX
    (sum_divisorCount_centered_sq_Icc_le_primeReciprocal_explicit R X hprime hX)

/- Sharp normalized form obtained from the cancellation `P ≤ μ²`.  Unlike the earlier transparent
majorant, this bound has no `X * distinctPairReciprocalWeight` term and is strong enough to tend to
zero when the reciprocal mass diverges. -/
theorem exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_sharp
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hX : 0 < X)
    (hμ : 0 < ∑ p ∈ R, ((p : ℝ)⁻¹)) :
    ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount R n < (∑ p ∈ R, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      4 * ((X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        2 * (∑ p ∈ R, ((p : ℝ)⁻¹)) * (R.card : ℝ)) /
        ((∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 * (X : ℝ)) := by
  exact exceptionalRatio_divisorCount_lt_half_le_of_sum_sq_le R X hμ hX
    (sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp R X hprime hX)

/- Algebraic normal form of the sharp finite bound.  This displays exactly the two quantities that
must be controlled in the moving-window argument. -/
theorem exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_sharp_additive
    (R : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hX : 0 < X)
    (hμ : 0 < ∑ p ∈ R, ((p : ℝ)⁻¹)) :
    ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount R n < (∑ p ∈ R, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      4 / (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        8 * (R.card : ℝ) /
          ((∑ p ∈ R, ((p : ℝ)⁻¹)) * (X : ℝ)) := by
  have hbase := exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_sharp
    R X hprime hX hμ
  calc
    ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount R n < (∑ p ∈ R, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      4 * ((X : ℝ) * (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        2 * (∑ p ∈ R, ((p : ℝ)⁻¹)) * (R.card : ℝ)) /
        ((∑ p ∈ R, ((p : ℝ)⁻¹)) ^ 2 * (X : ℝ)) := hbase
    _ = 4 / (∑ p ∈ R, ((p : ℝ)⁻¹)) +
        8 * (R.card : ℝ) /
          ((∑ p ∈ R, ((p : ℝ)⁻¹)) * (X : ℝ)) := by
      field_simp [ne_of_gt hμ, ne_of_gt (show (0 : ℝ) < (X : ℝ) by exact_mod_cast hX)]
      ring

/- A moving-window version of the preceding estimate.  Once a prime-window argument supplies a
positive mean, a centered second-moment majorant, and a vanishing normalized variance, the
exceptional proportion tends to zero.  No monotonicity of the window is assumed here; callers
which need a variable-family exceptional set can combine this with the block-cover lemmas above. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_moment_bounds
    (R : ℕ → Finset ℕ) (μ V : ℕ → ℝ)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < μ X)
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R X) n - μ X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X / (μ X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter (fun n ↦ divisorCount (R X) n < μ X / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hμ, hvar] with X hX hμX hvarX
    exact exceptionalRatio_divisorCount_lt_half_le_of_sum_sq_le
      (R X) X hμX hX hvarX
  · exact hvanish

/- Weighted moving-window counterpart.  The exceptional set is defined by a weighted divisor
   sum, while the proof is the same finite Chebyshev squeeze.  This is the reusable density
   endpoint for the prime-power weights used by Problem 878. -/
theorem tendsto_weightedDivisorCount_exceptionalRatio_zero_of_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (μ V : ℕ → ℝ)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < μ X)
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - μ X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X / (μ X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ weightedDivisorCount (R X) (w X) n < μ X / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hμ, hvar] with X hX hμX hvarX
    have hcard := card_filter_lt_half_le_of_sum_sq_le (Finset.Icc 1 X)
      (weightedDivisorCount (R X) (w X)) hμX hvarX
    have hμsq : 0 < (μ X) ^ 2 := sq_pos_of_pos hμX
    have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
    apply (div_le_iff₀ hXreal).2
    have hcard' :
        (((Finset.Icc 1 X).filter
          (fun n ↦ weightedDivisorCount (R X) (w X) n < μ X / 2)).card : ℝ) ≤
          4 * V X / (μ X) ^ 2 := by
      apply (le_div_iff₀ hμsq).2
      nlinarith [hcard]
    calc
      (((Finset.Icc 1 X).filter
          (fun n ↦ weightedDivisorCount (R X) (w X) n < μ X / 2)).card : ℝ) ≤
          4 * V X / (μ X) ^ 2 := hcard'
      _ = (4 * V X / ((μ X) ^ 2 * (X : ℝ))) * (X : ℝ) := by
        field_simp [ne_of_gt hμsq, ne_of_gt hXreal]
  
  · exact hvanish

/- Direct moving-window corollary: once the selected prime family is known to have positive
reciprocal mass and the explicit finite moment majorant tends to zero after normalization, the
low-divisor exceptional ratio tends to zero.  This packages the exact interface needed by the
normal-order part of Track A; all analytic estimates remain explicit hypotheses. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_explicit
    (R : ℕ → Finset ℕ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R X, ((p : ℝ)⁻¹))
    (hvanish : Tendsto (fun X : ℕ ↦
      4 * ((X : ℝ) * (∑ p ∈ R X, ((p : ℝ)⁻¹)) +
        (X : ℝ) * distinctPairReciprocalWeight (R X) +
        2 * (∑ p ∈ R X, ((p : ℝ)⁻¹)) * (R X).card) /
        ((∑ p ∈ R X, ((p : ℝ)⁻¹)) ^ 2 * (X : ℝ)))
      atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R X) n <
          (∑ p ∈ R X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let μ : ℕ → ℝ := fun X ↦ ∑ p ∈ R X, ((p : ℝ)⁻¹)
  let V : ℕ → ℝ := fun X ↦
    (X : ℝ) * μ X + (X : ℝ) * distinctPairReciprocalWeight (R X) +
      2 * μ X * (R X).card
  have hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R X) n - μ X) ^ 2 ≤ V X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_explicit
      (R X) X (hprime X) hX
  have hμ' : ∀ᶠ X : ℕ in atTop, 0 < μ X := by
    simpa [μ] using hμ
  have hvanish' : Tendsto (fun X : ℕ ↦ 4 * V X / (μ X ^ 2 * (X : ℝ))) atTop (𝓝 0) := by
    simpa [μ, V] using hvanish
  simpa [μ] using
    (tendsto_divisorCount_exceptionalRatio_zero_of_moment_bounds
      R μ V hμ' hvar hvanish')

/- Sharp moving-window corollary.  The cancellation of the full reciprocal square is retained in
the variance majorant, so the only required analytic input is the growth of the reciprocal mass
relative to the window cardinality. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp
    (R : ℕ → Finset ℕ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R X, ((p : ℝ)⁻¹))
    (hvanish : Tendsto (fun X : ℕ ↦
      4 * ((X : ℝ) * (∑ p ∈ R X, ((p : ℝ)⁻¹)) +
        2 * (∑ p ∈ R X, ((p : ℝ)⁻¹)) * (R X).card) /
        ((∑ p ∈ R X, ((p : ℝ)⁻¹)) ^ 2 * (X : ℝ)))
      atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R X) n <
          (∑ p ∈ R X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let μ : ℕ → ℝ := fun X ↦ ∑ p ∈ R X, ((p : ℝ)⁻¹)
  let V : ℕ → ℝ := fun X ↦ (X : ℝ) * μ X + 2 * μ X * (R X).card
  have hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R X) n - μ X) ^ 2 ≤ V X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp
      (R X) X (hprime X) hX
  have hμ' : ∀ᶠ X : ℕ in atTop, 0 < μ X := by simpa [μ] using hμ
  have hvanish' : Tendsto (fun X : ℕ ↦ 4 * V X / (μ X ^ 2 * (X : ℝ)))
      atTop (𝓝 0) := by
    simpa [μ, V] using hvanish
  simpa [μ] using
    (tendsto_divisorCount_exceptionalRatio_zero_of_moment_bounds
      R μ V hμ' hvar hvanish')

theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_limits
    (R : ℕ → Finset ℕ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R X, ((p : ℝ)⁻¹))
    (hinvμ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hcard : Tendsto (fun X : ℕ ↦
      ((R X).card : ℝ) /
        ((∑ p ∈ R X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R X) n <
          (∑ p ∈ R X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hupper : ∀ᶠ X : ℕ in atTop,
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R X) n <
          (∑ p ∈ R X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      4 / (∑ p ∈ R X, ((p : ℝ)⁻¹)) +
        8 * (R X).card /
          ((∑ p ∈ R X, ((p : ℝ)⁻¹)) * (X : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hμ] with X hX hμX
    exact exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_sharp_additive
      (R X) X (hprime X) hX hμX
  have hinvμ' : Tendsto (fun X : ℕ ↦
      4 * (∑ p ∈ R X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
    simpa using hinvμ.const_mul 4
  have hcard' : Tendsto (fun X : ℕ ↦
      8 * (((R X).card : ℝ) /
        ((∑ p ∈ R X, ((p : ℝ)⁻¹)) * (X : ℝ)))) atTop (𝓝 0) := by
    simpa using hcard.const_mul 8
  have hsum : Tendsto (fun X : ℕ ↦
      4 / (∑ p ∈ R X, ((p : ℝ)⁻¹)) +
        8 * (R X).card /
          ((∑ p ∈ R X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0) := by
    convert hinvμ'.add hcard' using 1
    · ext X
      ring
    · norm_num
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · exact hupper
  · exact hsum


/- The preceding finite residual estimate turns divergence of reciprocal mass alone into the
   cardinality condition required by the sharp exceptional-ratio wrapper. -/
/- If the selected family is contained in the initial interval, its cardinality residual is
   automatically bounded by the inverse reciprocal mass.  This removes one of the two scalar
   limits in the common case where `X` is the actual upper endpoint of the prime family. -/
theorem card_div_mass_mul_X_le_inv_mass_of_subset_Icc
    (R : Finset ℕ) (X : ℕ)
    (hsub : R ⊆ Finset.Icc 1 X) (hX : 0 < X)
    {μ : ℝ} (hμ : 0 < μ) :
    (R.card : ℝ) / (μ * (X : ℝ)) ≤ μ⁻¹ := by
  have hcard : R.card ≤ (Finset.Icc 1 X).card := Finset.card_le_card hsub
  have hcardIcc : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
    rw [Nat.card_Icc]
    rw [Nat.add_sub_cancel]
  have hcardReal : (R.card : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show R.card ≤ X by simpa [hcardIcc] using hcard)
  have hden : 0 < μ * (X : ℝ) := mul_pos hμ (by exact_mod_cast hX)
  apply (div_le_iff₀ hden).2
  calc
    (R.card : ℝ) ≤ (X : ℝ) := hcardReal
   _ = μ⁻¹ * (μ * (X : ℝ)) := by
     field_simp [ne_of_gt hμ]
theorem tendsto_card_div_mass_mul_X_zero_of_subset_Icc
    (R : ℕ → Finset ℕ)
    (hsub : ∀ X : ℕ, R X ⊆ Finset.Icc 1 X)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R X, ((p : ℝ)⁻¹))
    (hinvμ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((R X).card : ℝ) /
        ((∑ p ∈ R X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hμ] with X hX hμX
    exact card_div_mass_mul_X_le_inv_mass_of_subset_Icc
      (R X) X (hsub X) hX hμX
  · exact hinvμ

/- Combining the automatic cardinality residual with the sharp finite estimate leaves only the
   divergence of the reciprocal mass as an analytic input. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
    (R : ℕ → Finset ℕ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hsub : ∀ X : ℕ, R X ⊆ Finset.Icc 1 X)
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R X, ((p : ℝ)⁻¹))
    (hinvμ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R X) n <
          (∑ p ∈ R X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  exact tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_limits
    R hprime hμ hinvμ
    (tendsto_card_div_mass_mul_X_zero_of_subset_Icc R hsub hμ hinvμ)

/- The same sharp bridge with an explicit scale sequence.  This is useful when a family is
indexed by blocks but its natural ambient interval is an endpoint sequence `X m` rather than
the block index itself. -/
theorem tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc_scale
    (R : ℕ → Finset ℕ) (X : ℕ → ℕ)
    (hprime : ∀ m : ℕ, ∀ p ∈ R m, p.Prime)
    (hsub : ∀ m : ℕ, R m ⊆ Finset.Icc 1 (X m))
    (hX : Tendsto X atTop atTop)
    (hμ : ∀ᶠ m : ℕ in atTop, 0 < ∑ p ∈ R m, ((p : ℝ)⁻¹))
    (hinvμ : Tendsto (fun m : ℕ ↦
      (∑ p ∈ R m, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0)) :
    Tendsto (fun m : ℕ ↦
      ((((Finset.Icc 1 (X m)).filter
        (fun n ↦ divisorCount (R m) n <
          (∑ p ∈ R m, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X m : ℝ)) atTop (𝓝 0) := by
  have hXpos : ∀ᶠ m : ℕ in atTop, 0 < X m := by
    have h := hX.eventually (eventually_gt_atTop (0 : ℕ))
    filter_upwards [h] with m hm
    exact hm
  have hupper : ∀ᶠ m : ℕ in atTop,
      ((((Finset.Icc 1 (X m)).filter
        (fun n ↦ divisorCount (R m) n <
          (∑ p ∈ R m, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X m : ℝ) ≤
      4 / (∑ p ∈ R m, ((p : ℝ)⁻¹)) +
        8 * (R m).card /
          ((∑ p ∈ R m, ((p : ℝ)⁻¹)) * (X m : ℝ)) := by
    filter_upwards [hXpos, hμ] with m hmX hmμ
    exact exceptionalRatio_divisorCount_lt_half_le_of_primeReciprocal_sharp_additive
      (R m) (X m) (hprime m) hmX hmμ
  have hcard : Tendsto (fun m : ℕ ↦
      ((R m).card : ℝ) /
        ((∑ p ∈ R m, ((p : ℝ)⁻¹)) * (X m : ℝ))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun m ↦ by positivity)
    · filter_upwards [hXpos, hμ] with m hmX hmμ
      exact card_div_mass_mul_X_le_inv_mass_of_subset_Icc
        (R m) (X m) (hsub m) hmX hmμ
    · exact hinvμ
  have hinvμ' : Tendsto (fun m : ℕ ↦
      4 * (∑ p ∈ R m, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
    simpa using hinvμ.const_mul 4
  have hcard' : Tendsto (fun m : ℕ ↦
      8 * (((R m).card : ℝ) /
        ((∑ p ∈ R m, ((p : ℝ)⁻¹)) * (X m : ℝ)))) atTop (𝓝 0) := by
    simpa using hcard.const_mul 8
  have hsum : Tendsto (fun m : ℕ ↦
      4 / (∑ p ∈ R m, ((p : ℝ)⁻¹)) +
        8 * (R m).card /
          ((∑ p ∈ R m, ((p : ℝ)⁻¹)) * (X m : ℝ))) atTop (𝓝 0) := by
    convert hinvμ'.add hcard' using 1
    · ext m
      ring
    · norm_num
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun m ↦ by positivity)
  · exact hupper
  · exact hsum

/- Two-window bookkeeping lemma.  It turns two centered second-moment estimates into one
   explicit bound for the union of the two low-divisor-count exceptional sets. -/
theorem card_union_two_divisorCount_lt_half_le_of_sum_sq_le
    (U R₁ R₂ : Finset ℕ) {μ₁ μ₂ V₁ V₂ : ℝ}
    (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hvar₁ : ∑ n ∈ U, (divisorCount R₁ n - μ₁) ^ 2 ≤ V₁)
    (hvar₂ : ∑ n ∈ U, (divisorCount R₂ n - μ₂) ^ 2 ≤ V₂) :
    (((U.filter (fun n ↦ divisorCount R₁ n < μ₁ / 2)) ∪
        (U.filter (fun n ↦ divisorCount R₂ n < μ₂ / 2))).card : ℝ) ≤
      4 * V₁ / μ₁ ^ 2 + 4 * V₂ / μ₂ ^ 2 := by
  classical
  let E₁ : Finset ℕ := U.filter (fun n ↦ divisorCount R₁ n < μ₁ / 2)
  let E₂ : Finset ℕ := U.filter (fun n ↦ divisorCount R₂ n < μ₂ / 2)
  have h₁ := card_filter_lt_half_le_of_sum_sq_le U (divisorCount R₁) hμ₁ hvar₁
  have h₂ := card_filter_lt_half_le_of_sum_sq_le U (divisorCount R₂) hμ₂ hvar₂
  have hμ₁sq : 0 < μ₁ ^ 2 := sq_pos_of_pos hμ₁
  have hμ₂sq : 0 < μ₂ ^ 2 := sq_pos_of_pos hμ₂
  have hc₁ : (E₁.card : ℝ) ≤ 4 * V₁ / μ₁ ^ 2 := by
    apply (le_div_iff₀ hμ₁sq).2
    nlinarith [h₁]
  have hc₂ : (E₂.card : ℝ) ≤ 4 * V₂ / μ₂ ^ 2 := by
    apply (le_div_iff₀ hμ₂sq).2
    nlinarith [h₂]
  have hcard : ((E₁ ∪ E₂).card : ℝ) ≤ (E₁.card : ℝ) + (E₂.card : ℝ) := by
    exact_mod_cast Finset.card_union_le E₁ E₂
  calc
    ((E₁ ∪ E₂).card : ℝ) ≤ (E₁.card : ℝ) + (E₂.card : ℝ) := hcard
    _ ≤ 4 * V₁ / μ₁ ^ 2 + 4 * V₂ / μ₂ ^ 2 := add_le_add hc₁ hc₂

/- Normalized two-window form.  The union is still taken inside an arbitrary finite universe
`U`; specializing `U = Icc 1 X` yields the density estimate used by the first question. -/
theorem exceptionalRatio_union_two_divisorCount_lt_half_le_of_sum_sq_le
    (U : Finset ℕ) (X : ℕ) (R₁ R₂ : Finset ℕ)
    {μ₁ μ₂ V₁ V₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hX : 0 < X)
    (hvar₁ : ∑ n ∈ U, (divisorCount R₁ n - μ₁) ^ 2 ≤ V₁)
    (hvar₂ : ∑ n ∈ U, (divisorCount R₂ n - μ₂) ^ 2 ≤ V₂) :
    ((((U.filter (fun n ↦ divisorCount R₁ n < μ₁ / 2)) ∪
        (U.filter (fun n ↦ divisorCount R₂ n < μ₂ / 2))).card : ℕ) : ℝ) /
      (X : ℝ) ≤
      (4 * V₁ / μ₁ ^ 2 + 4 * V₂ / μ₂ ^ 2) / (X : ℝ) := by
  have hcard := card_union_two_divisorCount_lt_half_le_of_sum_sq_le
    U R₁ R₂ hμ₁ hμ₂ hvar₁ hvar₂
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  apply (div_le_iff₀ hXreal).2
  calc
    ((((U.filter (fun n ↦ divisorCount R₁ n < μ₁ / 2)) ∪
        (U.filter (fun n ↦ divisorCount R₂ n < μ₂ / 2))).card : ℕ) : ℝ) ≤
        4 * V₁ / μ₁ ^ 2 + 4 * V₂ / μ₂ ^ 2 := hcard
    _ = ((4 * V₁ / μ₁ ^ 2 + 4 * V₂ / μ₂ ^ 2) / (X : ℝ)) * (X : ℝ) := by
      field_simp [ne_of_gt hXreal]

/- Moving two-window version.  This is the density bookkeeping endpoint for the normal-order
construction: both window means must stay positive, while the sum of their normalized variance
bounds must vanish. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_moment_bounds
    (R₁ R₂ : ℕ → Finset ℕ) (μ₁ μ₂ V₁ V₂ : ℕ → ℝ)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < μ₁ X)
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < μ₂ X)
    (hvar₁ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₁ X) n - μ₁ X) ^ 2 ≤ V₁ X)
    (hvar₂ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₂ X) n - μ₂ X) ^ 2 ≤ V₂ X)
    (hvanish : Tendsto (fun X : ℕ ↦
      (4 * V₁ X / (μ₁ X) ^ 2 + 4 * V₂ X / (μ₂ X) ^ 2) / (X : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((((Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₁ X) n < μ₁ X / 2)) ∪
        (Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₂ X) n < μ₂ X / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hμ₁, hμ₂, hvar₁, hvar₂]
      with X hX hμ₁X hμ₂X hvar₁X hvar₂X
    exact exceptionalRatio_union_two_divisorCount_lt_half_le_of_sum_sq_le
      (Finset.Icc 1 X) X (R₁ X) (R₂ X) hμ₁X hμ₂X hX hvar₁X hvar₂X
  · exact hvanish

/- Explicit two-window corollary used by the complementary-window construction.  It supplies the
same endpoint as the generic theorem above, but computes both variance majorants from the actual
reciprocal prime masses and off-diagonal weights. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_explicit
    (R₁ R₂ : ℕ → Finset ℕ)
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hvanish : Tendsto (fun X : ℕ ↦
      (4 * ((X : ℝ) * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) +
          (X : ℝ) * distinctPairReciprocalWeight (R₁ X) +
          2 * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (R₁ X).card) /
          (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) ^ 2 +
        4 * ((X : ℝ) * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) +
          (X : ℝ) * distinctPairReciprocalWeight (R₂ X) +
          2 * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (R₂ X).card) /
          (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) ^ 2) /
        (X : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((((Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₁ X) n <
            (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
        (Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₂ X) n <
            (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let μ₁ : ℕ → ℝ := fun X ↦ ∑ p ∈ R₁ X, ((p : ℝ)⁻¹)
  let μ₂ : ℕ → ℝ := fun X ↦ ∑ p ∈ R₂ X, ((p : ℝ)⁻¹)
  let V₁ : ℕ → ℝ := fun X ↦
    (X : ℝ) * μ₁ X + (X : ℝ) * distinctPairReciprocalWeight (R₁ X) +
      2 * μ₁ X * (R₁ X).card
  let V₂ : ℕ → ℝ := fun X ↦
    (X : ℝ) * μ₂ X + (X : ℝ) * distinctPairReciprocalWeight (R₂ X) +
      2 * μ₂ X * (R₂ X).card
  have hvar₁ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₁ X) n - μ₁ X) ^ 2 ≤ V₁ X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_explicit
      (R₁ X) X (hprime₁ X) hX
  have hvar₂ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₂ X) n - μ₂ X) ^ 2 ≤ V₂ X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_explicit
      (R₂ X) X (hprime₂ X) hX
  have hμ₁' : ∀ᶠ X : ℕ in atTop, 0 < μ₁ X := by simpa [μ₁] using hμ₁
  have hμ₂' : ∀ᶠ X : ℕ in atTop, 0 < μ₂ X := by simpa [μ₂] using hμ₂
  have hvanish' : Tendsto (fun X : ℕ ↦
      (4 * V₁ X / (μ₁ X) ^ 2 + 4 * V₂ X / (μ₂ X) ^ 2) /
        (X : ℝ)) atTop (𝓝 0) := by
    simpa [μ₁, μ₂, V₁, V₂] using hvanish
  simpa [μ₁, μ₂] using
    (tendsto_divisorCount_union_two_exceptionalRatio_zero_of_moment_bounds
      R₁ R₂ μ₁ μ₂ V₁ V₂ hμ₁' hμ₂' hvar₁ hvar₂ hvanish')

/- Sharp complementary-window corollary.  This is the Track-A density interface after retaining
the diagonal cancellation in both finite variance estimates. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp
    (R₁ R₂ : ℕ → Finset ℕ)
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hvanish : Tendsto (fun X : ℕ ↦
      (4 * ((X : ℝ) * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) +
          2 * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (R₁ X).card) /
          (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) ^ 2 +
        4 * ((X : ℝ) * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) +
          2 * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (R₂ X).card) /
          (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) ^ 2) /
        (X : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((((Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₁ X) n <
            (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
        (Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₂ X) n <
            (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let μ₁ : ℕ → ℝ := fun X ↦ ∑ p ∈ R₁ X, ((p : ℝ)⁻¹)
  let μ₂ : ℕ → ℝ := fun X ↦ ∑ p ∈ R₂ X, ((p : ℝ)⁻¹)
  let V₁ : ℕ → ℝ := fun X ↦ (X : ℝ) * μ₁ X + 2 * μ₁ X * (R₁ X).card
  let V₂ : ℕ → ℝ := fun X ↦ (X : ℝ) * μ₂ X + 2 * μ₂ X * (R₂ X).card
  have hvar₁ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₁ X) n - μ₁ X) ^ 2 ≤ V₁ X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp
      (R₁ X) X (hprime₁ X) hX
  have hvar₂ : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X, (divisorCount (R₂ X) n - μ₂ X) ^ 2 ≤ V₂ X := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp
      (R₂ X) X (hprime₂ X) hX
  have hμ₁' : ∀ᶠ X : ℕ in atTop, 0 < μ₁ X := by simpa [μ₁] using hμ₁
  have hμ₂' : ∀ᶠ X : ℕ in atTop, 0 < μ₂ X := by simpa [μ₂] using hμ₂
  have hvanish' : Tendsto (fun X : ℕ ↦
      (4 * V₁ X / (μ₁ X) ^ 2 + 4 * V₂ X / (μ₂ X) ^ 2) /
        (X : ℝ)) atTop (𝓝 0) := by
    simpa [μ₁, μ₂, V₁, V₂] using hvanish
  simpa [μ₁, μ₂] using
    (tendsto_divisorCount_union_two_exceptionalRatio_zero_of_moment_bounds
      R₁ R₂ μ₁ μ₂ V₁ V₂ hμ₁' hμ₂' hvar₁ hvar₂ hvanish')

/- Minimal scalar-input form for the complementary windows.  It makes the analytic obligations
explicit as four limits: each reciprocal mass diverges, and each cardinality divided by `μ X`
vanishes. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_limits
    (R₁ R₂ : ℕ → Finset ℕ)
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hinvμ₁ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₁ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hinvμ₂ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₂ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hcard₁ : Tendsto (fun X : ℕ ↦
      ((R₁ X).card : ℝ) /
        ((∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0))
    (hcard₂ : Tendsto (fun X : ℕ ↦
      ((R₂ X).card : ℝ) /
        ((∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((((Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₁ X) n <
            (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
        (Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₂ X) n <
            (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun X : ℕ ↦
      4 / (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) +
        8 * (R₁ X).card /
          ((∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0) := by
    have h₁a : Tendsto (fun X : ℕ ↦
        4 * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
      simpa using hinvμ₁.const_mul 4
    have h₁b : Tendsto (fun X : ℕ ↦
        8 * (((R₁ X).card : ℝ) /
          ((∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (X : ℝ)))) atTop (𝓝 0) := by
      simpa using hcard₁.const_mul 8
    convert h₁a.add h₁b using 1
    · ext X
      ring
    · norm_num
  have h₂ : Tendsto (fun X : ℕ ↦
      4 / (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) +
        8 * (R₂ X).card /
          ((∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (X : ℝ))) atTop (𝓝 0) := by
    have h₂a : Tendsto (fun X : ℕ ↦
        4 * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
      simpa using hinvμ₂.const_mul 4
    have h₂b : Tendsto (fun X : ℕ ↦
        8 * (((R₂ X).card : ℝ) /
          ((∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (X : ℝ)))) atTop (𝓝 0) := by
      simpa using hcard₂.const_mul 8
    convert h₂a.add h₂b using 1
    · ext X
      ring
    · norm_num
  have hsum : Tendsto (fun X : ℕ ↦
      4 / (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) +
          8 * (R₁ X).card /
            ((∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (X : ℝ)) +
        (4 / (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) +
          8 * (R₂ X).card /
            ((∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (X : ℝ)))) atTop (𝓝 0) := by
    simpa [add_assoc] using h₁.add h₂
  have hvanish : Tendsto (fun X : ℕ ↦
      (4 * ((X : ℝ) * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) +
          2 * (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) * (R₁ X).card) /
          (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) ^ 2 +
        4 * ((X : ℝ) * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) +
          2 * (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) * (R₂ X).card) /
          (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) ^ 2) /
        (X : ℝ)) atTop (𝓝 0) := by
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), hμ₁, hμ₂]
      with X hX hμ₁X hμ₂X
    field_simp [ne_of_gt hμ₁X, ne_of_gt hμ₂X,
      ne_of_gt (show (0 : ℝ) < (X : ℝ) by exact_mod_cast hX)]
    ring
  exact tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp
    R₁ R₂ hprime₁ hprime₂ hμ₁ hμ₂ hvanish

/- If both complementary families lie in the initial interval, their two cardinality residuals
   are absorbed by the corresponding inverse reciprocal masses.  Thus the two-window endpoint
   also needs only the two reciprocal-mass divergences. -/
theorem tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
    (R₁ R₂ : ℕ → Finset ℕ)
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hsub₁ : ∀ X : ℕ, R₁ X ⊆ Finset.Icc 1 X)
    (hsub₂ : ∀ X : ℕ, R₂ X ⊆ Finset.Icc 1 X)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hinvμ₁ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₁ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hinvμ₂ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₂ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((((Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₁ X) n <
            (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
        (Finset.Icc 1 X).filter
          (fun n ↦ divisorCount (R₂ X) n <
            (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  exact tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_limits
    R₁ R₂ hprime₁ hprime₂ hμ₁ hμ₂ hinvμ₁ hinvμ₂
    (tendsto_card_div_mass_mul_X_zero_of_subset_Icc R₁ hsub₁ hμ₁ hinvμ₁)
    (tendsto_card_div_mass_mul_X_zero_of_subset_Icc R₂ hsub₂ hμ₂ hinvμ₂)
/-- The reciprocal weight of a union is at most the sum of the two weights.  This does not
require disjointness; an element in the intersection is counted only once on the left and at
least once on the right. -/
theorem pairReciprocalWeight_union_le
    (A B : Finset (ℕ × ℕ)) :
    pairReciprocalWeight (A ∪ B) ≤
      pairReciprocalWeight A + pairReciprocalWeight B := by
  classical
  have hunion : A ∪ B = A ∪ (B \ A) := by
    ext pq
    by_cases hA : pq ∈ A <;> simp [hA]
  calc
    pairReciprocalWeight (A ∪ B) = pairReciprocalWeight (A ∪ (B \ A)) := by
      rw [hunion]
    _ = pairReciprocalWeight A + pairReciprocalWeight (B \ A) := by
      unfold pairReciprocalWeight
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ pairReciprocalWeight A + pairReciprocalWeight B := by
      gcongr
      unfold pairReciprocalWeight
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (by intro pq hpq _; positivity)

/-- A finite union of pair families has weight at most the sum of the individual weights. -/
theorem pairReciprocalWeight_biUnion_le
    {ι : Type*} (I : Finset ι) (families : ι → Finset (ℕ × ℕ)) :
    pairReciprocalWeight (I.biUnion families) ≤
      ∑ i ∈ I, pairReciprocalWeight (families i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [pairReciprocalWeight]
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (pairReciprocalWeight_union_le _ _).trans
        (add_le_add_right ih (pairReciprocalWeight (families i)))

/-- Monotonicity of reciprocal weight under inclusion. -/
theorem pairReciprocalWeight_mono {A B : Finset (ℕ × ℕ)} (hAB : A ⊆ B) :
    pairReciprocalWeight A ≤ pairReciprocalWeight B := by
  unfold pairReciprocalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB
    (by intro pq hpq _; positivity)

/- Filtering a finite pair family can only decrease its reciprocal weight.  This is the basic
monotonicity step used when a bad-pair relation is split into rational-approximation blocks. -/
theorem pairReciprocalWeight_filter_le
    (pairs : Finset (ℕ × ℕ)) (bad : (ℕ × ℕ) → Prop) [DecidablePred bad] :
    pairReciprocalWeight (pairs.filter bad) ≤ pairReciprocalWeight pairs := by
  unfold pairReciprocalWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) 
  intro a _ _
  positivity

/-- A reusable squeeze interface for the analytic parameter sum: any pointwise nonnegative upper
bound tending to zero forces the reciprocal bad-pair weight itself to tend to zero. -/
theorem tendsto_pairReciprocalWeight_zero_of_le
    (pairs : ℕ → Finset (ℕ × ℕ)) (bound : ℕ → ℝ)
    (hupper : ∀ X, pairReciprocalWeight (pairs X) ≤ bound X)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto (fun X ↦ pairReciprocalWeight (pairs X)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ pairReciprocalWeight_nonneg (pairs X))
  · exact Filter.Eventually.of_forall hupper
  · exact hbound

/-- Natural-number form of the union bound. -/
theorem card_divisibleBySomePairUpTo_le (X : ℕ) (pairs : Finset (ℕ × ℕ)) :
    (divisibleBySomePairUpTo X pairs).card ≤
      ∑ pq ∈ pairs, X / (pq.1 * pq.2) := by
  unfold divisibleBySomePairUpTo
  calc
    (pairs.biUnion fun pq ↦ divisibleUpTo X (pq.1 * pq.2)).card ≤
        ∑ pq ∈ pairs, (divisibleUpTo X (pq.1 * pq.2)).card :=
      Finset.card_biUnion_le
    _ = ∑ pq ∈ pairs, X / (pq.1 * pq.2) := by
      apply Finset.sum_congr rfl
      intro pq hpq
      exact Nat.card_multiples' X (pq.1 * pq.2)

/-- Real-valued reciprocal-weight form of the union bound. In particular, if the reciprocal
weight of the bad pairs is `o(1)`, their divisibility-exceptional set is `o(X)`. -/
theorem card_divisibleBySomePairUpTo_le_reciprocalWeight
    (X : ℕ) (pairs : Finset (ℕ × ℕ)) :
    ((divisibleBySomePairUpTo X pairs).card : ℝ) ≤
      (X : ℝ) * pairReciprocalWeight pairs := by
  calc
    ((divisibleBySomePairUpTo X pairs).card : ℝ) ≤
        ((∑ pq ∈ pairs, X / (pq.1 * pq.2) : ℕ) : ℝ) := by
      exact_mod_cast card_divisibleBySomePairUpTo_le X pairs
    _ = ∑ pq ∈ pairs, ((X / (pq.1 * pq.2) : ℕ) : ℝ) := by
      norm_cast
    _ ≤ ∑ pq ∈ pairs, (X : ℝ) / ((pq.1 * pq.2 : ℕ) : ℝ) := by
      gcongr with pq hpq
      exact Nat.cast_div_le
    _ = (X : ℝ) * pairReciprocalWeight pairs := by
      unfold pairReciprocalWeight
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]

/-- After normalization by `X`, the exceptional proportion is at most the reciprocal weight. -/
theorem exceptionalRatio_le_pairReciprocalWeight
    {X : ℕ} (hX : 0 < X) (pairs : Finset (ℕ × ℕ)) :
    ((divisibleBySomePairUpTo X pairs).card : ℝ) / (X : ℝ) ≤
      pairReciprocalWeight pairs := by
  calc
    ((divisibleBySomePairUpTo X pairs).card : ℝ) / (X : ℝ) ≤
        ((X : ℝ) * pairReciprocalWeight pairs) / (X : ℝ) := by
      exact div_le_div_of_nonneg_right
        (card_divisibleBySomePairUpTo_le_reciprocalWeight X pairs) (by positivity)
    _ = pairReciprocalWeight pairs := by
      field_simp

/-- Asymptotic form of the union-bound step: reciprocal weight tending to zero forces the
normalized exceptional count to tend to zero. -/
theorem tendsto_exceptionalRatio_zero_of_reciprocalWeight
    (pairs : ℕ → Finset (ℕ × ℕ))
    (hweight : Tendsto (fun X ↦ pairReciprocalWeight (pairs X)) atTop (𝓝 0)) :
    Tendsto (fun X ↦
      ((divisibleBySomePairUpTo X (pairs X)).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun X ↦ by positivity
  · filter_upwards [eventually_gt_atTop 0] with X hX
    exact exceptionalRatio_le_pairReciprocalWeight hX (pairs X)
  · exact hweight

/- The variable-family version of the asymptotic union bound.  It is intentionally conditional on
   monotonicity: without a relation between `pairs n` and the endpoint family `pairs X`, a
   per-scale reciprocal-weight limit does not by itself control one fixed exceptional set. -/
theorem tendsto_variableExceptionalRatio_zero_of_reciprocalWeight
    (pairs : ℕ → Finset (ℕ × ℕ))
    (hmono : ∀ ⦃n m : ℕ⦄, n ≤ m → pairs n ⊆ pairs m)
    (hweight : Tendsto (fun X ↦ pairReciprocalWeight (pairs X)) atTop (𝓝 0)) :
    Tendsto (fun X ↦
      ((divisibleBySomeVariablePairUpTo X pairs).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun X ↦ by positivity
  · filter_upwards [eventually_gt_atTop 0] with X hX
    calc
      ((divisibleBySomeVariablePairUpTo X pairs).card : ℝ) / (X : ℝ) ≤
          ((divisibleBySomePairUpTo X (pairs X)).card : ℝ) / (X : ℝ) := by
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast card_divisibleBySomeVariablePairUpTo_le X pairs hmono)
          (by positivity)
      _ ≤ pairReciprocalWeight (pairs X) :=
        exceptionalRatio_le_pairReciprocalWeight hX (pairs X)
  · exact hweight

/- A block-cover variant for genuinely moving families.  The covering family at the endpoint
   need not be one of the original `pairs n`, and no monotonicity of `pairs` is assumed.  This is
   the form needed when report windows are grouped into geometric or dyadic blocks before the
   reciprocal-weight estimate is applied. -/
theorem divisibleBySomeVariablePairUpTo_subset_block
    (X : ℕ) (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃n⦄, n ≤ X → pairs n ⊆ block X) :
    divisibleBySomeVariablePairUpTo X pairs ⊆
      divisibleBySomePairUpTo X (block X) := by
  intro n hn
  have hnrange : n ∈ Finset.range X.succ := (Finset.mem_filter.mp hn).1
  have hdata : ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n :=
    (Finset.mem_filter.mp hn).2
  rcases hdata with ⟨pq, hpq, hn0, hdiv⟩
  have hle : n ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hnrange)
  have hpqX : pq ∈ block X := hcover hle hpq
  unfold divisibleBySomePairUpTo
  rw [Finset.mem_biUnion]
  refine ⟨pq, hpqX, ?_⟩
  exact Finset.mem_filter.mpr ⟨hnrange, hn0, hdiv⟩

theorem card_divisibleBySomeVariablePairUpTo_le_of_block
    (X : ℕ) (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃n⦄, n ≤ X → pairs n ⊆ block X) :
    (divisibleBySomeVariablePairUpTo X pairs).card ≤
      (divisibleBySomePairUpTo X (block X)).card := by
  exact Finset.card_le_card
    (divisibleBySomeVariablePairUpTo_subset_block X pairs block hcover)

theorem tendsto_variableExceptionalRatio_zero_of_blockWeight
    (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃X n : ℕ⦄, n ≤ X → pairs n ⊆ block X)
    (hweight : Tendsto (fun X ↦ pairReciprocalWeight (block X)) atTop (𝓝 0)) :
    Tendsto (fun X ↦
      ((divisibleBySomeVariablePairUpTo X pairs).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun X ↦ by positivity
  · filter_upwards [eventually_gt_atTop 0] with X hX
    calc
      ((divisibleBySomeVariablePairUpTo X pairs).card : ℝ) / (X : ℝ) ≤
          ((divisibleBySomePairUpTo X (block X)).card : ℝ) / (X : ℝ) := by
        have hcard := card_divisibleBySomeVariablePairUpTo_le_of_block
          X pairs block (fun {_n} hle ↦ hcover (X := X) hle)
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast hcard)
          (by positivity)
      _ ≤ pairReciprocalWeight (block X) :=
        exceptionalRatio_le_pairReciprocalWeight hX (block X)
  · exact hweight

/- A block cover may only be available after an initial range of indices.  The initial range is
   harmless for density: its cardinality is at most `K`, while the block controls all `n` with
   `K ≤ n ≤ X`. -/
theorem divisibleBySomeVariablePairUpTo_subset_initial_union_block
    (X K : ℕ) (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃n⦄, K ≤ n → n ≤ X → pairs n ⊆ block X) :
    divisibleBySomeVariablePairUpTo X pairs ⊆
      Finset.range K ∪ divisibleBySomePairUpTo X (block X) := by
  intro n hn
  have hnrange : n ∈ Finset.range X.succ := (Finset.mem_filter.mp hn).1
  have hdata : ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n :=
    (Finset.mem_filter.mp hn).2
  rcases lt_or_ge n K with hsmall | hlarge
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hsmall))
  · rcases hdata with ⟨pq, hpq, hn0, hdiv⟩
    have hle : n ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hnrange)
    have hpqX : pq ∈ block X := hcover hlarge hle hpq
    apply Finset.mem_union.mpr
    right
    unfold divisibleBySomePairUpTo
    rw [Finset.mem_biUnion]
    refine ⟨pq, hpqX, ?_⟩
    exact Finset.mem_filter.mpr ⟨hnrange, hn0, hdiv⟩

theorem card_divisibleBySomeVariablePairUpTo_le_of_initial_block
    (X K : ℕ) (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃n⦄, K ≤ n → n ≤ X → pairs n ⊆ block X) :
    (divisibleBySomeVariablePairUpTo X pairs).card ≤
      K + (divisibleBySomePairUpTo X (block X)).card := by
  apply le_trans (Finset.card_le_card
    (divisibleBySomeVariablePairUpTo_subset_initial_union_block X K pairs block hcover))
  calc
    (Finset.range K ∪ divisibleBySomePairUpTo X (block X)).card ≤
        (Finset.range K).card + (divisibleBySomePairUpTo X (block X)).card :=
      Finset.card_union_le _ _
    _ = K + (divisibleBySomePairUpTo X (block X)).card := by
      rw [Finset.card_range]

theorem tendsto_variableExceptionalRatio_zero_of_initial_blockWeight
    (pairs block : ℕ → Finset (ℕ × ℕ)) (K : ℕ → ℕ)
    (hcover : ∀ ⦃X n : ℕ⦄, K X ≤ n → n ≤ X → pairs n ⊆ block X)
    (hK : Tendsto (fun X ↦ (K X : ℝ) / (X : ℝ)) atTop (𝓝 0))
    (hweight : Tendsto (fun X ↦ pairReciprocalWeight (block X)) atTop (𝓝 0)) :
    Tendsto (fun X ↦
      ((divisibleBySomeVariablePairUpTo X (fun n ↦ pairs n)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun X ↦ (K X : ℝ) / (X : ℝ) +
      pairReciprocalWeight (block X)) atTop (𝓝 0) := by
    simpa using hK.add hweight
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun X ↦ by positivity
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hcard := card_divisibleBySomeVariablePairUpTo_le_of_initial_block
      X (K X) pairs block (fun {_n} hkn hle ↦ hcover hkn hle)
    have hcardR :
        ((divisibleBySomeVariablePairUpTo X (fun n ↦ pairs n)).card : ℝ) ≤
          (K X : ℝ) + (divisibleBySomePairUpTo X (block X)).card := by
      exact_mod_cast hcard
    calc
      ((divisibleBySomeVariablePairUpTo X (fun n ↦ pairs n)).card : ℝ) / (X : ℝ) ≤
          ((K X : ℝ) + (divisibleBySomePairUpTo X (block X)).card) / (X : ℝ) :=
        div_le_div_of_nonneg_right hcardR (by positivity)
      _ = (K X : ℝ) / (X : ℝ) +
          ((divisibleBySomePairUpTo X (block X)).card : ℝ) / (X : ℝ) := by
        ring
      _ ≤ (K X : ℝ) / (X : ℝ) + pairReciprocalWeight (block X) := by
        gcongr
        exact exceptionalRatio_le_pairReciprocalWeight hX (block X)
  · exact hsum

end Erdos878

namespace Erdos878

/- General order-theoretic bridge for the remaining prime-mass input.  The lower scale may be any
   real-valued quantity tending to infinity (for example, a harmonic or logarithmic block sum). -/
theorem tendsto_inv_zero_of_eventually_ge_mul_real
    (mass lower : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c)
    (hlower_atTop : Tendsto lower atTop atTop)
    (hlower : ∀ᶠ X : ℕ in atTop, c * lower X ≤ mass X) :
    Tendsto (fun X : ℕ ↦ (mass X)⁻¹) atTop (𝓝 0) := by
  have hcm : Tendsto (fun X : ℕ ↦ c * lower X) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hb := hlower_atTop.eventually (eventually_ge_atTop (b / c))
    filter_upwards [hb] with X hX
    simpa [mul_comm] using (div_le_iff₀ hc).mp hX
  have hmass : Tendsto mass atTop atTop :=
    Filter.tendsto_atTop_mono' atTop hlower hcm
  exact hmass.inv_tendsto_atTop

/- An eventual termwise lower bound is enough to transfer divergence of nonnegative partial sums.
   The finite initial segment is absorbed as a constant shift. -/
theorem tendsto_sum_atTop_of_eventually_ge_nonneg
    (u v : ℕ → ℝ)
    (hu : ∀ i : ℕ, 0 ≤ u i)
    (hlimv : Tendsto (fun m : ℕ ↦ ∑ i ∈ Finset.range m, v i) atTop atTop)
    (hbound : ∀ᶠ i : ℕ in atTop, v i ≤ u i) :
    Tendsto (fun m : ℕ ↦ ∑ i ∈ Finset.range m, u i) atTop atTop := by
  rcases (eventually_atTop.1 hbound) with ⟨N, hN⟩
  let c₀ : ℝ := ∑ i ∈ Finset.range N, v i
  have hpartial : ∀ᶠ m : ℕ in atTop,
      (∑ i ∈ Finset.range m, v i) - c₀ ≤ ∑ i ∈ Finset.range m, u i := by
    filter_upwards [eventually_ge_atTop N] with m hm
    have hsu := Finset.sum_range_add u N (m - N)
    have hsv := Finset.sum_range_add v N (m - N)
    rw [Nat.add_sub_of_le hm] at hsu hsv
    have htail : (∑ i ∈ Finset.range (m - N), v (N + i)) ≤
        ∑ i ∈ Finset.range (m - N), u (N + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hN (N + i) (by omega)
    have hsumUN : 0 ≤ ∑ i ∈ Finset.range N, u i := by
      exact Finset.sum_nonneg (fun i hi ↦ hu i)
    dsimp [c₀]
    rw [hsv, hsu]
    linarith
  have hlimg : Tendsto (fun m : ℕ ↦
      (∑ i ∈ Finset.range m, v i) - c₀) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-c₀) hlimv
    simpa [sub_eq_add_neg] using h
  exact Filter.tendsto_atTop_mono' atTop hpartial hlimg

/- A natural-valued specialization retained for callers that count blocks explicitly. -/
theorem tendsto_inv_zero_of_eventually_ge_mul_natCast
    (mass : ℕ → ℝ) (blocks : ℕ → ℕ) {c : ℝ}
    (hc : 0 < c)
    (hblocks : Tendsto (fun X : ℕ ↦ (blocks X : ℝ)) atTop atTop)
    (hlower : ∀ᶠ X : ℕ in atTop, c * (blocks X : ℝ) ≤ mass X) :
    Tendsto (fun X : ℕ ↦ (mass X)⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_zero_of_eventually_ge_mul_real mass
    (fun X : ℕ ↦ (blocks X : ℝ)) hc hblocks hlower

end Erdos878

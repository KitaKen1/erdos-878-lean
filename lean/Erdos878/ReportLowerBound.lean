import Erdos878.GoodPairSelection

/-!
# From the report's exceptional set to a pointwise `F` lower bound

At one fixed report scale, remove the integers divisible by a bad cross-window prime pair.
Every remaining integer has a complete bipartite graph of good *actual prime divisors*, so the
selection theorem retains the smaller of the two divisor counts.  This is the local statement
that will be stitched over geometric endpoint blocks; it assumes no monotonicity of the bad-pair
family as the scale changes.
-/

open Classical Filter
open scoped Topology Real

namespace Erdos878

theorem mem_divisibleBySomePairUpTo_of_bad_cross_divisors
    {T α β γ δ rho : ℝ} {n p q : ℕ}
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hn : n ≠ 0)
    (hpw : p ∈ primeWindow T α β) (hqw : q ∈ primeWindow T γ δ)
    (hpd : p ∣ n) (hqd : q ∣ n)
    (hbad : (p, q) ∈ badPairsAtReportScale T α β γ δ rho) :
    n ∈ divisibleBySomePairUpTo n (badPairsAtReportScale T α β γ δ rho) := by
  have hp : p.Prime := (Finset.mem_filter.mp hpw).2.1
  have hq : q.Prime := (Finset.mem_filter.mp hqw).2.1
  have hpq : p ≠ q := by
    intro heq
    have hratio := primeWindow_log_ratio_gt_one hpw hqw hT hβγ
    rw [heq, div_self (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'] at hratio
    exact (lt_irrefl _ hratio)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hpqd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
  unfold divisibleBySomePairUpTo
  rw [Finset.mem_biUnion]
  refine ⟨(p, q), hbad, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hn, hpqd⟩

theorem eventually_F_lower_of_report_nonexceptional
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ n : ℕ, n ≠ 0 → T / 2 ≤ Real.log (n : ℝ) →
      n ∉ divisibleBySomePairUpTo n (badPairsAtReportScale T α β γ δ rho) →
      min (divisorCount (primeWindow T α β) n)
          (divisorCount (primeWindow T γ δ) n) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  filter_upwards [eventually_F_lower_of_bad_pair_free_divisor_windows
      hβγ hδ0 hδ1 hβδ hrho,
    eventually_ge_atTop (1 : ℝ)] with T hselect hT
  intro n hn0 hn hnonexceptional
  let P : Finset ℕ := (primeWindow T α β).filter (fun p ↦ p ∣ n)
  let Q : Finset ℕ := (primeWindow T γ δ).filter (fun q ↦ q ∣ n)
  have hgood : ∀ p ∈ P, ∀ q ∈ Q,
      (p, q) ∉ badPairsAtReportScale T α β γ δ rho := by
    intro p hp q hq hbad
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    exact hnonexceptional
      (mem_divisibleBySomePairUpTo_of_bad_cross_divisors
        hT hβγ hn0 hp'.1 hq'.1 hp'.2 hq'.2 hbad)
  have hbase := hselect n P Q hn
    (by exact Finset.filter_subset _ _)
    (by exact Finset.filter_subset _ _)
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)
    (by intro q hq; exact (Finset.mem_filter.mp hq).2)
    hgood
  simpa [P, Q, divisorCount, Nat.cast_min] using hbase

end Erdos878

#print axioms Erdos878.eventually_F_lower_of_report_nonexceptional

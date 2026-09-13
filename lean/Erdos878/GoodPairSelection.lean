import Erdos878.GoodPairPacking

/-!
# Complete-bipartite pairing on the bad-pair-free part of a block

If every cross pair of actual prime divisors is good, take equally sized subsets and use a
bijection. This avoids any local-degree or Hall hypothesis and retains the minimum of the two
divisor counts, the quantity controlled by window normal-order estimates.
-/

open Classical Filter
open scoped Topology Real

namespace Erdos878

theorem eventually_F_lower_of_bad_pair_free_divisor_windows
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (n : ℕ) (P Q : Finset ℕ), T / 2 ≤ Real.log (n : ℝ) →
      P ⊆ primeWindow T α β → Q ⊆ primeWindow T γ δ →
      (∀ p ∈ P, p ∣ n) → (∀ q ∈ Q, q ∣ n) →
      (∀ p ∈ P, ∀ q ∈ Q, (p, q) ∉ badPairsAtReportScale T α β γ δ rho) →
      ((min P.card Q.card : ℕ) : ℝ) * (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  filter_upwards [eventually_admissible_packing_of_report_good_pairing
    hβγ hδ0 hδ1 hβδ hrho] with T hpack
  intro n P Q hn hPw hQw hPd hQd hgood
  obtain ⟨P', hPsub, hPcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_left P.card Q.card)
  obtain ⟨Q', hQsub, hQcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right P.card Q.card)
  let e : {p // p ∈ P'} ≃ {q // q ∈ Q'} := Finset.equivOfCardEq (hPcard.trans hQcard.symm)
  let pp : {p // p ∈ P'} → ℕ := fun p ↦ p.1
  let qq : {p // p ∈ P'} → ℕ := fun p ↦ (e p).1
  have hppw : ∀ i, pp i ∈ primeWindow T α β := fun i ↦ hPw (hPsub i.2)
  have hqqw : ∀ i, qq i ∈ primeWindow T γ δ := fun i ↦ hQw (hQsub (e i).2)
  have hppd : ∀ i, pp i ∣ n := fun i ↦ hPd i.1 (hPsub i.2)
  have hqqd : ∀ i, qq i ∣ n := fun i ↦ hQd (e i).1 (hQsub (e i).2)
  have hppi : Function.Injective pp := Subtype.val_injective
  have hqqi : Function.Injective qq := Subtype.val_injective.comp e.injective
  have hgg : ∀ i, (pp i, qq i) ∉ badPairsAtReportScale T α β γ δ rho :=
    fun i ↦ hgood i.1 (hPsub i.2) (e i).1 (hQsub (e i).2)
  obtain ⟨A, hA, hcard, _, hlow⟩ := hpack pp qq n hppw hqqw hppd hqqd hppi hqqi hn hgg
  have hcardA : A.card = min P.card Q.card := by
    simpa only [Fintype.card_coe, hPcard] using hcard
  calc
    ((min P.card Q.card : ℕ) : ℝ) * (n : ℝ) / Real.exp rho =
        ∑ _z ∈ A, (n : ℝ) / Real.exp rho := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcardA]
      ring
    _ ≤ ∑ z ∈ A, (z : ℝ) := Finset.sum_le_sum hlow
    _ = ((∑ z ∈ A, z : ℕ) : ℝ) := by
      simp only [Nat.cast_sum]
    _ ≤ (F n : ℝ) := by exact_mod_cast sum_le_F_of_admissible hA

end Erdos878

#print axioms Erdos878.eventually_F_lower_of_bad_pair_free_divisor_windows

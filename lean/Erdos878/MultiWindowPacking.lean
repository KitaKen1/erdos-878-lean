import Erdos878.MultiWindowExceptional

/-!
# Packing all report-window pairs into one admissible family

It is invalid to add separate inequalities of the form `cᵢ ≤ F n`.  Instead we select equally
many actual prime divisors from the two sides of every window pair, take their dependent sum as
one finite index type, construct one near-endpoint product for each index, and invoke the generic
packing theorem once.  Global window separation supplies injectivity and cross-disjointness.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

/-- For all sufficiently large report parameters, every nonexceptional integer admits one
combined packing whose size is the sum of the minimum divisor counts over all `k` pairs. -/
theorem eventually_multiWindow_F_lower (k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → T / 2 ≤ Real.log (n : ℝ) →
      (∀ i : Fin k, n ∉ divisibleBySomePairUpTo n
        (badPairsAtReportScale T
          (multiWindowAlpha k i) (multiWindowBeta k i)
          (multiWindowGamma k i) (multiWindowDelta k i) rho)) →
      (∑ i : Fin k,
          min
            (divisorCount
              (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)) n)
            (divisorCount
              (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)) n)) *
          (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  have hconstructAll : ∀ᶠ T : ℝ in atTop, ∀ i : Fin k,
      ∀ p ∈ primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i),
      ∀ q ∈ primeWindow T (multiWindowGamma k i) (multiWindowDelta k i),
      ∀ n : ℕ, T / 2 ≤ Real.log (n : ℝ) →
        (p, q) ∉ badPairsAtReportScale T
          (multiWindowAlpha k i) (multiWindowBeta k i)
          (multiWindowGamma k i) (multiWindowDelta k i) rho →
        ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
          (n : ℝ) / Real.exp rho ≤ ((p ^ a * q ^ b : ℕ) : ℝ) ∧
          p ^ a * q ^ b ≤ n := by
    rw [Filter.eventually_all]
    intro i
    rcases multiWindow_report_parameter_conditions i with
      ⟨_, _, _, hβγ, _, hδ0, hδ1, hβδ⟩
    exact eventually_exists_positive_power_product_of_report_good_pair
      hβγ hδ0 hδ1 hβδ hrho
  filter_upwards [hconstructAll, eventually_ge_atTop (1 : ℝ)] with T hconstruct hT
  intro n hn0 hnlog hnonexceptional
  let L : Fin k → Finset ℕ := fun i ↦
    (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)).filter
      (fun p ↦ p ∣ n)
  let R : Fin k → Finset ℕ := fun i ↦
    (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)).filter
      (fun q ↦ q ∣ n)
  have hselectL : ∀ i : Fin k, ∃ P : Finset ℕ,
      P ⊆ L i ∧ P.card = min (L i).card (R i).card := by
    intro i
    exact Finset.exists_subset_card_eq (Nat.min_le_left (L i).card (R i).card)
  have hselectR : ∀ i : Fin k, ∃ Q : Finset ℕ,
      Q ⊆ R i ∧ Q.card = min (L i).card (R i).card := by
    intro i
    exact Finset.exists_subset_card_eq (Nat.min_le_right (L i).card (R i).card)
  choose P hPsub hPcard using hselectL
  choose Q hQsub hQcard using hselectR
  let e : ∀ i : Fin k, {p // p ∈ P i} ≃ {q // q ∈ Q i} := fun i ↦
    Finset.equivOfCardEq ((hPcard i).trans (hQcard i).symm)
  let ι := Σ i : Fin k, {p // p ∈ P i}
  let pp : ι → ℕ := fun x ↦ x.2.1
  let qq : ι → ℕ := fun x ↦ (e x.1 x.2).1
  have hppw : ∀ x : ι,
      pp x ∈ primeWindow T
        (multiWindowAlpha k x.1) (multiWindowBeta k x.1) := by
    intro x
    have hxL : x.2.1 ∈ L x.1 := hPsub x.1 x.2.2
    exact (Finset.mem_filter.mp hxL).1
  have hqqw : ∀ x : ι,
      qq x ∈ primeWindow T
        (multiWindowGamma k x.1) (multiWindowDelta k x.1) := by
    intro x
    have hxR : (e x.1 x.2).1 ∈ R x.1 := hQsub x.1 (e x.1 x.2).2
    exact (Finset.mem_filter.mp hxR).1
  have hppd : ∀ x : ι, pp x ∣ n := by
    intro x
    have hxL : x.2.1 ∈ L x.1 := hPsub x.1 x.2.2
    exact (Finset.mem_filter.mp hxL).2
  have hqqd : ∀ x : ι, qq x ∣ n := by
    intro x
    have hxR : (e x.1 x.2).1 ∈ R x.1 := hQsub x.1 (e x.1 x.2).2
    exact (Finset.mem_filter.mp hxR).2
  have hpinj : Function.Injective pp := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    have hidx : i = j := by
      apply eq_of_mem_multiWindow_left hT (hppw ⟨i, p⟩)
      rw [show pp ⟨i, p⟩ = pp ⟨j, q⟩ from hpq]
      exact hppw ⟨j, q⟩
    subst j
    have hpq' : p = q := Subtype.ext hpq
    subst q
    rfl
  have hqinj : Function.Injective qq := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    have hidx : i = j := by
      apply eq_of_mem_multiWindow_right hT (hqqw ⟨i, p⟩)
      rw [show qq ⟨i, p⟩ = qq ⟨j, q⟩ from hpq]
      exact hqqw ⟨j, q⟩
    subst j
    have heq : e i p = e i q := Subtype.ext hpq
    have hpq' : p = q := (e i).injective heq
    subst q
    rfl
  have hpprime : ∀ x : ι, (pp x).Prime := fun x ↦
    (Finset.mem_filter.mp (hppw x)).2.1
  have hqprime : ∀ x : ι, (qq x).Prime := fun x ↦
    (Finset.mem_filter.mp (hqqw x)).2.1
  have hcross : ∀ x y : ι, pp x ≠ qq y := by
    intro x y heq
    have hratio := primeWindow_log_ratio_gt_one (hppw x) (hqqw y) hT
      (multiWindow_beta_lt_gamma_cross x.1 y.1).le
    rw [heq, div_self
      (Real.log_pos (by exact_mod_cast (hqprime y).one_lt)).ne'] at hratio
    exact (lt_irrefl _ hratio)
  have hgood : ∀ x : ι,
      (pp x, qq x) ∉ badPairsAtReportScale T
        (multiWindowAlpha k x.1) (multiWindowBeta k x.1)
        (multiWindowGamma k x.1) (multiWindowDelta k x.1) rho := by
    intro x hbad
    apply hnonexceptional x.1
    exact mem_divisibleBySomePairUpTo_of_bad_cross_divisors
      hT (multiWindow_beta_le_gamma x.1) hn0
      (hppw x) (hqqw x) (hppd x) (hqqd x) hbad
  have hterms : ∀ x : ι, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (n : ℝ) / Real.exp rho ≤ ((pp x ^ a * qq x ^ b : ℕ) : ℝ) ∧
      pp x ^ a * qq x ^ b ≤ n := fun x ↦
    hconstruct x.1 (pp x) (hppw x) (qq x) (hqqw x) n hnlog (hgood x)
  have hpack := real_card_mul_div_le_F_of_positive_power_products
    pp qq hpprime hqprime hppd hqqd hpinj hqinj hcross hterms
  have hcard : (Fintype.card ι : ℝ) =
      ∑ i : Fin k,
        min
          (divisorCount
            (primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i)) n)
          (divisorCount
            (primeWindow T (multiWindowGamma k i) (multiWindowDelta k i)) n) := by
    simp only [ι, Fintype.card_sigma, Fintype.card_coe, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hPcard i]
    simp only [L, R, divisorCount, Nat.cast_min]
  rw [hcard] at hpack
  exact hpack

end

end Erdos878

#print axioms Erdos878.eventually_multiWindow_F_lower

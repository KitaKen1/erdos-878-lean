import Erdos878FC
import Erdos878.GoodPairReport

/-!
# Admissible packing of constructed prime-power pairs

Positive exponents retain both primes. Consequently disjoint pairs give distinct, coprime
terms automatically; these are not additional assumptions about the constructed products.
-/

open Classical Filter
open scoped Topology Real

namespace Erdos878

/-- Turn genuinely constructed near-endpoint products into the finite-set definition of `F`. -/
theorem exists_admissible_packing_of_positive_power_products
    {ι : Type*} [Fintype ι] {n : ℕ} {C : ℝ} (p q : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hpd : ∀ i, p i ∣ n) (hqd : ∀ i, q i ∣ n)
    (hpinj : Function.Injective p) (hqinj : Function.Injective q)
    (hcross : ∀ i j, p i ≠ q j)
    (hterms : ∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (n : ℝ) / C ≤ ((p i ^ a * q i ^ b : ℕ) : ℝ) ∧ p i ^ a * q i ^ b ≤ n) :
    ∃ A : Finset ℕ, IsAdmissible n A ∧ A.card = Fintype.card ι ∧
      (∀ z ∈ A, z.primeFactors.card = 2) ∧ (∀ z ∈ A, (n : ℝ) / C ≤ (z : ℝ)) := by
  classical
  choose a b ha hb hlo hhi using hterms
  let term : ι → ℕ := fun i ↦ p i ^ a i * q i ^ b i
  have hpos : ∀ i, 0 < term i := by
    intro i
    exact Nat.mul_pos (pow_pos (hp i).pos _) (pow_pos (hq i).pos _)
  have hnontrivial : ∀ i, 2 ≤ term i := by
    intro i
    have hpdiv : p i ∣ term i := by
      exact dvd_mul_of_dvd_left (dvd_pow_self _ (ha i).ne') _
    exact (hp i).two_le.trans (Nat.le_of_dvd (hpos i) hpdiv)
  have hfac : ∀ i, (term i).primeFactors = {p i, q i} := fun i ↦
    primeFactors_positive_power_product (hp i) (hq i) (ha i) (hb i)
  have hinj : Function.Injective term := by
    intro i j hij
    have hmem : p i ∈ (term i).primeFactors := by rw [hfac]; simp
    rw [hij, hfac] at hmem
    rcases Finset.mem_insert.mp hmem with heq | hqj
    · exact hpinj heq
    · exact False.elim (hcross i j (Finset.mem_singleton.mp hqj))
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (term i) (term j) := by
    intro i j hij
    apply (Nat.disjoint_primeFactors (hpos i).ne' (hpos j).ne').mp
    rw [hfac, hfac]
    rw [Finset.disjoint_left]
    intro s hsi hsj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsi hsj
    rcases hsi with rfl | rfl <;> rcases hsj with heq | heq
    · exact hij (hpinj heq)
    · exact hcross i j heq
    · exact hcross j i heq.symm
    · exact hij (hqinj heq)
  let A := Finset.univ.image term
  have hA : IsAdmissible n A := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr ⟨hnontrivial i, hhi i⟩
    · intro z hz w hw hzw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact hcop i j (fun heq ↦ hzw (congrArg term heq))
    · intro z hz s hs hsz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      have hsF := Nat.mem_primeFactors.mpr ⟨hs, hsz, (hpos i).ne'⟩
      rw [hfac] at hsF
      rcases Finset.mem_insert.mp hsF with heq | hqi
      · simpa only [heq] using hpd i
      · simpa only [Finset.mem_singleton.mp hqi] using hqd i
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_univ
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hfac]
    simp [hcross i i]
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hlo i

theorem real_card_mul_div_le_F_of_positive_power_products
    {ι : Type*} [Fintype ι] {n : ℕ} {C : ℝ} (p q : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hpd : ∀ i, p i ∣ n) (hqd : ∀ i, q i ∣ n)
    (hpinj : Function.Injective p) (hqinj : Function.Injective q)
    (hcross : ∀ i j, p i ≠ q j)
    (hterms : ∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (n : ℝ) / C ≤ ((p i ^ a * q i ^ b : ℕ) : ℝ) ∧ p i ^ a * q i ^ b ≤ n) :
    (Fintype.card ι : ℝ) * (n : ℝ) / C ≤ (F n : ℝ) := by
  obtain ⟨A, hA, hcard, _, hlow⟩ := exists_admissible_packing_of_positive_power_products
    p q hp hq hpd hqd hpinj hqinj hcross hterms
  calc
    (Fintype.card ι : ℝ) * (n : ℝ) / C = ∑ _z ∈ A, (n : ℝ) / C := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ ≤ ∑ z ∈ A, (z : ℝ) := Finset.sum_le_sum hlow
    _ = ((∑ z ∈ A, z : ℕ) : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ (F n : ℝ) := by exact_mod_cast sum_le_F_of_admissible hA

/-- The report parameters now give actual `F`-contributing terms, not just a rotation certificate.
Prime injectivity is enough; coprimality, distinctness and two-prime support are conclusions. -/
theorem eventually_admissible_packing_of_report_good_pairing
    {α β γ δ rho : ℝ}
    (hβγ : β ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] (p q : ι → ℕ) (n : ℕ),
      (∀ i, p i ∈ primeWindow T α β) → (∀ i, q i ∈ primeWindow T γ δ) →
      (∀ i, p i ∣ n) → (∀ i, q i ∣ n) →
      Function.Injective p → Function.Injective q →
      T / 2 ≤ Real.log (n : ℝ) →
      (∀ i, (p i, q i) ∉ badPairsAtReportScale T α β γ δ rho) →
      ∃ A : Finset ℕ, IsAdmissible n A ∧ A.card = Fintype.card ι ∧
        (∀ z ∈ A, z.primeFactors.card = 2) ∧
        (∀ z ∈ A, (n : ℝ) / Real.exp rho ≤ (z : ℝ)) := by
  filter_upwards [eventually_exists_positive_power_product_of_report_good_pair
    hβγ hδ0 hδ1 hβδ hrho, eventually_ge_atTop (1 : ℝ)] with T hconstruct hT
  intro ι inst p q n hpw hqw hpd hqd hpinj hqinj hn hgood
  have hp : ∀ i, (p i).Prime := fun i ↦ (Finset.mem_filter.mp (hpw i)).2.1
  have hq : ∀ i, (q i).Prime := fun i ↦ (Finset.mem_filter.mp (hqw i)).2.1
  have hcross : ∀ i j, p i ≠ q j := by
    intro i j heq
    have hh := primeWindow_log_ratio_gt_one (hpw i) (hqw j) hT hβγ
    rw [heq, div_self (Real.log_pos (by exact_mod_cast (hq j).one_lt)).ne'] at hh
    exact (lt_irrefl _ hh)
  exact exists_admissible_packing_of_positive_power_products p q hp hq hpd hqd hpinj hqinj
    hcross (fun i ↦ hconstruct (p i) (hpw i) (q i) (hqw i) n hn (hgood i))

end Erdos878

#print axioms Erdos878.eventually_admissible_packing_of_report_good_pairing

import Erdos878.Rotation
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Nat.PrimeFin

/-!
# Constructing actual two-prime powers from a good pair

Unlike an interface which assumes an approximation or a large product in advance, this module
uses Dirichlet's theorem to produce the approximation. Excluding bad pairs forces its denominator
to be large. Shifting the logarithmic target by `log p + log q` makes both final exponents positive.
-/

open Classical Filter
open scoped Topology Real

namespace Erdos878

/-- Dirichlet approximation with a nonnegative numerator in lowest terms. -/
theorem exists_coprime_nat_approx_of_one_le {ξ : ℝ} (hξ : 1 ≤ ξ)
    {M : ℕ} (hM : 0 < M) :
    ∃ r h : ℕ, 0 < r ∧ r ≤ M ∧ Nat.Coprime h r ∧
      |ξ - (h : ℝ) / (r : ℝ)| ≤ 1 / ((r : ℝ) * (M : ℝ)) := by
  obtain ⟨s, hs, hsM⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ hM
  have hr : 0 < (s.den : ℝ) := by exact_mod_cast s.pos
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hrone : (1 : ℝ) ≤ (s.den : ℝ) := by exact_mod_cast s.pos
  have herr : 1 / (((M : ℝ) + 1) * (s.den : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hspos : (0 : ℝ) ≤ (s : ℝ) := by
    have := (abs_le.mp hs).2
    linarith
  have hnum : 0 ≤ s.num := Rat.num_nonneg.mpr (by exact_mod_cast hspos)
  have hcast : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    have hz : (s.num.natAbs : ℤ) = s.num := Int.natAbs_of_nonneg hnum
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℝ)) hz
  refine ⟨s.den, s.num.natAbs, s.pos, hsM, s.reduced, ?_⟩
  rw [hcast, ← Rat.cast_def]
  exact hs.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))

/-- The shifted target is beyond every congruence obstruction for a bounded denominator. -/
theorem shifted_rotation_floor_threshold
    {L Q t : ℝ} {r h M : ℕ}
    (hL : 0 < L) (hQ : 0 ≤ Q) (hM : 0 < M) (hr : 0 < r) (hrM : r ≤ M)
    (happrox : |Q / L - (h : ℝ) / (r : ℝ)| ≤ 1 / ((r : ℝ) * (M : ℝ)))
    (hbudget : ((M : ℝ) + 1) * Q + 3 * L ≤ t) :
    (((r - 1) * h : ℕ) : ℝ) ≤
      (r : ℝ) * ((t - L - Q) / L - 1 / (M : ℝ)) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hrMreal : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrM
  have hupper : (h : ℝ) / (r : ℝ) ≤ Q / L + 1 / ((r : ℝ) * (M : ℝ)) := by
    have := (abs_le.mp happrox).1
    linarith
  have hnum : (h : ℝ) * L ≤ (r : ℝ) * Q + L / (M : ℝ) := by
    have hh := (div_le_iff₀ hrpos).mp hupper
    have hhL := mul_le_mul_of_nonneg_right hh hL.le
    calc
      (h : ℝ) * L ≤ ((Q / L + 1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ)) * L := hhL
      _ = (r : ℝ) * Q + L / (M : ℝ) := by
        field_simp [hL.ne', hrpos.ne', hMpos.ne']
  have hLM : L / (M : ℝ) ≤ L := (div_le_self hL.le hMone)
  have hrMQ : (r : ℝ) * Q ≤ (M : ℝ) * Q :=
    mul_le_mul_of_nonneg_right hrMreal hQ
  have hgrid : (h : ℝ) ≤ (t - L - Q) / L - 1 / (M : ℝ) := by
    apply (le_sub_iff_add_le).2
    apply (le_div_iff₀ hL).2
    have hcomm : (1 / (M : ℝ)) * L = L / (M : ℝ) := by ring
    rw [add_mul, hcomm]
    nlinarith
  have hnat : (r - 1) * h ≤ r * h := Nat.mul_le_mul_right h (Nat.sub_le _ _)
  calc
    (((r - 1) * h : ℕ) : ℝ) ≤ ((r * h : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (r : ℝ) * (h : ℝ) := by norm_cast
    _ ≤ (r : ℝ) * ((t - L - Q) / L - 1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hgrid hrpos.le

/-- A good pair yields a near-endpoint product; neither exponent is allowed to vanish. -/
theorem exists_positive_power_product_of_good_pair
    {p q n M : ℕ} {rho : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) (hn : 0 < n) (hM : 0 < M) (hrho : 0 < rho)
    (hwidth : 8 * Real.log (p : ℝ) ≤ rho * (M : ℝ))
    (hbudget : ((M : ℝ) + 1) * Real.log (q : ℝ) +
      3 * Real.log (p : ℝ) ≤ Real.log (n : ℝ))
    (hgood : ∀ r h : ℕ, ¬ isBadApprox rho M p q r h) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (n : ℝ) / Real.exp rho ≤ ((p ^ a * q ^ b : ℕ) : ℝ) ∧ p ^ a * q ^ b ≤ n := by
  let L : ℝ := Real.log (p : ℝ)
  let Q : ℝ := Real.log (q : ℝ)
  let t : ℝ := Real.log (n : ℝ) - L - Q
  have hp0 : 0 < p := by omega
  have hq : 1 < q := lt_of_lt_of_le hp hpq
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp)
  have hQ : 0 < Q := Real.log_pos (by exact_mod_cast hq)
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hLQ : L ≤ Q := Real.log_le_log (by exact_mod_cast hp0) (by exact_mod_cast hpq)
  have hratio : 1 ≤ Q / L := (le_div_iff₀ hL).2 (by simpa using hLQ)
  obtain ⟨r, h, hr, hrM, hcop, happ⟩ := exists_coprime_nat_approx_of_one_le hratio hM
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrlarge : denominatorCutoff p rho ≤ r := by
    apply Nat.le_of_not_gt
    intro hrsmall
    exact hgood r h ⟨hr, hrsmall, happ⟩
  have hthreshold : (((r - 1) * h : ℕ) : ℝ) ≤ (r : ℝ) * (t / L - 1 / (M : ℝ)) :=
    shifted_rotation_floor_threshold hL hQ.le hM hr hrM happ hbudget
  obtain ⟨a, b, hb, hab⟩ := exists_nonneg_floor_rep_of_coprime hr hcop hthreshold
  have hxi : 0 ≤ (r : ℝ) * (t / L - 1 / (M : ℝ)) :=
    (by positivity : 0 ≤ (((r - 1) * h : ℕ) : ℝ)).trans hthreshold
  have hgap := rotation_gap_of_floor_congruence hL hQ hMpos hr hb happ hab
    (Nat.floor_le hxi) (Nat.lt_floor_add_one _)
  have hrr : 4 * L / rho ≤ (r : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hrlarge)
  have hLr : L / (r : ℝ) ≤ rho / 4 := by
    apply (div_le_iff₀ hrpos).2
    have hh := (div_le_iff₀ hrho).mp hrr
    nlinarith
  have hLM : 2 * L / (M : ℝ) ≤ rho / 4 := by
    apply (div_le_iff₀ hMpos).2
    dsimp [L] at *
    nlinarith
  have hfullgap : 0 ≤ Real.log (n : ℝ) -
      (((a + 1 : ℕ) : ℝ) * L + ((b + 1 : ℕ) : ℝ) * Q) := by
    push_cast
    dsimp [t] at hgap
    linarith [hgap.1]
  have hfullrho : Real.log (n : ℝ) -
      (((a + 1 : ℕ) : ℝ) * L + ((b + 1 : ℕ) : ℝ) * Q) ≤ Real.log (Real.exp rho) := by
    rw [Real.log_exp]
    push_cast
    dsimp [t] at hgap
    linarith [hgap.2]
  have hprod := power_product_mem_Icc_of_log_gap hp0 (by omega) hn (Real.exp_pos rho)
    (p := p) (q := q) (a := a + 1) (b := b + 1) rfl rfl rfl hfullgap hfullrho
  exact ⟨a + 1, b + 1, by omega, by omega, hprod.1, by exact_mod_cast hprod.2⟩

/-- The constructed terms really consume exactly their two primes. -/
theorem primeFactors_positive_power_product {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b) :
    (p ^ a * q ^ b).primeFactors = {p, q} := by
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Nat.primeFactors_prime_pow ha.ne' hp, Nat.primeFactors_prime_pow hb.ne' hq]
  simp

end Erdos878

#print axioms Erdos878.exists_positive_power_product_of_good_pair

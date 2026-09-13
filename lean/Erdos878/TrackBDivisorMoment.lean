/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license; see LICENSE at the publication package root.

Modified for Erdős 878: standalone imports and namespace for the local Mathlib version.
Source: gersh/ternary-goldbach-lean, commit 27df23af6a712895f22204d0d81102baa74f0ebe,
MathExtras/NumberTheory/Vinogradov/HardCutoffTypeIIQSensitive.lean.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Track B: the divisor second moment

The bound is uniform in the endpoint, including zero. It supplies the logarithmic coefficient
budget for the nonlinear Type-II estimates without using a pointwise power-loss bound on τ.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- Harmonic-sum bound `Σ_{d=1}^N 1/d ≤ 1 + log N` (Mathlib's
`harmonic_le_one_add_log`, recast over `ℝ` on `Icc 1 N`). -/
theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have heq : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  linarith [heq ▸ h]

/-- The reciprocal sum over multiples of `g` in `[1, N]` is at most
`(1/g)·H(N)`. -/
theorem sum_Icc_ite_dvd_inv_le (N g : ℕ) (hg : 1 ≤ g) :
    ∑ d ∈ Finset.Icc 1 N, (if g ∣ d then ((d : ℝ))⁻¹ else 0) ≤
      ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hsub : {d ∈ Finset.Icc 1 N | g ∣ d} ⊆
      (Finset.Icc 1 N).image (fun e => g * e) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hgd⟩ := hd
    refine Finset.mem_image.mpr ⟨d / g, ?_, Nat.mul_div_cancel' hgd⟩
    rw [Finset.mem_Icc]
    refine ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hgd),
      (Nat.div_le_self d g).trans hdN⟩
  calc ∑ d ∈ {d ∈ Finset.Icc 1 N | g ∣ d}, ((d : ℝ))⁻¹
      ≤ ∑ d ∈ (Finset.Icc 1 N).image (fun e => g * e), ((d : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ = ∑ e ∈ Finset.Icc 1 N, (((g * e : ℕ) : ℝ))⁻¹ :=
        Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)
    _ = ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        push_cast
        rw [mul_inv]

/-! ## Layer 2b: the divisor second moment -/

/-- **Divisor-count second moment** (crude but honest):
`Σ_{m=1}^N τ(m)² ≤ N·(1 + log N)³`.

Double counting: `τ(m)² = Σ_{d₁,d₂ ∣ m} 1`, the inner count of
`m ∈ (0,N]` divisible by both is `⌊N/lcm⌋ ≤ N·gcd/(d₁d₂)`, the gcd is
bounded by the sum of common divisors `g`, and the three resulting
reciprocal sums are each one harmonic factor `H(N) ≤ 1 + log N`. -/
theorem sum_Ioc_card_divisors_sq_le (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  classical
  set H : ℝ := ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ with hH
  have hH_nonneg : 0 ≤ H := Finset.sum_nonneg fun e _ => by positivity
  have hH_le : H ≤ 1 + Real.log N := sum_Icc_inv_le_one_add_log N
  -- the indicator reciprocal sum
  set A : ℕ → ℝ := fun g => ∑ d ∈ Finset.Icc 1 N,
    (if g ∣ d then ((d : ℝ))⁻¹ else 0) with hA
  have hA_nonneg : ∀ g, 0 ≤ A g := fun g =>
    Finset.sum_nonneg fun d _ => by by_cases h : g ∣ d <;> simp [h]
  have hA_le : ∀ g, 1 ≤ g → A g ≤ ((g : ℝ))⁻¹ * H := fun g hg =>
    sum_Icc_ite_dvd_inv_le N g hg
  -- Step 1: pointwise divisor-count expansion
  have hcard : ∀ m ∈ Finset.Ioc 0 N,
      ((m.divisors.card : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) := by
    intro m hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hm
    have hset : m.divisors = {d ∈ Finset.Icc 1 N | d ∣ m} := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        have hd0 : d ≠ 0 := by
          rintro rfl
          exact absurd (zero_dvd_iff.mp hdvd) (by omega)
        exact ⟨⟨by omega, (Nat.le_of_dvd hm0 hdvd).trans hmN⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hset, Finset.sum_boole]
  -- Step 2+3: expand the square, swap, evaluate the inner sum to ⌊N/lcm⌋
  have hmain : ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
        ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
    calc ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2
        = ∑ m ∈ Finset.Ioc 0 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hcard m hm, sq, Finset.sum_mul_sum]
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc 0 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
          have hpt : ∀ m : ℕ,
              (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) =
                (if Nat.lcm d₁ d₂ ∣ m then (1 : ℝ) else 0) := by
            intro m
            by_cases h1 : d₁ ∣ m <;> by_cases h2 : d₂ ∣ m
            · simp [h1, h2, Nat.lcm_dvd h1 h2]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h2 ((Nat.dvd_lcm_right d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
          simp_rw [hpt]
          rw [Finset.sum_boole]
          norm_cast
          exact Nat.Ioc_filter_dvd_card_eq_div N (Nat.lcm d₁ d₂)
  rw [hmain]
  -- Step 4: ⌊N/lcm⌋ ≤ N·gcd/(d₁·d₂)
  have hstep4 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤
        ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
    refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
    obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
    obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
    have hlcm0 : 0 < Nat.lcm d₁ d₂ :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have h1 : ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤ (N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) :=
      Nat.cast_div_le
    refine h1.trans (le_of_eq ?_)
    have hgl : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
        (d₁ : ℝ) * (d₂ : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgcd0 : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hgl, mul_comm (N : ℝ) ((Nat.gcd d₁ d₂ : ℕ) : ℝ),
      mul_div_mul_left _ _ hgcd0]
  refine hstep4.trans ?_
  -- Step 5: gcd ≤ Σ_g common-divisor indicator
  have hgcd_le : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
      ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≤
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) := by
    intro d₁ hd₁ d₂ hd₂
    obtain ⟨h11, h1N⟩ := Finset.mem_Icc.mp hd₁
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgle : Nat.gcd d₁ d₂ ≤ d₁ := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d₁ d₂)
    have hgmem : Nat.gcd d₁ d₂ ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsingle := Finset.single_le_sum
      (f := fun g => if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0)
      (fun g _ => by by_cases h : g ∣ d₁ ∧ g ∣ d₂ <;> simp [h]) hgmem
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using hsingle
  -- Step 6: rearrange to N · Σ_g g · A(g)²
  have hstep6 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
        (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
    have hpoint : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
        (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
          ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
            ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) := by
      intro d₁ hd₁ d₂ hd₂
      obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
      obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
      have hfact : ∀ g : ℕ,
          (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
            (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
          (N : ℝ) * (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) /
            ((d₁ : ℝ) * (d₂ : ℝ)) := by
        intro g
        by_cases h1 : g ∣ d₁
        · by_cases h2 : g ∣ d₂
          · simp only [h1, h2, and_self, ite_true, div_eq_mul_inv, mul_inv]
            ring
          · simp [h1, h2]
        · simp [h1]
      simp_rw [hfact]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgcd_le d₁ hd₁ d₂ hd₂) (Nat.cast_nonneg N))
        (by positivity)
    calc ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ))
        ≤ ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
              ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ =>
            hpoint d₁ hd₁ d₂ hd₂
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ g ∈ Finset.Icc 1 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_comm
      _ = (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [hA]
          have hterm : ∀ d₁ d₂ : ℕ,
              (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
              ((N : ℝ) * (g : ℝ) * (if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0)) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) := fun _ _ => by ring
          simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
          rw [← Finset.mul_sum]
          ring
  refine hstep6.trans ?_
  -- Step 7: A(g) ≤ H/g, sum the harmonic factors
  have hstep7 : ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) ≤ H * H * H := by
    have hterm : ∀ g ∈ Finset.Icc 1 N,
        (g : ℝ) * (A g * A g) ≤ ((g : ℝ))⁻¹ * (H * H) := by
      intro g hg
      obtain ⟨hg1, _⟩ := Finset.mem_Icc.mp hg
      have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hg1
      have hAg := hA_le g hg1
      have hAg0 := hA_nonneg g
      have hinvH : 0 ≤ ((g : ℝ))⁻¹ * H := mul_nonneg (by positivity) hH_nonneg
      calc (g : ℝ) * (A g * A g)
          ≤ (g : ℝ) * ((((g : ℝ))⁻¹ * H) * (((g : ℝ))⁻¹ * H)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hgpos)
            exact mul_le_mul hAg hAg hAg0 hinvH
        _ = ((g : ℝ))⁻¹ * (H * H) := by
            field_simp
    calc ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
        ≤ ∑ g ∈ Finset.Icc 1 N, ((g : ℝ))⁻¹ * (H * H) := Finset.sum_le_sum hterm
      _ = H * (H * H) := by rw [← Finset.sum_mul, ← hH]
      _ = H * H * H := by ring
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
      ≤ (N : ℝ) * (H * H * H) := mul_le_mul_of_nonneg_left hstep7 hN0
    _ ≤ (N : ℝ) * ((1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N)) := by
        have h1 : H * H * H ≤ (1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N) := by
          have hl0 : (0 : ℝ) ≤ 1 + Real.log N := hH_nonneg.trans hH_le
          exact mul_le_mul (mul_le_mul hH_le hH_le hH_nonneg hl0) hH_le hH_nonneg
            (mul_nonneg hl0 hl0)
        exact mul_le_mul_of_nonneg_left h1 hN0
    _ = (N : ℝ) * (1 + Real.log N) ^ 3 := by ring


end
end Erdos878.TrackB

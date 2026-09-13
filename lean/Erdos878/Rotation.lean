/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Erdos878.BadPair
import Mathlib.Data.ZMod.Basic

/-!
# Logarithmic rotation bookkeeping

This module isolates the elementary floor/congruence part of the Track-A construction.  The finite
existence statement `exists_nonneg_rep_of_coprime` handles the reduced residue and nonnegative
coefficient once the coprime approximation and an explicit floor-index threshold are supplied.
The remaining analytic/Diophantine input is the uniform production of those data for useful prime
pairs.  Once supplied, `rotation_gap_of_floor_congruence` turns a logarithmic approximation into
the one-sided interval for a product of two prime powers.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos878

/- A finite modular bridge for the rotation construction.  If `h` is coprime to `r`, every
  sufficiently large grid index `j` has a representative `r * a + b * h` with a nonnegative
  exponent `a` and a reduced residue `b < r`.  This is the elementary part that is often left
  implicit in an analytic discussion; the genuinely difficult input is still the choice of a
  useful prime pair and the approximation of `Q/L` by `h/r`. -/
set_option linter.style.haveILetI false in
theorem exists_nonneg_rep_of_coprime
    {r h j : ℕ} (hr : 0 < r) (hcop : Nat.Coprime h r)
    (hj : (r - 1) * h ≤ j) :
    ∃ a b : ℕ, b < r ∧ r * a + b * h = j := by
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime h hcop
  let b : ℕ := (u⁻¹ * (j : ZMod r)).val
  have hb_lt : b < r := by
    exact ZMod.val_lt _
  have hb_cast : (b : ZMod r) = (u⁻¹ : ZMod r) * (j : ZMod r) := by
    dsimp [b]
    change (((u⁻¹ : ZMod r) * (j : ZMod r)).val : ZMod r) =
      (u⁻¹ : ZMod r) * (j : ZMod r)
    simpa only [ZMod.cast_id] using
      (ZMod.natCast_val (R := ZMod r) ((u⁻¹ : ZMod r) * (j : ZMod r)))
  have hunit_cast : (u : ZMod r) = (h : ZMod r) := by
    exact ZMod.coe_unitOfCoprime h hcop
  have hcongZ : (h : ZMod r) * (b : ZMod r) = (j : ZMod r) := by
    rw [hb_cast, ← hunit_cast]
    simp
  have hcong : b * h ≡ j [MOD r] := by
    apply (ZMod.natCast_eq_natCast_iff (b * h) j r).mp
    simpa [Nat.cast_mul, mul_comm] using hcongZ
  have hb_le : b ≤ r - 1 := Nat.le_pred_of_lt hb_lt
  have hbh_le : b * h ≤ (r - 1) * h := Nat.mul_le_mul_right h hb_le
  have hbhj : b * h ≤ j := hbh_le.trans hj
  have hdvd : r ∣ j - b * h := (Nat.modEq_iff_dvd' hbhj).mp hcong
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, b, hb_lt, ?_⟩
  have hsub : j - b * h = r * a := ha
  have heq : j = r * a + b * h := (Nat.sub_eq_iff_eq_add hbhj).mp hsub
  exact heq.symm

/- The form used by the rotation argument: it is enough to prove a real lower bound for the
   floor-grid point before taking the floor.  `Nat.le_floor` supplies the discrete threshold and
   the preceding modular lemma supplies the nonnegative exponents. -/
theorem exists_nonneg_floor_rep_of_coprime
    {r h : ℕ} {ξ : ℝ} (hr : 0 < r) (hcop : Nat.Coprime h r)
    (hx : (((r - 1) * h : ℕ) : ℝ) ≤ ξ) :
    ∃ a b : ℕ, b < r ∧ r * a + b * h = Nat.floor ξ := by
  have hj : (r - 1) * h ≤ Nat.floor ξ := Nat.le_floor hx
  exact exists_nonneg_rep_of_coprime hr hcop hj

/- A purely algebraic rotation lemma.  `j` is a floor-grid point and `r*a+b*h=j` is the
congruence solution.  The approximation error is measured in logarithmic coordinates; the
conclusion is exactly the one-sided gap needed before casting the exponents to powers. -/
theorem rotation_gap_of_floor_congruence
    {L Q t : ℝ} {r h a b j M : ℕ}
    (hL : 0 < L) (_hQ : 0 < Q) (hM : 0 < (M : ℝ))
    (hr : 0 < r) (hb : b < r)
    (happrox : |Q / L - (h : ℝ) / (r : ℝ)| ≤ 1 / ((r : ℝ) * (M : ℝ)))
    (hcong : r * a + b * h = j)
    (hfloor₁ : (j : ℝ) ≤ (r : ℝ) * (t / L - 1 / (M : ℝ)))
    (hfloor₂ : (r : ℝ) * (t / L - 1 / (M : ℝ)) < (j : ℝ) + 1) :
    0 ≤ t - ((a : ℝ) * L + (b : ℝ) * Q) ∧
      t - ((a : ℝ) * L + (b : ℝ) * Q) ≤ L / (r : ℝ) + 2 * L / (M : ℝ) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hbR : 0 ≤ (b : ℝ) := by positivity
  have hb_lt : (b : ℝ) < (r : ℝ) := by exact_mod_cast hb
  have hcongR : (r : ℝ) * (a : ℝ) + (b : ℝ) * (h : ℝ) = (j : ℝ) := by
    exact_mod_cast hcong
  have herror :
      |(b : ℝ) * (Q - ((h : ℝ) / (r : ℝ)) * L)| ≤ L / (M : ℝ) := by
    have hbound : (b : ℝ) * |Q / L - (h : ℝ) / (r : ℝ)| ≤
        (b : ℝ) * (1 / ((r : ℝ) * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left happrox hbR
    have hrewrite : (b : ℝ) * (Q - ((h : ℝ) / (r : ℝ)) * L) =
        (b : ℝ) * L * (Q / L - (h : ℝ) / (r : ℝ)) := by
      field_simp [hL.ne', hrR.ne', hM.ne']
    rw [hrewrite, abs_mul]
    have hLnonneg : 0 ≤ L := hL.le
    have habsbl : |(b : ℝ) * L| = (b : ℝ) * L :=
      abs_of_nonneg (mul_nonneg hbR hLnonneg)
    rw [habsbl]
    have hscaled := mul_le_mul_of_nonneg_left hbound hLnonneg
    have hfactor : L * ((b : ℝ) * (1 / ((r : ℝ) * (M : ℝ)))) ≤ L / (M : ℝ) := by
      have hbfrac : (b : ℝ) / (r : ℝ) ≤ 1 := by
        exact (div_le_iff₀ hrR).2 (by linarith)
      have hfrac := mul_le_mul_of_nonneg_right hbfrac (le_of_lt hM)
      field_simp [hrR.ne', hM.ne'] at hfrac ⊢
      nlinarith
    calc
      (b : ℝ) * L * |Q / L - (h : ℝ) / (r : ℝ)| =
          L * ((b : ℝ) * |Q / L - (h : ℝ) / (r : ℝ)|) := by ring
      _ ≤ L / (M : ℝ) := hscaled.trans hfactor
  have hrepr :
      (a : ℝ) * L + (b : ℝ) * Q =
        (j : ℝ) * L / (r : ℝ) + (b : ℝ) *
          (Q - ((h : ℝ) / (r : ℝ)) * L) := by
    rw [← hcongR]
    field_simp [hrR.ne']
    ring
  rw [hrepr]
  have hfloor₁' : (j : ℝ) * L / (r : ℝ) ≤ t - L / (M : ℝ) := by
    apply (div_le_iff₀ hrR).2
    have hmul := mul_le_mul_of_nonneg_right hfloor₁ hL.le
    field_simp [hL.ne'] at hmul ⊢
    nlinarith
  have hfloor₂' : t - L / (M : ℝ) - L / (r : ℝ) <
      (j : ℝ) * L / (r : ℝ) := by
    apply (lt_div_iff₀ hrR).2
    have hmul := mul_lt_mul_of_pos_right hfloor₂ hL
    field_simp [hL.ne'] at hmul ⊢
    nlinarith
  constructor
  · have hupper' : (b : ℝ) * (Q - ((h : ℝ) / (r : ℝ)) * L) ≤ L / (M : ℝ) :=
      (le_abs_self _).trans herror
    linarith [hfloor₁', hupper']
  · have hlower' : -(L / (M : ℝ)) ≤
      (b : ℝ) * (Q - ((h : ℝ) / (r : ℝ)) * L) := by
      exact neg_le_of_abs_le herror
    have hj : t - (j : ℝ) * L / (r : ℝ) <
        L / (M : ℝ) + L / (r : ℝ) := by
      linarith [hfloor₂']
    have hstep : t - ((j : ℝ) * L / (r : ℝ) +
        (b : ℝ) * (Q - ((h : ℝ) / (r : ℝ)) * L)) <
        (L / (M : ℝ) + L / (r : ℝ)) + L / (M : ℝ) := by
      linarith [hj, hlower']
    have hrewrite : (L / (M : ℝ) + L / (r : ℝ)) + L / (M : ℝ) =
        L / (r : ℝ) + 2 * L / (M : ℝ) := by ring
    rw [← hrewrite]
    exact hstep.le

/- The logarithmic gap is now converted into the actual natural-number product bounds used by
   `F`.  This keeps the analytic production of a suitable prime pair and floor index outside the
   lemma: once the finite congruence bridge and logarithmic gap are supplied, no further analytic
   argument is hidden in the exp/log conversion. -/
theorem power_product_mem_Icc_of_log_gap
    {p q n a b : ℕ} {L Q t C : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hn : 0 < n) (hC : 0 < C)
    (hLp : L = Real.log (p : ℝ)) (hQq : Q = Real.log (q : ℝ))
    (htn : t = Real.log (n : ℝ))
    (hgap : 0 ≤ t - ((a : ℝ) * L + (b : ℝ) * Q))
    (hgapC : t - ((a : ℝ) * L + (b : ℝ) * Q) ≤ Real.log C) :
    (n : ℝ) / C ≤ ((p ^ a * q ^ b : ℕ) : ℝ) ∧
      ((p ^ a * q ^ b : ℕ) : ℝ) ≤ (n : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hprodR : 0 < ((p ^ a * q ^ b : ℕ) : ℝ) := by positivity
  have hlogprod :
      Real.log ((p ^ a * q ^ b : ℕ) : ℝ) =
        (a : ℝ) * L + (b : ℝ) * Q := by
    rw [show ((p ^ a * q ^ b : ℕ) : ℝ) = (p : ℝ) ^ a * (q : ℝ) ^ b by norm_num]
    rw [Real.log_mul (pow_ne_zero a hpR.ne') (pow_ne_zero b hqR.ne'),
      Real.log_pow, Real.log_pow, hLp, hQq]
  have hupperLog : Real.log ((p ^ a * q ^ b : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    rw [hlogprod]
    linarith [hgap, htn]
  have hupperExp := Real.exp_le_exp.mpr hupperLog
  rw [Real.exp_log hprodR, Real.exp_log hnR] at hupperExp
  have hlowerLog : Real.log (n : ℝ) - Real.log C ≤
      Real.log ((p ^ a * q ^ b : ℕ) : ℝ) := by
    rw [hlogprod]
    linarith [hgapC, htn]
  have hlowerExp := Real.exp_le_exp.mpr hlowerLog
  rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hC, Real.exp_log hprodR] at hlowerExp
  exact ⟨hlowerExp, hupperExp⟩

end Erdos878

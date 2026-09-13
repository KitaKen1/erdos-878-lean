/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/

import Erdos878.UnionBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The bad-prime-pair family for Erdős Problem 878

This file records the exact finite combinatorial object used by the Track A proposal.  It does
not claim the analytic `o(1)` estimate: that estimate is the remaining Brun--Titchmarsh and
parameter-summation theorem.  The point of this module is to make the boundary precise and to
connect the filtered bad family to the already proved union-bound and Cartesian-weight lemmas.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos878

noncomputable section

/- A finite prime window in logarithmic coordinates.  The endpoint conventions match the report:
`exp(T^a) < p ≤ exp(T^b)`; the lower endpoint is implemented with a strict-prime filter below. -/
def primeWindow (T a b : ℝ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil (Real.exp (Real.rpow T a)))
    (Nat.floor (Real.exp (Real.rpow T b)))).filter
      (fun p => Nat.Prime p ∧ Real.exp (Real.rpow T a) < p)

theorem primeWindow_log_bounds
    {T a b : ℝ} {p : ℕ} (hp : p ∈ primeWindow T a b) (hpp : 0 < p) :
    Real.rpow T a < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ Real.rpow T b := by
  have hmem := Finset.mem_filter.mp hp
  have hIcc := Finset.mem_Icc.mp hmem.1
  have hlow : Real.exp (Real.rpow T a) < (p : ℝ) := by
    exact hmem.2.2
  have hhighNat : p ≤ Nat.floor (Real.exp (Real.rpow T b)) := hIcc.2
  have hhigh : (p : ℝ) ≤ Real.exp (Real.rpow T b) := by
    exact le_trans (by exact_mod_cast hhighNat) (Nat.floor_le (Real.exp_nonneg _))
  constructor
  · exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hpp)).2 hlow
  · exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp)).2 hhigh

def denominatorCutoff (p : ℕ) (rho : ℝ) : ℕ :=
  Nat.ceil (4 * Real.log (p : ℝ) / rho)

/- The ceiling contributes only one additive unit.  This pointwise estimate is what turns the
number of admissible denominators into a logarithmic factor after summing with `1/p`. -/
theorem denominatorCutoff_cast_lt_log
    {p : ℕ} {rho : ℝ} (hp : 1 < p) (hrho : 0 < rho) :
    (denominatorCutoff p rho : ℝ) <
      4 * Real.log (p : ℝ) / rho + 1 := by
  unfold denominatorCutoff
  apply Nat.ceil_lt_add_one
  exact (div_pos (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hp))) hrho).le

/- The rational-approximation relation from the report.  The explicit positivity condition on `r`
avoids relying on Lean's convention for division by zero. -/
def isBadApprox (rho : ℝ) (M p q r h : ℕ) : Prop :=
  1 ≤ r ∧ r < denominatorCutoff p rho ∧
    |Real.log (q : ℝ) / Real.log (p : ℝ) - (h : ℝ) / (r : ℝ)| ≤
      1 / ((r : ℝ) * (M : ℝ))

theorem isBadApprox_r_lt_of_log_upper
    {rho : ℝ} {M p q r h : ℕ} {U : ℝ}
    (hbad : isBadApprox rho M p q r h) (hrho : 0 < rho)
    (hp_log : Real.log (p : ℝ) ≤ U) :
    r < Nat.ceil (4 * U / rho) := by
  have hfour : 4 * Real.log (p : ℝ) ≤ 4 * U := by
    exact mul_le_mul_of_nonneg_left hp_log (by norm_num)
  have hratio : 4 * Real.log (p : ℝ) / rho ≤ 4 * U / rho := by
    exact div_le_div_of_nonneg_right hfour hrho.le
  have hceil : denominatorCutoff p rho ≤ Nat.ceil (4 * U / rho) := by
    unfold denominatorCutoff
    apply Nat.ceil_le.mpr
    exact hratio.trans (Nat.le_ceil _)
  exact lt_of_lt_of_le hbad.2.1 hceil

theorem isBadApprox_h_div_le
    {rho : ℝ} {M p q r h : ℕ}
    (hbad : isBadApprox rho M p q r h) :
    (h : ℝ) / (r : ℝ) ≤ Real.log (q : ℝ) / Real.log (p : ℝ) +
      1 / ((r : ℝ) * (M : ℝ)) := by
  have habs := hbad.2.2
  have hlow :
      - (1 / ((r : ℝ) * (M : ℝ))) ≤
        Real.log (q : ℝ) / Real.log (p : ℝ) - (h : ℝ) / (r : ℝ) :=
    (abs_le.mp habs).1
  linarith

theorem isBadApprox_h_le_of_log_bounds
    {rho : ℝ} {M p q r h : ℕ} {L V : ℝ}
    (hbad : isBadApprox rho M p q r h) (hp : 1 < p) (hq : 1 < q)
    (hM : 0 < M) (hL : 0 < L)
    (hLp : L ≤ Real.log (p : ℝ)) (hV : Real.log (q : ℝ) ≤ V) :
    (h : ℝ) ≤ (r : ℝ) * (V / L) + 1 / (M : ℝ) := by
  have hrnat : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hbad.1
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrnat
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hplog : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)
  have hqlog_nonneg : 0 ≤ Real.log (q : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hVnonneg : 0 ≤ V := hqlog_nonneg.trans hV
  have hinv : (Real.log (p : ℝ))⁻¹ ≤ L⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hL hLp
  have hratio : Real.log (q : ℝ) / Real.log (p : ℝ) ≤ V / L := by
    calc
      Real.log (q : ℝ) / Real.log (p : ℝ) =
          Real.log (q : ℝ) * (Real.log (p : ℝ))⁻¹ := by ring
      _ ≤ V * (Real.log (p : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hV (inv_nonneg.mpr hplog.le)
      _ ≤ V * L⁻¹ := mul_le_mul_of_nonneg_left hinv hVnonneg
      _ = V / L := by ring
  have hdiv := isBadApprox_h_div_le hbad
  have hbase : (h : ℝ) ≤
      (Real.log (q : ℝ) / Real.log (p : ℝ) +
        1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) :=
    (div_le_iff₀ hrpos).mp hdiv
  have hadd := add_le_add_right hratio (1 / ((r : ℝ) * (M : ℝ)))
  have hmul := mul_le_mul_of_nonneg_right hadd hrpos.le
  have hmul' :
      (Real.log (q : ℝ) / Real.log (p : ℝ) +
        1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) ≤
      (V / L + 1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) := by
    simpa [add_comm, add_left_comm, add_assoc] using hmul
  calc
    (h : ℝ) ≤
        (Real.log (q : ℝ) / Real.log (p : ℝ) +
          1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) := hbase
    _ ≤ (V / L + 1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) := hmul'
    _ = (r : ℝ) * (V / L) + 1 / (M : ℝ) := by
      field_simp [hL.ne', hrpos.ne', hmpos.ne']
      

theorem isBadApprox_h_lt_of_log_bounds
    {rho : ℝ} {M p q r h : ℕ} {L V : ℝ} {H : ℕ}
    (hbad : isBadApprox rho M p q r h) (hp : 1 < p) (hq : 1 < q)
    (hM : 0 < M) (hL : 0 < L)
    (hLp : L ≤ Real.log (p : ℝ)) (hV : Real.log (q : ℝ) ≤ V)
    (hH : (r : ℝ) * (V / L) + 1 / (M : ℝ) < (H : ℝ)) :
    h < H := by
  have hh := isBadApprox_h_le_of_log_bounds hbad hp hq hM hL hLp hV
  have hh' : (h : ℝ) < (H : ℝ) := lt_of_le_of_lt hh hH
  exact_mod_cast hh'

/- The lower endpoint of the q-window also forces the numerator h to be large.  This is the
missing decay input when the Brun majorant is summed over h: small h cannot occur for a q whose
logarithm lies in the complementary upper window. -/
theorem isBadApprox_h_lower_of_prime_windows
    {T α β γ δ rho : ℝ} {M p q r h : ℕ}
    (hp : p ∈ primeWindow T α β)
    (hq : q ∈ primeWindow T γ δ)
    (hbad : isBadApprox rho M p q r h)
    (hT : 1 ≤ T) (hM : 0 < M) :
    (r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ) < (h : ℝ) := by
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hqPrime : Nat.Prime q := (Finset.mem_filter.mp hq).2.1
  have hpPos : 0 < p := hpPrime.pos
  have hqPos : 0 < q := hqPrime.pos
  have hplogPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hqlogLower : Real.rpow T γ < Real.log (q : ℝ) :=
    (primeWindow_log_bounds hq hqPos).1
  have hplogUpper : Real.log (p : ℝ) ≤ Real.rpow T β :=
    (primeWindow_log_bounds hp hpPos).2
  have hβpowPos : 0 < Real.rpow T β := Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one hT) _
  have hγpowNonneg : 0 ≤ Real.rpow T γ :=
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) _).le
  have hratioMul :
      (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) ≤ Real.rpow T γ := by
    calc
      (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) =
          (Real.rpow T γ * Real.log (p : ℝ)) / Real.rpow T β := by ring
      _ ≤ (Real.rpow T γ * Real.rpow T β) / Real.rpow T β := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hplogUpper hγpowNonneg) hβpowPos.le
      _ = Real.rpow T γ := by field_simp [hβpowPos.ne']
  have hratioLower :
      Real.rpow T γ / Real.rpow T β < Real.log (q : ℝ) / Real.log (p : ℝ) := by
    apply (lt_div_iff₀ hplogPos).2
    exact hratioMul.trans_lt hqlogLower
  have hrnat : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hbad.1
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrnat
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdiff :
      Real.log (q : ℝ) / Real.log (p : ℝ) - (h : ℝ) / (r : ℝ) ≤
        1 / ((r : ℝ) * (M : ℝ)) :=
    (abs_le.mp hbad.2.2).2
  have hdiv :
      Real.log (q : ℝ) / Real.log (p : ℝ) - 1 / ((r : ℝ) * (M : ℝ)) ≤
        (h : ℝ) / (r : ℝ) := by
    linarith
  have hbase :
      (Real.log (q : ℝ) / Real.log (p : ℝ) -
        1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) ≤ (h : ℝ) := by
    exact (le_div_iff₀ hrpos).mp hdiv
  have hstrict :
      (r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ) <
        (Real.log (q : ℝ) / Real.log (p : ℝ) -
          1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) := by
    calc
      (r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ) <
          (r : ℝ) * (Real.log (q : ℝ) / Real.log (p : ℝ)) - 1 / (M : ℝ) := by
        exact sub_lt_sub_right (mul_lt_mul_of_pos_left hratioLower hrpos) _
      _ = (Real.log (q : ℝ) / Real.log (p : ℝ) -
          1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) := by
        field_simp [hrpos.ne', hmpos.ne']
  exact hstrict.trans_le hbase

/- A natural-number version of the preceding lower bound.  `Nat.ceil` is used so that this
threshold can index the finite h-sum directly. -/
noncomputable def primeWindowHLower (T β γ : ℝ) (M r : ℕ) : ℕ :=
  Nat.ceil ((r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ))

theorem primeWindowHLower_le_of_badApprox
    {T α β γ δ rho : ℝ} {M p q r h : ℕ}
    (hp : p ∈ primeWindow T α β)
    (hq : q ∈ primeWindow T γ δ)
    (hbad : isBadApprox rho M p q r h)
    (hT : 1 ≤ T) (hM : 0 < M) :
    primeWindowHLower T β γ M r ≤ h := by
  apply Nat.ceil_le.mpr
  exact_mod_cast le_of_lt
    (isBadApprox_h_lower_of_prime_windows hp hq hbad hT hM)

theorem isBadApprox_log_q_mem
    {rho : ℝ} {M p q r h : ℕ}
    (hbad : isBadApprox rho M p q r h) (hp : 1 < p) :
    ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) -
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) +
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) := by
  have hplog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp
  have habs := hbad.2.2
  have hmul_lo := mul_le_mul_of_nonneg_right (abs_le.mp habs).1 hplog.le
  have hmul_hi := mul_le_mul_of_nonneg_right (abs_le.mp habs).2 hplog.le
  have hrewrite :
      Real.log (p : ℝ) *
          (Real.log (q : ℝ) / Real.log (p : ℝ) - (h : ℝ) / (r : ℝ)) =
        Real.log (q : ℝ) - ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    field_simp [hplog.ne']
  have hrewrite' :
      (Real.log (q : ℝ) / Real.log (p : ℝ) - (h : ℝ) / (r : ℝ)) *
          Real.log (p : ℝ) =
        Real.log (q : ℝ) - ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    rw [mul_comm]
    exact hrewrite
  rw [hrewrite'] at hmul_lo hmul_hi
  have hfrac : (1 / ((r : ℝ) * (M : ℝ))) * Real.log (p : ℝ) =
      Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) := by ring
  have hfrac_neg : -(1 / ((r : ℝ) * (M : ℝ))) * Real.log (p : ℝ) =
      -Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) := by
    calc
      -(1 / ((r : ℝ) * (M : ℝ))) * Real.log (p : ℝ) =
          -((1 / ((r : ℝ) * (M : ℝ))) * Real.log (p : ℝ)) := by ring
      _ = -Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) := by rw [hfrac]; ring
  rw [hfrac_neg] at hmul_lo
  rw [hfrac] at hmul_hi
  constructor <;> linarith

theorem isBadApprox_q_mem_exp_interval
    {rho : ℝ} {M p q r h : ℕ}
    (hbad : isBadApprox rho M p q r h) (hp : 1 < p) (hq : 1 < q) :
    Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) -
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) +
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hlog := isBadApprox_log_q_mem hbad hp
  constructor
  · have he := Real.exp_le_exp.mpr hlog.1
    simpa [Real.exp_log hqpos] using he
  · have he := Real.exp_le_exp.mpr hlog.2
    simpa [Real.exp_log hqpos] using he

theorem isBadApprox_q_mem_nat_interval
    {rho : ℝ} {M p q r h : ℕ}
    (hbad : isBadApprox rho M p q r h) (hp : 1 < p) (hq : 1 < q) :
    q ∈ Finset.Icc
      (Nat.ceil (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) -
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)))))
      (Nat.floor (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) +
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))))) := by
  have hqexp := isBadApprox_q_mem_exp_interval hbad hp hq
  apply Finset.mem_Icc.mpr
  constructor
  · apply Nat.ceil_le.mpr
    exact hqexp.1
  · exact Nat.le_floor hqexp.2

/-- Positivity and relative-width conditions for the explicit Brun--Titchmarsh q-window.  The
parameter-summation proof can therefore discharge these side conditions from the natural bounds
`1 < M`, `0 < r`, and `0 < h`, rather than carrying an informal positivity convention. -/
theorem badPairQWindow_hypotheses_of_prime_window
    {T α β : ℝ} {M r h p : ℕ}
    (hp : p ∈ primeWindow T α β) (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    0 < Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) ∧
      Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) <
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hpOne : 1 < p := hpPrime.one_lt
  have hlog : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hpOne)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hden : 0 < (r : ℝ) * (M : ℝ) := mul_pos hrpos hmpos
  constructor
  · exact div_pos hlog hden
  · have hMreal : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hInv : (1 : ℝ) / (M : ℝ) < 1 := by
      have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hMreal
      simpa using h
    have hhOne : 1 ≤ h := by omega
    have hhreal : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhOne
    have hratio : (1 : ℝ) / (M : ℝ) < (h : ℝ) := hInv.trans_le hhreal
    have hmul : ((1 : ℝ) / (M : ℝ)) * Real.log (p : ℝ) <
        (h : ℝ) * Real.log (p : ℝ) :=
      mul_lt_mul_of_pos_right hratio hlog
    have hdiv : (((1 : ℝ) / (M : ℝ)) * Real.log (p : ℝ)) / (r : ℝ) <
        ((h : ℝ) * Real.log (p : ℝ)) / (r : ℝ) :=
      (div_lt_div_iff_of_pos_right hrpos).2 hmul
    calc
      Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) =
          (((1 : ℝ) / (M : ℝ)) * Real.log (p : ℝ)) / (r : ℝ) := by
        field_simp [hrpos.ne', hmpos.ne']
      _ < ((h : ℝ) * Real.log (p : ℝ)) / (r : ℝ) := hdiv
      _ = ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by ring

def badPairs (T α β γ δ rho : ℝ) (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeWindow T α β).product (primeWindow T γ δ)).filter
    (fun pq ↦ ∃ r h : ℕ, isBadApprox rho M pq.1 pq.2 r h)

/- The source proof chooses the approximation parameter as a function of the main scale (in the
report, `M(T) = floor (T^(1-δ) / 8)`).  This wrapper keeps the finite definition above reusable
while exposing that dependence explicitly for the final asymptotic statement. -/
def badPairsWithScale
    (T α β γ δ rho : ℝ) (M : ℝ → ℕ) : Finset (ℕ × ℕ) :=
  badPairs T α β γ δ rho (M T)

/-- The scale selected in the source proof of the first subquestion.  The floor is taken in
`ℕ`; no positivity claim is built into the definition, so such side conditions remain explicit
in the analytic theorem that uses it. -/
def reportApproximationScale (T delta : ℝ) : ℕ :=
  Nat.floor (Real.rpow T (1 - delta) / 8)

/- A finite arithmetic gate for the report scale.  The analytic proof still has to show that
the hypothesis eventually holds (for example from `delta < 1`); this lemma only records the
floor calculation without smuggling that asymptotic step into the definition. -/
theorem reportApproximationScale_gt_one_of_rpow
    {T delta : ℝ} (hpow : 16 ≤ Real.rpow T (1 - delta)) :
    1 < reportApproximationScale T delta := by
  unfold reportApproximationScale
  have hdiv : (2 : ℝ) ≤ Real.rpow T (1 - delta) / 8 := by
    linarith
  have hfloor : 2 ≤ Nat.floor (Real.rpow T (1 - delta) / 8) :=
    Nat.le_floor hdiv
  exact lt_of_lt_of_le (by norm_num) hfloor

theorem eventually_reportApproximationScale_gt_one
    {delta : ℝ} (hdelta : delta < 1) :
    ∀ᶠ T : ℝ in atTop, 1 < reportApproximationScale T delta := by
  have hpow : Tendsto (fun T : ℝ => T ^ (1 - delta)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hdelta)
  filter_upwards [hpow.eventually (eventually_ge_atTop (16 : ℝ))] with T hT
  exact reportApproximationScale_gt_one_of_rpow hT

/-- The report scale is eventually large enough for the elementary width decomposition. -/
theorem eventually_reportApproximationScale_ge_four
    {delta : ℝ} (hdelta : delta < 1) :
    ∀ᶠ T : ℝ in atTop, 4 ≤ (reportApproximationScale T delta : ℝ) := by
  have hpow : Tendsto (fun T : ℝ => T ^ (1 - delta)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hdelta)
  filter_upwards [hpow.eventually (eventually_ge_atTop (32 : ℝ))] with T hT
  unfold reportApproximationScale
  have hdiv : (4 : ℝ) ≤ Real.rpow T (1 - delta) / 8 := by
    have hdiv' := (div_le_div_iff_of_pos_right
      (by norm_num : (0 : ℝ) < 8)).2 hT
    norm_num at hdiv'
    exact hdiv'
  have hfloor : 4 ≤ Nat.floor (Real.rpow T (1 - delta) / 8) :=
    Nat.le_floor hdiv
  exact_mod_cast hfloor

/-- If `beta + delta < 1` (and `beta ≥ 0`), the report's floor scale eventually dominates
`2 T^beta`.  The extra factor `2` is convenient for the width condition in the Brun majorant. -/
theorem eventually_two_rpow_le_reportApproximationScale
    {beta delta : ℝ} (hbeta : 0 ≤ beta) (hbetadelta : beta + delta < 1) :
    ∀ᶠ T : ℝ in atTop,
      2 * Real.rpow T beta ≤ (reportApproximationScale T delta : ℝ) := by
  let e : ℝ := 1 - delta - beta
  have he : 0 < e := by
    dsimp [e]
    linarith
  have hpow : Tendsto (fun T : ℝ => T ^ e) atTop atTop := tendsto_rpow_atTop he
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hpow.eventually (eventually_ge_atTop (24 : ℝ))] with T hT hTe
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hβpow : 1 ≤ Real.rpow T beta := Real.one_le_rpow hT hbeta
  have hβnonneg : 0 ≤ Real.rpow T beta := (Real.rpow_pos_of_pos hTpos _).le
  have hprod : 24 * Real.rpow T beta ≤ Real.rpow T (1 - delta) := by
    calc
      24 * Real.rpow T beta ≤ Real.rpow T e * Real.rpow T beta :=
        mul_le_mul_of_nonneg_right hTe hβnonneg
      _ = Real.rpow T (e + beta) := by
        exact (Real.rpow_add hTpos e beta).symm
      _ = Real.rpow T (1 - delta) := by
        congr 1
        dsimp [e]
        ring
  have hscale_floor :
      Real.rpow T (1 - delta) / 8 - 1 <
        (reportApproximationScale T delta : ℝ) := by
    unfold reportApproximationScale
    exact Nat.sub_one_lt_floor _
  have hthree : 3 * Real.rpow T beta ≤ Real.rpow T (1 - delta) / 8 := by
    nlinarith [hprod]
  have htwo : 2 * Real.rpow T beta ≤
      Real.rpow T (1 - delta) / 8 - 1 := by
    nlinarith [hthree, hβpow]
  exact le_of_lt (lt_of_le_of_lt htwo hscale_floor)

/-- The preceding scale estimate supplies the width hypothesis for every positive denominator in
the first prime window.  This is the exact side condition needed before applying the decomposed
Brun majorant to the source-scale parameter sum. -/
theorem eventually_primeWindow_width_of_reportApproximationScale
    {α beta delta : ℝ} (hbeta : 0 ≤ beta) (hbetadelta : beta + delta < 1) :
    ∀ᶠ T : ℝ in atTop,
      ∀ p ∈ primeWindow T α beta, ∀ r : ℕ, 0 < r →
        2 * Real.log (p : ℝ) ≤ (r : ℝ) *
          (reportApproximationScale T delta : ℝ) := by
  filter_upwards [eventually_two_rpow_le_reportApproximationScale hbeta hbetadelta]
    with T hscale p hp r hr
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hlogupper : Real.log (p : ℝ) ≤ Real.rpow T beta :=
    (primeWindow_log_bounds hp hpPrime.pos).2
  have hlogdouble : 2 * Real.log (p : ℝ) ≤ 2 * Real.rpow T beta := by
    exact mul_le_mul_of_nonneg_left hlogupper (by norm_num)
  have hMnonneg : 0 ≤ (reportApproximationScale T delta : ℝ) := by positivity
  have hrone : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (show 1 ≤ r by omega)
  have hRM : (reportApproximationScale T delta : ℝ) ≤
      (r : ℝ) * (reportApproximationScale T delta : ℝ) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hrone hMnonneg
  linarith

def badPairsAtReportScale
    (T α β γ δ rho : ℝ) : Finset (ℕ × ℕ) :=
  badPairsWithScale T α β γ δ rho (fun S ↦ reportApproximationScale S δ)

/-- A global `r` range obtained from the upper endpoint of the first prime window. -/
def reportRBound (T beta rho : ℝ) : ℕ :=
  Nat.ceil (4 * Real.rpow T beta / rho)

theorem reportRBound_cast_lt
    {T beta rho : ℝ} (harg : 0 ≤ 4 * Real.rpow T beta / rho) :
    (reportRBound T beta rho : ℝ) < 4 * Real.rpow T beta / rho + 1 := by
  unfold reportRBound
  exact Nat.ceil_lt_add_one harg

theorem report_endpoint_ratio_pos {T α δ : ℝ} (hT : 0 < T) :
    0 < Real.rpow T δ / Real.rpow T α := by
  exact div_pos (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hT _)

/-- A uniform numerator range obtained by taking one more than the ceiling of the endpoint bound.
The positivity of the endpoint ratio is kept as an explicit hypothesis in the companion lemma. -/
def reportHBound (T α β δ rho : ℝ) (M : ℕ) : ℕ :=
  Nat.ceil ((reportRBound T β rho : ℝ) *
      (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ)) + 1

theorem reportHBound_cast_lt
    {T α β δ rho : ℝ} {M : ℕ}
    (harg : 0 ≤ (reportRBound T β rho : ℝ) *
      (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ)) :
    (reportHBound T α β δ rho M : ℝ) <
      (reportRBound T β rho : ℝ) * (Real.rpow T δ / Real.rpow T α) +
        1 / (M : ℝ) + 2 := by
  unfold reportHBound
  have hceil := Nat.ceil_lt_add_one harg
  norm_num at hceil ⊢
  linarith

def reportHAtReportScale (T α β δ rho : ℝ) : ℕ :=
  reportHBound T α β δ rho (reportApproximationScale T δ)

theorem reportHBound_condition
    {T α β δ rho : ℝ} {M r : ℕ}
    (hr : r < reportRBound T β rho)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) <
      (reportHBound T α β δ rho M : ℝ) := by
  have hrReal : (r : ℝ) < (reportRBound T β rho : ℝ) := by
    exact_mod_cast hr
  have hmul : (r : ℝ) * (Real.rpow T δ / Real.rpow T α) <
      (reportRBound T β rho : ℝ) * (Real.rpow T δ / Real.rpow T α) :=
    mul_lt_mul_of_pos_right hrReal hpositive
  have hsum : (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) <
      (reportRBound T β rho : ℝ) * (Real.rpow T δ / Real.rpow T α) +
        1 / (M : ℝ) := by
    linarith
  have hceil :
      (reportRBound T β rho : ℝ) * (Real.rpow T δ / Real.rpow T α) +
          1 / (M : ℝ) ≤
        (Nat.ceil ((reportRBound T β rho : ℝ) *
          (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ)) : ℝ) := by
    exact Nat.le_ceil _
  calc
    (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) <
        (reportRBound T β rho : ℝ) * (Real.rpow T δ / Real.rpow T α) +
          1 / (M : ℝ) := hsum
    _ ≤ (Nat.ceil ((reportRBound T β rho : ℝ) *
          (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ)) : ℝ) := hceil
    _ < (Nat.ceil ((reportRBound T β rho : ℝ) *
          (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ)) : ℝ) + 1 := by norm_num
    _ = (reportHBound T α β δ rho M : ℝ) := by
      simp [reportHBound]

theorem isBadApprox_r_lt_reportRBound
    {T α β rho : ℝ} {M p q r h : ℕ}
    (hp : p ∈ primeWindow T α β)
    (hbad : isBadApprox rho M p q r h)
    (hrho : 0 < rho) :
    r < reportRBound T β rho := by
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hpPos : 0 < p := hpPrime.pos
  have hlogUpper : Real.log (p : ℝ) ≤ Real.rpow T β :=
    (primeWindow_log_bounds hp hpPos).2
  simpa [reportRBound] using isBadApprox_r_lt_of_log_upper hbad hrho hlogUpper

theorem isBadApprox_h_lt_of_prime_windows
    {T α β γ δ rho : ℝ} {M p q r h H : ℕ}
    (hp : p ∈ primeWindow T α β)
    (hq : q ∈ primeWindow T γ δ)
    (hbad : isBadApprox rho M p q r h)
    (hM : 0 < M) (hL : 0 < Real.rpow T α)
    (hH : (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) < (H : ℝ)) :
    h < H := by
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hqPrime : Nat.Prime q := (Finset.mem_filter.mp hq).2.1
  have hpPos : 0 < p := hpPrime.pos
  have hqPos : 0 < q := hqPrime.pos
  have hLp : Real.rpow T α ≤ Real.log (p : ℝ) :=
    le_of_lt (primeWindow_log_bounds hp hpPos).1
  have hV : Real.log (q : ℝ) ≤ Real.rpow T δ :=
    (primeWindow_log_bounds hq hqPos).2
  exact isBadApprox_h_lt_of_log_bounds hbad hpPrime.one_lt hqPrime.one_lt hM hL hLp hV hH

/-- One rational-approximation block of the bad-pair family. -/
def badPairBlock (T α β γ δ rho : ℝ) (M r h : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeWindow T α β).product (primeWindow T γ δ)).filter
    (fun pq ↦ isBadApprox rho M pq.1 pq.2 r h)

theorem badPairBlock_empty_below_primeWindowHLower
    {T α β γ δ rho : ℝ} {M r h : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M)
    (hh : h < primeWindowHLower T β γ M r) :
    badPairBlock T α β γ δ rho M r h = ∅ := by
  classical
  ext pq
  constructor
  · intro hpq
    have hmem := Finset.mem_filter.mp hpq
    have hprod := Finset.mem_product.mp hmem.1
    have hpqLower := primeWindowHLower_le_of_badApprox
      hprod.1 hprod.2 hmem.2 hT hM
    exfalso
    exact (Nat.not_le_of_lt hh) hpqLower
  · intro hpq
    simp at hpq

theorem badPairBlock_zero_r_empty
    (T α β γ δ rho : ℝ) (M h : ℕ) :
    badPairBlock T α β γ δ rho M 0 h = ∅ := by
  classical
  ext pq
  simp [badPairBlock, isBadApprox]

/-- The zero-numerator block needs separate treatment because its logarithmic centre is zero.  If
every pair of windows has log-ratio larger than the approximation error, that block is empty. -/
theorem badPairBlock_h_zero_empty_of_ratio_bound
    (T α β γ δ rho : ℝ) (M r : ℕ)
    (hlogratio : ∀ ⦃p q : ℕ⦄,
      p ∈ primeWindow T α β → q ∈ primeWindow T γ δ →
        1 / ((r : ℝ) * (M : ℝ)) <
          Real.log (q : ℝ) / Real.log (p : ℝ)) :
    badPairBlock T α β γ δ rho M r 0 = ∅ := by
  classical
  ext pq
  constructor
  · intro hpq
    have hmem := Finset.mem_filter.mp hpq
    have hprod := Finset.mem_product.mp hmem.1
    have hbad : isBadApprox rho M pq.1 pq.2 r 0 := hmem.2
    have hupper : Real.log (pq.2 : ℝ) / Real.log (pq.1 : ℝ) ≤
        1 / ((r : ℝ) * (M : ℝ)) := by
      have habs := (abs_le.mp hbad.2.2).2
      simpa using habs
    exfalso
    exact (not_lt_of_ge hupper) (hlogratio hprod.1 hprod.2)
  · intro hpq
    simp at hpq

/- Ordered complementary windows have a strictly positive logarithmic separation.  This is the
   reusable form of the estimate used below for the zero-numerator block. -/
theorem primeWindow_log_ratio_gt_one
    {T α β γ δ : ℝ} {p q : ℕ}
    (hp : p ∈ primeWindow T α β)
    (hq : q ∈ primeWindow T γ δ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) :
    1 < Real.log (q : ℝ) / Real.log (p : ℝ) := by
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hqPrime : Nat.Prime q := (Finset.mem_filter.mp hq).2.1
  have hpPos : 0 < p := hpPrime.pos
  have hqPos : 0 < q := hqPrime.pos
  have hplogPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hpUpper : Real.log (p : ℝ) ≤ Real.rpow T β :=
    (primeWindow_log_bounds hp hpPos).2
  have hqLower : Real.rpow T γ < Real.log (q : ℝ) :=
    (primeWindow_log_bounds hq hqPos).1
  have hpow : Real.rpow T β ≤ Real.rpow T γ :=
    Real.rpow_le_rpow_of_exponent_le hT hβγ
  have hlogOrder : Real.log (p : ℝ) < Real.log (q : ℝ) := by
    linarith
  apply (lt_div_iff₀ hplogPos).2
  simpa using hlogOrder

/-- In the ordered complementary windows from the source proof, `h=0` is automatically
impossible once `T ≥ 1` and `M > 1`: every q has larger logarithm than every p, whereas the
zero-centre error is strictly less than one. -/
theorem badPairBlock_h_zero_empty_of_ordered_windows
    (T α β γ δ rho : ℝ) (M r : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hM : 1 < M) (hr : 0 < r) :
    badPairBlock T α β γ δ rho M r 0 = ∅ := by
  apply badPairBlock_h_zero_empty_of_ratio_bound T α β γ δ rho M r
  intro p q hp hq
  have hratioOne : (1 : ℝ) < Real.log (q : ℝ) / Real.log (p : ℝ) :=
    primeWindow_log_ratio_gt_one hp hq hT hβγ
  have hrOne : 1 ≤ r := by omega
  have hrReal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrOne
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hMReal : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdenStep : (r : ℝ) < (r : ℝ) * (M : ℝ) := by
    have h := mul_lt_mul_of_pos_left hMReal hrPos
    simpa using h
  have hden : (1 : ℝ) < (r : ℝ) * (M : ℝ) := hrReal.trans_lt hdenStep
  have herr : 1 / ((r : ℝ) * (M : ℝ)) < (1 : ℝ) := by
    have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hden
    simpa using h
  exact herr.trans hratioOne

/-- The finite q-window forced by one fixed rational-approximation block.  It keeps the original
second prime window and intersects it with the exponentiated logarithmic interval coming from
`isBadApprox_q_mem_nat_interval`. -/
def badPairQWindow
    (T _α _β γ δ _rho : ℝ) (M r h p : ℕ) : Finset ℕ := by
  classical
  exact (primeWindow T γ δ).filter (fun q ↦
    q ∈ Finset.Icc
      (Nat.ceil (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) -
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)))))
      (Nat.floor (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) +
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))))))

/-- Union of the q-windows over the p's in the first prime window. -/
def badPairBlockQWindows
    (T α β γ δ rho : ℝ) (M r h : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (primeWindow T α β).biUnion (fun p ↦
    (badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q)))

theorem badPairBlock_subset_qWindows
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    badPairBlock T α β γ δ rho M r h ⊆
      badPairBlockQWindows T α β γ δ rho M r h := by
  classical
  intro pq hpq
  rcases pq with ⟨p, q⟩
  have hpq_mem := Finset.mem_filter.mp hpq
  have hpProd := Finset.mem_product.mp hpq_mem.1
  have hpPrime := (Finset.mem_filter.mp hpProd.1).2.1
  have hqPrime := (Finset.mem_filter.mp hpProd.2).2.1
  have hqInterval := isBadApprox_q_mem_nat_interval hpq_mem.2 hpPrime.one_lt hqPrime.one_lt
  have hqWindow : q ∈ badPairQWindow T α β γ δ rho M r h p := by
    apply Finset.mem_filter.mpr
    exact ⟨hpProd.2, hqInterval⟩
  refine Finset.mem_biUnion.mpr ⟨p, hpProd.1, ?_⟩
  exact Finset.mem_image.mpr ⟨q, hqWindow, rfl⟩

theorem badPairBlockWeight_le_qWindows
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      pairReciprocalWeight (badPairBlockQWindows T α β γ δ rho M r h) :=
  pairReciprocalWeight_mono (badPairBlock_subset_qWindows T α β γ δ rho M r h)

theorem pairReciprocalWeight_image_fixed_left
    (p : ℕ) (Q : Finset ℕ) :
    pairReciprocalWeight (Q.image (fun q ↦ (p, q))) =
      ((p : ℝ)⁻¹) * (∑ q ∈ Q, ((q : ℝ)⁻¹)) := by
  classical
  unfold pairReciprocalWeight
  rw [Finset.sum_image]
  · simp only [Nat.cast_mul, mul_inv]
    rw [Finset.mul_sum]
  · intro a ha b hb hab
    simpa using congrArg Prod.snd hab

theorem pairReciprocalWeight_qWindows_le
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    pairReciprocalWeight (badPairBlockQWindows T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) := by
  classical
  unfold badPairBlockQWindows
  calc
    pairReciprocalWeight
        ((primeWindow T α β).biUnion (fun p ↦
          (badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q)))) ≤
        ∑ p ∈ primeWindow T α β,
          pairReciprocalWeight
            ((badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q))) :=
      pairReciprocalWeight_biUnion_le _ _
    _ = ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) *
            (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact pairReciprocalWeight_image_fixed_left p
        (badPairQWindow T α β γ δ rho M r h p)

/-- A finite union of rational-approximation blocks.  The bounds `R` and `H` are supplied by the
analytic part of the argument; the finite bookkeeping below is independent of how they are
chosen. -/
def badPairBlocks (T α β γ δ rho : ℝ) (M R H : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range R).biUnion (fun r ↦
    (Finset.range H).biUnion (fun h ↦ badPairBlock T α β γ δ rho M r h))

/- A sharper finite cover keeps the denominator range attached to the first prime.  This is the
form needed for the `R p = ceil (4 log p / rho)` summation: replacing it by a single global
`R` loses the logarithmic weight which is later paired with `1/p`. -/
def badPairBlockAtPrime
    (T α β γ δ rho : ℝ) (M p r h : ℕ) : Finset (ℕ × ℕ) :=
  (badPairBlock T α β γ δ rho M r h).filter (fun pq ↦ pq.1 = p)

/- A single `p`-slice of a rational-approximation block is controlled directly by its q-window.
This avoids first taking a union over all `p`, which is precisely what permits the
`p`-dependent denominator cutoff to survive the later summation. -/
theorem badPairBlockAtPrime_subset_qWindow_image
    (T α β γ δ rho : ℝ) (M p r h : ℕ)
    :
    badPairBlockAtPrime T α β γ δ rho M p r h ⊆
      (badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q)) := by
  classical
  intro pq hpq
  rcases pq with ⟨p', q⟩
  have hfilter := Finset.mem_filter.mp hpq
  have hEq : p' = p := hfilter.2
  subst p'
  have hblock := hfilter.1
  have hblockFilter := Finset.mem_filter.mp hblock
  have hprod := Finset.mem_product.mp hblockFilter.1
  have hpPrime := (Finset.mem_filter.mp hprod.1).2.1
  have hqPrime := (Finset.mem_filter.mp hprod.2).2.1
  have hqInterval := isBadApprox_q_mem_nat_interval hblockFilter.2
    hpPrime.one_lt hqPrime.one_lt
  apply Finset.mem_image.mpr
  exact ⟨q, Finset.mem_filter.mpr ⟨hprod.2, hqInterval⟩, rfl⟩

def badPairBlocksPrimeDependent
    (T α β γ δ rho : ℝ) (M : ℕ) (R : ℕ → ℕ) (H : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (primeWindow T α β).biUnion (fun p ↦
    (Finset.range (R p)).biUnion (fun r ↦
      (Finset.range H).biUnion (fun h ↦
        badPairBlockAtPrime T α β γ δ rho M p r h)))

theorem badPairs_subset_badPairBlocksPrimeDependent
    (T α β γ δ rho : ℝ) (M : ℕ) (R : ℕ → ℕ) (H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (hR : ∀ ⦃p : ℕ⦄, p ∈ primeWindow T α β →
      denominatorCutoff p rho ≤ R p) :
    badPairs T α β γ δ rho M ⊆
      badPairBlocksPrimeDependent T α β γ δ rho M R H := by
  classical
  intro pq hpq
  rcases pq with ⟨p, q⟩
  have hpqMem := Finset.mem_filter.mp hpq
  have hpProd := hpqMem.1
  have hpWin := (Finset.mem_product.mp hpProd).1
  obtain ⟨r, h, hhH, hbad⟩ := hcover (pq := (p, q)) hpq
  have hrR : r < R p :=
    lt_of_lt_of_le hbad.2.1 (hR hpWin)
  refine Finset.mem_biUnion.mpr ⟨p, hpWin, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hrR, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_range.mpr hhH, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_filter.mpr ⟨hpProd, hbad⟩, rfl⟩

/- Weight version of the preceding cover.  The three finite unions are kept in the same order as
the definitions, so a later analytic bound may sum `p` first and retain `R p` explicitly. -/
theorem badPairWeight_le_primeDependent_block_sum
    (T α β γ δ rho : ℝ) (M : ℕ) (R : ℕ → ℕ) (H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (hR : ∀ ⦃p : ℕ⦄, p ∈ primeWindow T α β →
      denominatorCutoff p rho ≤ R p) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (R p),
          ∑ h ∈ Finset.range H,
            pairReciprocalWeight
              (badPairBlockAtPrime T α β γ δ rho M p r h) := by
  classical
  have hsubset := badPairs_subset_badPairBlocksPrimeDependent
    T α β γ δ rho M R H hcover hR
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        pairReciprocalWeight
          (badPairBlocksPrimeDependent T α β γ δ rho M R H) :=
      pairReciprocalWeight_mono hsubset
    _ ≤ ∑ p ∈ primeWindow T α β,
        pairReciprocalWeight
          ((Finset.range (R p)).biUnion (fun r ↦
            (Finset.range H).biUnion (fun h ↦
              badPairBlockAtPrime T α β γ δ rho M p r h))) := by
      unfold badPairBlocksPrimeDependent
      exact pairReciprocalWeight_biUnion_le _ _
    _ ≤ ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (R p),
          pairReciprocalWeight
            ((Finset.range H).biUnion (fun h ↦
              badPairBlockAtPrime T α β γ δ rho M p r h)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact pairReciprocalWeight_biUnion_le _ _
    _ ≤ ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (R p),
          ∑ h ∈ Finset.range H,
            pairReciprocalWeight
              (badPairBlockAtPrime T α β γ δ rho M p r h) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      exact pairReciprocalWeight_biUnion_le _ _

/-- A canonical witness chosen from the existential predicate in `badPairs`.  These choices are
used only to turn the a priori existential family into a finite union; the analytic estimate still
has to bound the resulting blocks uniformly. -/
noncomputable def badWitnessR
    (T α β γ δ rho : ℝ) (M : ℕ) (pq : ℕ × ℕ) : ℕ := by
  classical
  exact if hpq : pq ∈ badPairs T α β γ δ rho M then
    Classical.choose (Finset.mem_filter.mp hpq).2
  else 0

noncomputable def badWitnessH
    (T α β γ δ rho : ℝ) (M : ℕ) (pq : ℕ × ℕ) : ℕ := by
  classical
  exact if hpq : pq ∈ badPairs T α β γ δ rho M then
    Classical.choose (Classical.choose_spec (Finset.mem_filter.mp hpq).2)
  else 0

theorem badWitness_spec
    (T α β γ δ rho : ℝ) (M : ℕ) {pq : ℕ × ℕ}
    (hpq : pq ∈ badPairs T α β γ δ rho M) :
    isBadApprox rho M pq.1 pq.2
      (badWitnessR T α β γ δ rho M pq)
      (badWitnessH T α β γ δ rho M pq) := by
  classical
  have hex : ∃ r h : ℕ, isBadApprox rho M pq.1 pq.2 r h :=
    (Finset.mem_filter.mp hpq).2
  have hr : isBadApprox rho M pq.1 pq.2
      (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)) := by
    exact Classical.choose_spec (Classical.choose_spec hex)
  simpa [badWitnessR, badWitnessH, hpq] using hr

/-- Finite bounds for the canonically selected witnesses.  They are intentionally defined from the
finite bad family rather than claimed to be the sharp analytic bounds. -/
noncomputable def badWitnessRBound
    (T α β γ δ rho : ℝ) (M : ℕ) : ℕ :=
  ((badPairs T α β γ δ rho M).image
      (badWitnessR T α β γ δ rho M)).sup id + 1

noncomputable def badWitnessHBound
    (T α β γ δ rho : ℝ) (M : ℕ) : ℕ :=
  ((badPairs T α β γ δ rho M).image
      (badWitnessH T α β γ δ rho M)).sup id + 1

theorem badWitnessR_lt_bound
    (T α β γ δ rho : ℝ) (M : ℕ) {pq : ℕ × ℕ}
    (hpq : pq ∈ badPairs T α β γ δ rho M) :
    badWitnessR T α β γ δ rho M pq < badWitnessRBound T α β γ δ rho M := by
  unfold badWitnessRBound
  apply Nat.lt_succ_of_le
  exact Finset.le_sup (f := id)
    (Finset.mem_image.mpr ⟨pq, hpq, rfl⟩)

theorem badWitnessH_lt_bound
    (T α β γ δ rho : ℝ) (M : ℕ) {pq : ℕ × ℕ}
    (hpq : pq ∈ badPairs T α β γ δ rho M) :
    badWitnessH T α β γ δ rho M pq < badWitnessHBound T α β γ δ rho M := by
  unfold badWitnessHBound
  apply Nat.lt_succ_of_le
  exact Finset.le_sup (f := id)
    (Finset.mem_image.mpr ⟨pq, hpq, rfl⟩)

theorem badPairs_subset_window_product
    (T α β γ δ rho : ℝ) (M : ℕ) :
    badPairs T α β γ δ rho M ⊆
      (primeWindow T α β).product (primeWindow T γ δ) := by
  classical
  intro pq hpq
  exact (Finset.mem_filter.mp hpq).1

theorem badPairBlock_subset_window_product
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    badPairBlock T α β γ δ rho M r h ⊆
      (primeWindow T α β).product (primeWindow T γ δ) := by
  classical
  intro pq hpq
  exact (Finset.mem_filter.mp hpq).1

theorem badPairs_subset_badPairBlocks
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h) :
    badPairs T α β γ δ rho M ⊆ badPairBlocks T α β γ δ rho M R H := by
  classical
  intro pq hpq
  obtain ⟨r, hrR, h, hhH, hbad⟩ := hcover hpq
  refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hrR, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_range.mpr hhH, ?_⟩
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpq).1, hbad⟩

/- Convert a finite-union inclusion into the existential cover required by the weight lemmas. -/
theorem badPairs_cover_of_subset_badPairBlocks
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hsubset : badPairs T α β γ δ rho M ⊆
      badPairBlocks T α β γ δ rho M R H) :
    ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h := by
  classical
  intro pq hpq
  have hmem := hsubset hpq
  rcases Finset.mem_biUnion.mp hmem with ⟨r, hrmem, hmem⟩
  rcases Finset.mem_biUnion.mp hmem with ⟨h, hhmem, hpair⟩
  have hfilter := Finset.mem_filter.mp hpair
  exact ⟨r, Finset.mem_range.mp hrmem, h, Finset.mem_range.mp hhmem, hfilter.2⟩

/-- The source-scale finite cover: the `r` bound comes from the first window, `h=0` is removed
by the ordered-window lemma, and positive `h` is controlled by the explicit endpoint inequality
used to choose `H`. -/
theorem badPairs_subset_badPairBlocks_of_ordered_windows
    (T α β γ δ rho : ℝ) (M H : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hH : ∀ ⦃r : ℕ⦄, r < reportRBound T β rho →
      (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) < (H : ℝ)) :
    badPairs T α β γ δ rho M ⊆
      badPairBlocks T α β γ δ rho M (reportRBound T β rho) H := by
  classical
  apply badPairs_subset_badPairBlocks T α β γ δ rho M _ _
  intro pq hpq
  have hpqMem := Finset.mem_filter.mp hpq
  have hpProd := Finset.mem_product.mp hpqMem.1
  obtain ⟨r, h, hbad⟩ := hpqMem.2
  have hrR := isBadApprox_r_lt_reportRBound hpProd.1 hbad hrho
  have hHlt : h < H := by
    by_cases hh0 : h = 0
    · have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hbad.1
      have hzero : pq ∈ badPairBlock T α β γ δ rho M r 0 := by
        apply Finset.mem_filter.mpr
        exact ⟨hpqMem.1, by simpa [hh0] using hbad⟩
      have hempty := badPairBlock_h_zero_empty_of_ordered_windows
        T α β γ δ rho M r hT hβγ hM hrpos
      rw [hempty] at hzero
      exfalso
      simp at hzero
    · exact isBadApprox_h_lt_of_prime_windows hpProd.1 hpProd.2 hbad
        (Nat.zero_lt_of_lt hM) hL (hH hrR)
  exact ⟨r, hrR, h, hHlt, hbad⟩

theorem badPairs_subset_badPairBlocks_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    badPairs T α β γ δ rho M ⊆
      badPairBlocks T α β γ δ rho M (reportRBound T β rho)
        (reportHBound T α β δ rho M) := by
  apply badPairs_subset_badPairBlocks_of_ordered_windows T α β γ δ rho M
    (reportHBound T α β δ rho M) hT hβγ hrho hM hL
  intro r hr
  exact reportHBound_condition hr hpositive

theorem badPairs_subset_badPairBlocks_explicit
    (T α β γ δ rho : ℝ) (M : ℕ) :
    badPairs T α β γ δ rho M ⊆
      badPairBlocks T α β γ δ rho M
        (badWitnessRBound T α β γ δ rho M)
        (badWitnessHBound T α β γ δ rho M) := by
  apply badPairs_subset_badPairBlocks T α β γ δ rho M _ _
  intro pq hpq
  exact ⟨badWitnessR T α β γ δ rho M pq,
    badWitnessR_lt_bound T α β γ δ rho M hpq,
    badWitnessH T α β γ δ rho M pq,
    badWitnessH_lt_bound T α β γ δ rho M hpq,
    badWitness_spec T α β γ δ rho M hpq⟩

theorem badPairWeight_le_badPairBlock_sum
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H,
        pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) := by
  classical
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        pairReciprocalWeight (badPairBlocks T α β γ δ rho M R H) :=
      pairReciprocalWeight_mono (badPairs_subset_badPairBlocks T α β γ δ rho M R H hcover)
    _ ≤ ∑ r ∈ Finset.range R,
        pairReciprocalWeight ((Finset.range H).biUnion
          (fun h ↦ badPairBlock T α β γ δ rho M r h)) := by
      exact pairReciprocalWeight_biUnion_le _ _
    _ ≤ ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H,
        pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) := by
      gcongr with r hr
      exact pairReciprocalWeight_biUnion_le _ _

/-- The finite parameter-summation interface.  Any explicit upper bound for each `(r,h)` block
can be inserted here; the analytic proof is consequently isolated from the finite covering and
union bookkeeping. -/
theorem badPairWeight_le_parameter_sum_of_bounds
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (bound : ℕ → ℕ → ℝ)
    (hblock : ∀ ⦃r h : ℕ⦄, r < R → h < H →
      pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤ bound r h) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H, bound r h := by
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H,
          pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) :=
      badPairWeight_le_badPairBlock_sum T α β γ δ rho M R H hcover
    _ ≤ ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H, bound r h := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro h hh
      exact hblock (Finset.mem_range.mp hr) (Finset.mem_range.mp hh)

/- A filtered h-sum that retains the lower-endpoint information from the q-window.  The
majorant is set to zero below `primeWindowHLower`; those blocks are empty, so this is a strict
refinement of the unfiltered parameter-sum interface. -/
theorem badPairWeight_le_parameter_sum_of_bounds_lower_h
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hT : 1 ≤ T) (hM : 0 < M)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (bound : ℕ → ℕ → ℝ)
    (hblock : ∀ ⦃r h : ℕ⦄,
      r < R → primeWindowHLower T β γ M r ≤ h → h < H →
      pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤ bound r h) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range R,
        ∑ h ∈ Finset.range H,
          if primeWindowHLower T β γ M r ≤ h then bound r h else 0 := by
  apply badPairWeight_le_parameter_sum_of_bounds T α β γ δ rho M R H hcover
    (fun r h ↦ if primeWindowHLower T β γ M r ≤ h then bound r h else 0)
  intro r h hr hh
  by_cases hlow : primeWindowHLower T β γ M r ≤ h
  · simpa [hlow] using hblock hr hlow hh
  · have hempty : badPairBlock T α β γ δ rho M r h = ∅ :=
      badPairBlock_empty_below_primeWindowHLower hT hM (Nat.lt_of_not_ge hlow)
    rw [hempty]
    simp [hlow, pairReciprocalWeight]

theorem badPairWeight_le_window_product
    (T α β γ δ rho : ℝ) (M : ℕ) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      pairReciprocalWeight ((primeWindow T α β).product (primeWindow T γ δ)) := by
  classical
  unfold badPairs
  exact pairReciprocalWeight_filter_le _ _

theorem badPairWeight_le_marginal_product
    (T α β γ δ rho : ℝ) (M : ℕ) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      (∑ p ∈ primeWindow T α β, ((p : ℝ)⁻¹)) *
        (∑ q ∈ primeWindow T γ δ, ((q : ℝ)⁻¹)) := by
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        pairReciprocalWeight ((primeWindow T α β).product (primeWindow T γ δ)) :=
      badPairWeight_le_window_product T α β γ δ rho M
    _ = (∑ p ∈ primeWindow T α β, ((p : ℝ)⁻¹)) *
        (∑ q ∈ primeWindow T γ δ, ((q : ℝ)⁻¹)) :=
      pairReciprocalWeight_product _ _

/- The finite bad-pair construction is now separated from the analytic estimate.  Once a
uniform nonnegative upper bound for the parameter sum has been proved, this theorem closes the
topological `o(1)` step without introducing an axiom or hiding the missing estimate in a `sorry`. -/
theorem tendsto_badPairWeight_zero_of_analytic_bound
    {alpha beta gamma delta rho : ℝ} {M : ℕ}
    (bound : ℝ → ℝ)
    (hupper : ∀ T,
      pairReciprocalWeight (badPairs T alpha beta gamma delta rho M) ≤ bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight (badPairs T alpha beta gamma delta rho M))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg (badPairs T alpha beta gamma delta rho M))
  · exact Filter.Eventually.of_forall hupper
  · exact hbound

end

end Erdos878

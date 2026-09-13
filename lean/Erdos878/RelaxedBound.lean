/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.PrimeCounting

/-!
# Integer-base relaxation for the formula (17) gap

This file isolates the first rigorous step of the third #878 candidate.  A prime divisor set
has logarithmic budget at most `log n`.  After paying `log p / L` for each base, all remaining
weight is confined to the positive-part surplus on the bases with `log p < L`.  The later
short-interval summation is deliberately not hidden in this lemma.
-/

open scoped BigOperators

namespace Erdos878

noncomputable def normalizedPrimePowerWeight (n p : ℕ) : ℝ :=
  (p ^ Nat.log p n : ℝ) / (n : ℝ)

noncomputable def normalizedBaseCost (L : ℝ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / L

noncomputable def normalizedPositiveSurplus (n : ℕ) (L : ℝ) (p : ℕ) : ℝ :=
  max (normalizedPrimePowerWeight n p - normalizedBaseCost L p) 0

/-- The real endpoint profile used in the report.  The integer base `b` is represented by
`a = log b`, and `k = floor(log n / log b)` is exactly `Nat.log b n` for the integer input. -/
noncomputable def surplusProfile (T L : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  max (Real.exp (k * a - T) - a / L) 0

theorem surplusProfile_nonneg (T L : ℝ) (k : ℕ) (a : ℝ) :
    0 ≤ surplusProfile T L k a := by
  exact le_max_right _ _

theorem surplusProfile_pos_iff {T L : ℝ} {k : ℕ} {a : ℝ} :
    0 < surplusProfile T L k a ↔ a / L < Real.exp (k * a - T) := by
  simp [surplusProfile]

theorem surplusProfile_eq_zero_of_exp_le {T L : ℝ} {k : ℕ} {a : ℝ}
    (h : Real.exp (k * a - T) ≤ a / L) :
    surplusProfile T L k a = 0 := by
  unfold surplusProfile
  rw [max_eq_right (sub_nonpos.mpr h)]

/- The endpoint bands in the report have `k*a ≤ T` because `k` is the floor exponent.  On
such a band the profile is automatically bounded by one: the exponential term is at most one,
and the cost term is nonnegative.  This is the first pointwise estimate needed when summing a
band by counting its integer bases. -/
theorem surplusProfile_le_one_of_mul_le
    {T L : ℝ} {k : ℕ} {a : ℝ}
    (hL : 0 < L) (ha0 : 0 ≤ a)
    (hka : (k : ℝ) * a ≤ T) :
    surplusProfile T L k a ≤ 1 := by
  unfold surplusProfile
  apply max_le
  · have hexp : Real.exp ((k : ℝ) * a - T) ≤ 1 := by
      calc
        Real.exp ((k : ℝ) * a - T) ≤ Real.exp 0 := by
          apply (Real.exp_le_exp).2
          linarith
        _ = 1 := by norm_num
    have hcost : 0 ≤ a / L := div_nonneg ha0 hL.le
    linarith
  · norm_num

/- Retaining the distance from the upper logarithmic endpoint gives a sharper pointwise bound.
When `a ≤ L`, the positive profile is at most `(L-a)/L`; this is the elementary decay factor used
when the short endpoint bands are summed instead of merely counted. -/
theorem surplusProfile_le_one_sub_div_of_mul_le
    {T L : ℝ} {k : ℕ} {a : ℝ}
    (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hka : (k : ℝ) * a ≤ T) :
    surplusProfile T L k a ≤ (L - a) / L := by
  unfold surplusProfile
  apply max_le
  · have hexp : Real.exp ((k : ℝ) * a - T) ≤ 1 := by
      calc
        Real.exp ((k : ℝ) * a - T) ≤ Real.exp 0 := by
          apply (Real.exp_le_exp).2
          linarith
        _ = 1 := by norm_num
    have hcost : 0 ≤ a / L := div_nonneg ha0 hL.le
    have hrewrite : (L - a) / L = 1 - a / L := by
      field_simp [ne_of_gt hL]
    rw [hrewrite]
    linarith
  · have hnonneg : 0 ≤ L - a := sub_nonneg.mpr haL
    exact div_nonneg hnonneg hL.le

/- If the exponent endpoint lies strictly above the upper logarithmic cutoff, then no positive
profile survives on the lower half `L/2 ≤ a ≤ L` once `L ≥ 2`.  This removes the single boundary
fiber that is not eliminated by the crude integer window `T/L - 1 < k`.  The proof is elementary:
for `t = a/L ∈ [1/2,1]`, `exp (-(L-a)) ≤ t` follows from
`1/t ≤ 1 + 2(1-t) ≤ exp (L-a)`. -/
theorem surplusProfile_eq_zero_of_endpoint_above
    {T L : ℝ} {k : ℕ} {a : ℝ}
    (hL2 : 2 ≤ L) (hhalf : L / 2 ≤ a) (haL : a ≤ L)
    (hk : 0 < k) (hT : (k : ℝ) * L < T) :
    surplusProfile T L k a = 0 := by
  have hLpos : 0 < L := by linarith
  have ha0 : 0 < a := by
    have : 0 < L / 2 := by positivity
    exact this.trans_le hhalf
  let t : ℝ := a / L
  let y : ℝ := L * (1 - t)
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos ha0 hLpos
  have hthalf : (1 / 2 : ℝ) ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hLpos).2
    nlinarith
  have htone : t ≤ 1 := by
    dsimp [t]
    exact (div_le_iff₀ hLpos).2 (by linarith)
  have hprod : 0 ≤ (2 * t - 1) * (1 - t) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hinv_basic : 1 / t ≤ 1 + 2 * (1 - t) := by
    apply (div_le_iff₀ htpos).2
    nlinarith [hprod]
  have hy_eq : y = L - a := by
    dsimp [y, t]
    field_simp [ne_of_gt hLpos]
  have hy0 : 0 ≤ y := by
    rw [hy_eq]
    exact sub_nonneg.mpr haL
  have hlin : 1 + 2 * (1 - t) ≤ 1 + y := by
    have hLy : 2 * (1 - t) ≤ L * (1 - t) := by
      exact mul_le_mul_of_nonneg_right hL2 (by linarith)
    linarith
  have hexpadd : 1 + y ≤ Real.exp y := by
    simpa [add_comm] using (Real.add_one_le_exp y)
  have hinv : 1 / t ≤ Real.exp y := hinv_basic.trans (hlin.trans hexpadd)
  have hmul : 1 ≤ t * Real.exp y := by
    have h := (div_le_iff₀ htpos).mp hinv
    nlinarith
  have hexpneg : Real.exp (-y) ≤ t := by
    have hdiv : 1 / Real.exp y ≤ t := by
      apply (div_le_iff₀ (Real.exp_pos y)).2
      simpa [mul_comm] using hmul
    simpa [Real.exp_neg] using hdiv
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
  have hdiff : 0 ≤ L - a := sub_nonneg.mpr haL
  have hka : (k : ℝ) * a - T ≤ -y := by
    have hstrict : (k : ℝ) * a - T < (k : ℝ) * a - (k : ℝ) * L := by
      linarith
    have hmul : (L - a) ≤ (k : ℝ) * (L - a) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hkone hdiff
    rw [hy_eq]
    nlinarith
  have hexp : Real.exp ((k : ℝ) * a - T) ≤ Real.exp (-y) :=
    (Real.exp_le_exp).mpr hka
  apply surplusProfile_eq_zero_of_exp_le
  have hcost : a / L = t := by rfl
  rw [hcost]
  exact hexp.trans hexpneg

/- A positive profile on the large-base side forces the exponent endpoint to be close to `T`.
The deliberately coarse `log 2` loss is enough for the later finite-band counting argument and
avoids hiding the report's analytic work in an axiom. -/
theorem surplusProfile_pos_mul_lower_of_half_le
    {T L A : ℝ} {k : ℕ} {a : ℝ}
    (hL : 0 < L) (hA : L / 2 ≤ A) (hapos : A ≤ a)
    (hpos : 0 < surplusProfile T L k a) :
    T - Real.log 2 < (k : ℝ) * a := by
  have hLa : L / 2 ≤ a := hA.trans hapos
  have hhalf : (1 / 2 : ℝ) ≤ a / L := by
    apply (le_div_iff₀ hL).2
    nlinarith
  have hdiff : a / L < Real.exp ((k : ℝ) * a - T) :=
    (surplusProfile_pos_iff.mp hpos)
  have hexp : (1 / 2 : ℝ) < Real.exp ((k : ℝ) * a - T) :=
    hhalf.trans_lt hdiff
  have hlog : Real.log (1 / 2 : ℝ) < (k : ℝ) * a - T :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    have heq : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [heq, Real.log_inv]
  rw [hloghalf] at hlog
  linarith

/- Combining the floor-band upper endpoint with the preceding lower endpoint gives the compact
interval in the logarithmic base variable that the report sums one exponent at a time. -/
theorem surplusProfile_pos_mem_band_of_half_le
    {T L A : ℝ} {k : ℕ} {a : ℝ}
    (hL : 0 < L) (hA : L / 2 ≤ A) (hapos : A ≤ a)
    (hk : 0 < k) (hka : (k : ℝ) * a ≤ T)
    (hpos : 0 < surplusProfile T L k a) :
    T / (k : ℝ) - Real.log 2 / (k : ℝ) < a ∧
      a ≤ T / (k : ℝ) := by
  have hkl : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlow := surplusProfile_pos_mul_lower_of_half_le hL hA hapos hpos
  constructor
  · have hrewrite : T / (k : ℝ) - Real.log 2 / (k : ℝ) =
        (T - Real.log 2) / (k : ℝ) := by ring
    rw [hrewrite]
    apply (div_lt_iff₀ hkl).2
    simpa [mul_comm] using hlow
  · apply (le_div_iff₀ hkl).2
    simpa [mul_comm] using hka

/- A derivative-free sharpened endpoint band.  The report uses a constant `2`; the elementary
   exponential estimate below gives the slightly weaker constant `4`, which is already enough to
   preserve the decisive `(L-r)/T` width.  This avoids importing a mean-value theorem into the
   finite kernel while retaining the scale needed by the later global summation. -/
theorem surplusProfile_pos_mem_sharp_band
    {T L A : ℝ} {k : ℕ} {a : ℝ}
    (hT : 4 ≤ T) (hL : 0 < L) (hAhalf : L / 2 ≤ A) (hapos : A ≤ a)
    (hk : 0 < k) (hTk : T / (k : ℝ) ≤ L)
    (hka : (k : ℝ) * a ≤ T)
    (hpos : 0 < surplusProfile T L k a) :
    T / (k : ℝ) - 4 * (L - T / (k : ℝ)) / T < a ∧
      a ≤ T / (k : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  let r : ℝ := T / (k : ℝ)
  let d : ℝ := r - a
  have hkr : (k : ℝ) * r = T := by
    dsimp [r]
    field_simp [hkreal.ne']
  have hupper : a ≤ r := by
    apply (le_div_iff₀ hkreal).2
    simpa [r, mul_comm] using hka
  have ha_half : L / 2 ≤ a := hAhalf.trans hapos
  have hrL : r ≤ L := by simpa [r] using hTk
  have hdnonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hdlower : d ≤ r / 2 := by
    dsimp [d]
    nlinarith [ha_half, hrL]
  have hkdle : (k : ℝ) * d ≤ T / 2 := by
    have hm := mul_le_mul_of_nonneg_left hdlower hkreal.le
    calc
      (k : ℝ) * d ≤ (k : ℝ) * (r / 2) := hm
      _ = ((k : ℝ) * r) / 2 := by ring
      _ = T / 2 := by rw [hkr]
  have hTquarter : T / 4 ≤ T - 1 - (k : ℝ) * d := by
    nlinarith
  have ha_pos : 0 < a := by
    have hLhalf : 0 < L / 2 := by positivity
    exact hLhalf.trans_le ha_half
  have hlower : r - 4 * (L - r) / T < a := by
    by_contra hnot
    have hdl : 4 * (L - r) / T ≤ d := by
      dsimp [d] at *
      linarith
    have hdlmul : 4 * (L - r) ≤ d * T := by
      exact (div_le_iff₀ hTpos).mp hdl
    have hdlquarter : L - r ≤ d * (T / 4) := by
      nlinarith
    have hDprod : L - r ≤ d * (T - 1 - (k : ℝ) * d) := by
      exact hdlquarter.trans
        (mul_le_mul_of_nonneg_left hTquarter hdnonneg)
    have hprod : L ≤ (1 + (k : ℝ) * d) * (r - d) := by
      have hid : (1 + (k : ℝ) * d) * (r - d) =
          r + d * (T - 1 - (k : ℝ) * d) := by
        calc
          (1 + (k : ℝ) * d) * (r - d) =
              r + d * ((k : ℝ) * r - 1 - (k : ℝ) * d) := by ring
          _ = r + d * (T - 1 - (k : ℝ) * d) := by rw [hkr]
      rw [hid]
      linarith
    have hkaT : (k : ℝ) * a - T = -((k : ℝ) * d) := by
      calc
        (k : ℝ) * a - T = (k : ℝ) * a - (k : ℝ) * r := by rw [← hkr]
        _ = -((k : ℝ) * d) := by dsimp [d]; ring
    have hpos' : a / L < Real.exp (-((k : ℝ) * d)) := by
      rw [surplusProfile_pos_iff] at hpos
      simpa [hkaT] using hpos
    have hmul := mul_lt_mul_of_pos_right hpos' (Real.exp_pos ((k : ℝ) * d))
    have hcancel : Real.exp (-((k : ℝ) * d)) * Real.exp ((k : ℝ) * d) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    have hmul' : (a / L) * Real.exp ((k : ℝ) * d) < 1 := by
      simpa [hcancel] using hmul
    have hmulL := mul_lt_mul_of_pos_right hmul' hL
    have hprodlt : a * Real.exp ((k : ℝ) * d) < L := by
      calc
        a * Real.exp ((k : ℝ) * d) =
            ((a / L) * Real.exp ((k : ℝ) * d)) * L := by
              field_simp [hL.ne']
        _ < 1 * L := hmulL
        _ = L := by ring
    have hexp : 1 + (k : ℝ) * d ≤ Real.exp ((k : ℝ) * d) := by
      simpa [add_comm] using (Real.add_one_le_exp ((k : ℝ) * d))
    have hprod' : (1 + (k : ℝ) * d) * a ≤
        Real.exp ((k : ℝ) * d) * a := by
      exact mul_le_mul_of_nonneg_right hexp ha_pos.le
    have hprod'' : L ≤ Real.exp ((k : ℝ) * d) * a := by
      have hprodA : L ≤ (1 + (k : ℝ) * d) * a := by
        simpa [d] using hprod
      exact hprodA.trans (by simpa [mul_comm] using hprod')
    linarith
  constructor
  · simpa [r] using hlower
  · simpa [r] using hupper

/- Integer bases whose logarithms lie in a strict/open-to-closed real interval are contained in
the corresponding floor endpoints.  This elementary counting lemma is the finite conversion used
after the profile support estimate; it keeps the `+1` endpoint contribution explicit. -/
theorem card_le_of_log_band
    (D : Finset ℕ) {u v : ℝ}
    (hD : ∀ b ∈ D, b ≠ 0 ∧ u < Real.log (b : ℝ) ∧
      Real.log (b : ℝ) ≤ v) :
    D.card ≤ Nat.floor (Real.exp v) + 1 -
      (Nat.floor (Real.exp u) + 1) := by
  have hsub : D ⊆ Finset.Icc (Nat.floor (Real.exp u) + 1)
      (Nat.floor (Real.exp v)) := by
    intro b hb
    have hdata := hD b hb
    have hbpos : 0 < (b : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hdata.1)
    have hupperR : (b : ℝ) ≤ Real.exp v := by
      have hlogexp : Real.exp (Real.log (b : ℝ)) = (b : ℝ) :=
        Real.exp_log hbpos
      have hexp := (Real.exp_le_exp).2 hdata.2.2
      simpa [hlogexp] using hexp
    have hupper : b ≤ Nat.floor (Real.exp v) := Nat.le_floor hupperR
    have hlowerR : Real.exp u < (b : ℝ) := by
      have hexp := (Real.exp_lt_exp).2 hdata.2.1
      simpa [Real.exp_log hbpos] using hexp
    have hlower : Nat.floor (Real.exp u) < b :=
      (Nat.floor_lt' hdata.1).2 hlowerR
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  exact hcard

/- The exact floor count has a simple real upper bound.  This removes the integer floors only
after the endpoint contribution has been retained, so the unavoidable `+1` error is explicit. -/
theorem floor_log_band_count_le_exp_width_add_one
    {u v : ℝ} (huv : u ≤ v) :
    ((Nat.floor (Real.exp v) + 1 -
      (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) ≤
      Real.exp v - Real.exp u + 1 := by
  have hfloor : Nat.floor (Real.exp u) ≤ Nat.floor (Real.exp v) := by
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr huv
  have hrewrite : Nat.floor (Real.exp v) + 1 -
      (Nat.floor (Real.exp u) + 1) =
      Nat.floor (Real.exp v) - Nat.floor (Real.exp u) := by
    omega
  rw [hrewrite]
  have huvfloor :
      ((Nat.floor (Real.exp v) : ℕ) : ℝ) -
        ((Nat.floor (Real.exp u) : ℕ) : ℝ) ≤
      Real.exp v - Real.exp u + 1 := by
    have hv : ((Nat.floor (Real.exp v) : ℕ) : ℝ) ≤ Real.exp v :=
      Nat.floor_le (Real.exp_pos v).le
    have hu : Real.exp u < ((Nat.floor (Real.exp u) : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one (Real.exp u)
    linarith
  exact_mod_cast huvfloor

private theorem sum_log_primeFactors_le_log {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hprodPos : 0 < ∏ p ∈ n.primeFactors, p := by
    exact Finset.prod_pos fun p hp ↦ (Nat.pos_of_mem_primeFactors hp)
  have hprodDvd : (∏ p ∈ n.primeFactors, p) ∣ n :=
    Nat.prod_primeFactors_dvd n
  have hprodLe : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprodDvd
  have hprodLeReal : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hprodLe
  have hlog := Real.log_le_log (by exact_mod_cast hprodPos) hprodLeReal
  have hlogProd :
      Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
        ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
    rw [show ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
        ∏ p ∈ n.primeFactors, (p : ℝ) by simp]
    rw [Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
  rw [hlogProd] at hlog
  exact hlog

private theorem normalizedPrimePowerWeight_le_one {n p : ℕ}
    (hn : n ≠ 0) : normalizedPrimePowerWeight n p ≤ 1 := by
  unfold normalizedPrimePowerWeight
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  apply (div_le_iff₀ hnpos).2
  have hpow := Nat.pow_log_le_self p hn
  exact_mod_cast (show p ^ Nat.log p n ≤ 1 * n by simpa using hpow)

theorem normalizedPrimePowerWeight_eq_exp_log_profile
    {n b : ℕ} (hn : n ≠ 0) (hb : 1 < b) :
    normalizedPrimePowerWeight n b =
      Real.exp (Nat.log b n * Real.log (b : ℝ) - Real.log (n : ℝ)) := by
  unfold normalizedPrimePowerWeight
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hb0 : 0 < b := by omega
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hquot : 0 < ((b : ℝ) ^ Nat.log b n) / (n : ℝ) := by
    positivity
  rw [← Real.exp_log hquot]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]

theorem normalizedPositiveSurplus_eq_surplusProfile
    {n b : ℕ} (hn : n ≠ 0) (hb : 1 < b) {L : ℝ} :
    normalizedPositiveSurplus n L b =
      surplusProfile (Real.log (n : ℝ)) L (Nat.log b n) (Real.log (b : ℝ)) := by
  unfold normalizedPositiveSurplus normalizedBaseCost surplusProfile
  rw [normalizedPrimePowerWeight_eq_exp_log_profile hn hb]

theorem natLog_eq_floor_log_div
    {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    Nat.log b n = ⌊Real.log (n : ℝ) / Real.log (b : ℝ)⌋₊ := by
  let k := Nat.log b n
  have hpow_lo : b ^ k ≤ n := Nat.pow_log_le_self b hn
  have hpow_hi : n < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb n
  have hblog : 0 < Real.log (b : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hb
  have hnlog : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hk_nonneg : 0 ≤ Real.log (n : ℝ) / Real.log (b : ℝ) :=
    div_nonneg hnlog hblog.le
  apply Eq.symm
  rw [Nat.floor_eq_iff hk_nonneg]
  constructor
  · apply (le_div_iff₀ hblog).2
    have hpow_loR : ((b ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_lo
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((b ^ k : ℕ) : ℝ)) hpow_loR
    rw [show ((b ^ k : ℕ) : ℝ) = (b : ℝ) ^ k by norm_num, Real.log_pow] at hlog
    simpa [k, mul_comm] using hlog
  · apply (div_lt_iff₀ hblog).2
    have hpow_hiR : (n : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hpow_hi
    have hlog := Real.strictMonoOn_log (by positivity : (0 : ℝ) < (n : ℝ))
      (by positivity : (0 : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ)) hpow_hiR
    rw [show ((b ^ (k + 1) : ℕ) : ℝ) = (b : ℝ) ^ (k + 1) by norm_num,
      Real.log_pow] at hlog
    simpa [k, Nat.cast_add, add_mul, mul_comm] using hlog

private theorem normalizedPrimePowerWeight_le_cost_add_surplus
    {n p : ℕ} {L : ℝ} :
    normalizedPrimePowerWeight n p ≤
      normalizedBaseCost L p + normalizedPositiveSurplus n L p := by
  unfold normalizedPositiveSurplus
  by_cases hdiff : normalizedPrimePowerWeight n p - normalizedBaseCost L p ≤ 0
  · rw [max_eq_right hdiff]
    linarith
  · rw [max_eq_left (le_of_not_ge hdiff)]
    linarith

/-- The exact finite integer-base relaxation used before the surplus summation.

The set `B` is any finite container for the bases with `log p < L`; choosing the natural
interval `2 ≤ p ≤ exp L` gives the usual formulation.  The statement is intentionally
agnostic about primality distribution and therefore can be reused by the later analytic bound.
-/
theorem relaxed_prime_power_upper
    {n : ℕ} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L) {B : Finset ℕ}
    (hB : ∀ p ∈ n.primeFactors, Real.log (p : ℝ) < L → p ∈ B) :
    ∑ p ∈ n.primeFactors, normalizedPrimePowerWeight n p ≤
      Real.log (n : ℝ) / L +
        ∑ p ∈ B, normalizedPositiveSurplus n L p := by
  let P := n.primeFactors
  let S := P.filter (fun p : ℕ ↦ Real.log (p : ℝ) < L)
  have hpoint : ∀ p ∈ P,
      normalizedPrimePowerWeight n p ≤
        normalizedBaseCost L p +
          if p ∈ S then normalizedPositiveSurplus n L p else 0 := by
    intro p hp
    by_cases hsmall : Real.log (p : ℝ) < L
    · have hpS : p ∈ S := by simp [S, P, hp, hsmall]
      simp only [hpS, ite_true]
      exact normalizedPrimePowerWeight_le_cost_add_surplus
    · have hlarge : L ≤ Real.log (p : ℝ) := le_of_not_gt hsmall
      have hcost : 1 ≤ normalizedBaseCost L p := by
        unfold normalizedBaseCost
        exact (le_div_iff₀ hL).2 (by simpa [one_mul] using hlarge)
      have hw : normalizedPrimePowerWeight n p ≤ 1 :=
        normalizedPrimePowerWeight_le_one hn
      have hpS : p ∉ S := by simp [S, P, hp, hsmall]
      simp only [hpS, ite_false, add_zero]
      exact hw.trans hcost
  calc
    ∑ p ∈ P, normalizedPrimePowerWeight n p ≤
        ∑ p ∈ P, (normalizedBaseCost L p +
          if p ∈ S then normalizedPositiveSurplus n L p else 0) := by
      gcongr with p hp
      exact hpoint p hp
    _ = (∑ p ∈ P, normalizedBaseCost L p) +
        ∑ p ∈ S, normalizedPositiveSurplus n L p := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [show (∑ p ∈ P,
          if p ∈ S then normalizedPositiveSurplus n L p else 0) =
          ∑ p ∈ S, normalizedPositiveSurplus n L p by
        have hfilter : P.filter (fun p : ℕ ↦ p ∈ S) = S := by
          ext p
          simp only [Finset.mem_filter]
          constructor
          · exact fun h ↦ h.2
          · intro hpS
            exact ⟨(Finset.filter_subset _ _ ) hpS, hpS⟩
        calc
          (∑ p ∈ P, if p ∈ S then normalizedPositiveSurplus n L p else 0) =
              ∑ p ∈ P.filter (fun p : ℕ ↦ p ∈ S), normalizedPositiveSurplus n L p := by
                exact (Finset.sum_filter (s := P)
                  (p := fun p : ℕ ↦ p ∈ S)
                  (f := fun p : ℕ ↦ normalizedPositiveSurplus n L p)).symm
          _ = ∑ p ∈ S, normalizedPositiveSurplus n L p := by rw [hfilter]]
    _ ≤ Real.log (n : ℝ) / L +
        ∑ p ∈ B, normalizedPositiveSurplus n L p := by
      have hcost :
          (∑ p ∈ P, normalizedBaseCost L p) ≤ Real.log (n : ℝ) / L := by
        unfold normalizedBaseCost
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right
          (sum_log_primeFactors_le_log hn) (le_of_lt hL)
      have hsubset : S ⊆ B := by
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
        have hpSmall : Real.log (p : ℝ) < L := (Finset.mem_filter.mp hp).2
        exact hB p hpP hpSmall
      exact add_le_add hcost
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro p hp _
          change 0 ≤ max
            (normalizedPrimePowerWeight n p - normalizedBaseCost L p) 0
          exact le_max_right _ _))

/-- Concrete interval form: the abstract container in `relaxed_prime_power_upper` may be chosen
as the integer interval `2 ≤ b ≤ floor(exp L)`. -/
theorem relaxed_prime_power_upper_exp_interval
    {n : ℕ} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∑ p ∈ n.primeFactors, normalizedPrimePowerWeight n p ≤
      Real.log (n : ℝ) / L +
        ∑ p ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L p := by
  apply relaxed_prime_power_upper hn hL
  intro p hp hlog
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hpp.two_le
  have hpExp : (p : ℝ) < Real.exp L :=
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hpp.pos)).mp hlog
  have hpFloor : p ≤ ⌊Real.exp L⌋₊ := Nat.le_floor hpExp.le
  exact Finset.mem_Icc.mpr ⟨hp2, hpFloor⟩

/-! The first band in the report's endpoint decomposition is completely elementary.  If
`log 2 ≤ A`, every base `2 ≤ b ≤ exp A` contributes at most one unit of normalized surplus;
there are at most `exp A` such bases.  This is the rigorous small-base term corresponding to the
`Z = exp A` summand in the compressed proof sketch. -/
theorem small_base_surplus_sum_le_exp
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hL : 0 < L) :
    ∑ p ∈ Finset.Icc 2 (⌊Real.exp A⌋₊), normalizedPositiveSurplus n L p ≤ Real.exp A := by
  have hexp : 0 ≤ Real.exp A := Real.exp_pos A |>.le
  have hpoint : ∀ p ∈ Finset.Icc 2 (⌊Real.exp A⌋₊),
      normalizedPositiveSurplus n L p ≤ (1 : ℝ) := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
    have hcost : 0 ≤ normalizedBaseCost L p := by
      unfold normalizedBaseCost
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))) hL.le
    have hw : normalizedPrimePowerWeight n p ≤ 1 := by
      unfold normalizedPrimePowerWeight
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      apply (div_le_iff₀ hnpos).2
      have hpow := Nat.pow_log_le_self p hn
      exact_mod_cast (show p ^ Nat.log p n ≤ 1 * n by simpa using hpow)
    apply max_le
    · linarith
    · norm_num
  calc
    ∑ p ∈ Finset.Icc 2 (⌊Real.exp A⌋₊), normalizedPositiveSurplus n L p ≤
        ∑ _p ∈ Finset.Icc 2 (⌊Real.exp A⌋₊), (1 : ℝ) := by
      gcongr with p hp
      exact hpoint p hp
    _ = (Finset.Icc 2 (⌊Real.exp A⌋₊)).card := by simp
    _ ≤ (⌊Real.exp A⌋₊ : ℝ) := by
      have hk : 2 ≤ ⌊Real.exp A⌋₊ := by
        apply Nat.le_floor
        have htwo : (2 : ℝ) ≤ Real.exp A := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          exact Real.exp_le_exp.mpr hA
        exact htwo
      rw [Nat.card_Icc]
      have hcard : ⌊Real.exp A⌋₊ + 1 - 2 ≤ ⌊Real.exp A⌋₊ := by omega
      exact_mod_cast hcard
    _ ≤ Real.exp A := by exact_mod_cast (Nat.floor_le hexp)

/-! Split the complete integer-base container at the endpoint `exp A`.  This is the exact
bookkeeping step needed before the report's per-exponent endpoint bands: the small contribution is
handled by `small_base_surplus_sum_le_exp`, and every remaining base lies in the displayed tail
interval. -/
theorem surplus_sum_split_small_tail
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L) :
    ∑ p ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L p ≤
      Real.exp A +
        ∑ p ∈ Finset.Icc (⌊Real.exp A⌋₊ + 1) (⌊Real.exp L⌋₊),
          normalizedPositiveSurplus n L p := by
  let B : Finset ℕ := Finset.Icc 2 (⌊Real.exp L⌋₊)
  let S : Finset ℕ := Finset.Icc 2 (⌊Real.exp A⌋₊)
  let T : Finset ℕ := Finset.Icc (⌊Real.exp A⌋₊ + 1) (⌊Real.exp L⌋₊)
  have hfloorA : 2 ≤ ⌊Real.exp A⌋₊ := by
    apply Nat.le_floor
    have htwo : (2 : ℝ) ≤ Real.exp A := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hA
    exact htwo
  have hfloorle : ⌊Real.exp A⌋₊ ≤ ⌊Real.exp L⌋₊ := by
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr hAL
  have hSB : S ⊆ B := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hp).1, (Finset.mem_Icc.mp hp).2.trans hfloorle⟩
  have hTB : T ⊆ B := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨hfloorA.trans (Nat.le_succ _)
          |>.trans (Finset.mem_Icc.mp hp).1, (Finset.mem_Icc.mp hp).2⟩
  have hcover : B ⊆ S ∪ T := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
    have hpk : p ≤ ⌊Real.exp A⌋₊ ∨ ⌊Real.exp A⌋₊ + 1 ≤ p := by omega
    rcases hpk with hpk | hpk
    · exact Finset.mem_union_left T (Finset.mem_Icc.mpr ⟨hp2, hpk⟩)
    · exact Finset.mem_union_right S
        (Finset.mem_Icc.mpr ⟨hpk, (Finset.mem_Icc.mp hp).2⟩)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hpS hpT
    have hle : p ≤ ⌊Real.exp A⌋₊ := (Finset.mem_Icc.mp hpS).2
    have hge : ⌊Real.exp A⌋₊ + 1 ≤ p := (Finset.mem_Icc.mp hpT).1
    omega
  have hsum :
      (∑ p ∈ B, normalizedPositiveSurplus n L p) ≤
        ∑ p ∈ S ∪ T, normalizedPositiveSurplus n L p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hcover (by
      intro p hp hnot
      exact le_max_right _ _)
  have hsmall := small_base_surplus_sum_le_exp hn hA hL
  calc
    ∑ p ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L p
        = ∑ p ∈ B, normalizedPositiveSurplus n L p := by rfl
    _ ≤ ∑ p ∈ S ∪ T, normalizedPositiveSurplus n L p := hsum
    _ = (∑ p ∈ S, normalizedPositiveSurplus n L p) +
        ∑ p ∈ T, normalizedPositiveSurplus n L p := Finset.sum_union hdisj
    _ ≤ Real.exp A + ∑ p ∈ T, normalizedPositiveSurplus n L p := by
      gcongr
    _ = Real.exp A +
        ∑ p ∈ Finset.Icc (⌊Real.exp A⌋₊ + 1) (⌊Real.exp L⌋₊),
          normalizedPositiveSurplus n L p := by rfl

/-! The report's endpoint bands are indexed by the integer exponent
`k = floor(log n / log b)`, represented here by `Nat.log b n`.  The next two lemmas make that
partition explicit.  They do not estimate a band; they expose exactly the finite sum to which a
per-band analytic estimate must be applied. -/
noncomputable def surplusBand (n : ℕ) (L : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (⌊Real.exp L⌋₊)).filter (fun b ↦ Nat.log b n = k)

theorem mem_surplusBand_iff {n k b : ℕ} {L : ℝ} :
    b ∈ surplusBand n L k ↔
      b ∈ Finset.Icc 2 (⌊Real.exp L⌋₊) ∧ Nat.log b n = k := by
  simp [surplusBand]

theorem base_interval_eq_biUnion_surplusBand
    {n : ℕ} {L : ℝ} :
    Finset.Icc 2 (⌊Real.exp L⌋₊) =
      (Finset.range (n + 1)).biUnion (fun k ↦ surplusBand n L k) := by
  classical
  ext b
  constructor
  · intro hb
    have hlog : Nat.log b n ≤ n := Nat.log_le_self b n
    refine Finset.mem_biUnion.mpr ⟨Nat.log b n,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hlog), ?_⟩
    exact Finset.mem_filter.mpr ⟨hb, rfl⟩
  · intro hb
    obtain ⟨k, hk, hbk⟩ := Finset.mem_biUnion.mp hb
    exact (Finset.mem_filter.mp hbk).1

theorem surplus_sum_eq_sum_surplusBands
    {n : ℕ} {L : ℝ} :
    (∑ b ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L b) =
      ∑ k ∈ Finset.range (n + 1),
        ∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b := by
  classical
  have hdisj : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      i ≠ j → Disjoint (surplusBand n L i) (surplusBand n L j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro b hbi hbj
    have hki := (Finset.mem_filter.mp hbi).2
    have hkj := (Finset.mem_filter.mp hbj).2
    exact hij (hki.symm.trans hkj)
  rw [base_interval_eq_biUnion_surplusBand]
  exact Finset.sum_biUnion hdisj

theorem surplus_sum_le_of_band_bounds
    {n : ℕ} {L : ℝ} {C : ℕ → ℝ}
    (hband : ∀ k ∈ Finset.range (n + 1),
      (∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b) ≤ C k) :
    ∑ b ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L b ≤
      ∑ k ∈ Finset.range (n + 1), C k := by
  rw [surplus_sum_eq_sum_surplusBands]
  gcongr with k hk
  exact hband k hk

/- Every floor-exponent band has the elementary profile bound obtained above.  This is intentionally
stated separately from the sharper support count: it provides a checked baseline for each band and
makes the remaining work precisely the improvement from the full band cardinality to the short
endpoint interval claimed in the report. -/
theorem surplusBand_sum_le_card
    {n : ℕ} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L) (k : ℕ) :
    (∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b) ≤
      ((surplusBand n L k).card : ℝ) := by
  calc
    (∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b) ≤
        ∑ _b ∈ surplusBand n L k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbdata := (Finset.mem_filter.mp hb)
      have hbI : b ∈ Finset.Icc 2 (⌊Real.exp L⌋₊) := hbdata.1
      have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hbI).1
      have hblog : 0 ≤ Real.log (b : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
      have hpow : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hpowR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hpow
      have hlog := Real.log_le_log
        (by positivity : 0 < ((b ^ Nat.log b n : ℕ) : ℝ)) hpowR
      rw [show ((b ^ Nat.log b n : ℕ) : ℝ) = (b : ℝ) ^ Nat.log b n by norm_num,
        Real.log_pow] at hlog
      have hka : (Nat.log b n : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
        simpa [mul_comm] using hlog
      rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2]
      exact surplusProfile_le_one_of_mul_le hL hblog hka
    _ = ((surplusBand n L k).card : ℝ) := by simp

/- If a finite collection of bases is already restricted to the positive-profile part of one
exponent band, the preceding support lemma and `card_le_of_log_band` give an exact floor-endpoint
count.  The hypotheses are intentionally generic so the later report proof can instantiate them
with whichever tail filter it uses. -/
theorem sum_surplusProfile_le_floor_band
    (D : Finset ℕ) {T L A : ℝ} {k : ℕ}
    (hL : 0 < L) (hk : 0 < k)
    (hD : ∀ b ∈ D,
      b ≠ 0 ∧ L / 2 ≤ A ∧ A ≤ Real.log (b : ℝ) ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ T ∧
        0 < surplusProfile T L k (Real.log (b : ℝ))) :
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
      ((Nat.floor (Real.exp (T / (k : ℝ))) + 1 -
        (Nat.floor (Real.exp ((T - Real.log 2) / (k : ℝ))) + 1) : ℕ) : ℝ) := by
  have hcard : D.card ≤
      Nat.floor (Real.exp (T / (k : ℝ))) + 1 -
        (Nat.floor (Real.exp ((T - Real.log 2) / (k : ℝ))) + 1) := by
    apply card_le_of_log_band D
    intro b hb
    have hdata := hD b hb
    have hband := surplusProfile_pos_mem_band_of_half_le
      hL hdata.2.1 hdata.2.2.1 hk hdata.2.2.2.1 hdata.2.2.2.2
    refine ⟨hdata.1, ?_, hband.2⟩
    have hrewrite : T / (k : ℝ) - Real.log 2 / (k : ℝ) =
        (T - Real.log 2) / (k : ℝ) := by ring
    rw [← hrewrite]
    exact hband.1
  calc
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
        ∑ _b ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hdata := hD b hb
      have hLhalf : 0 ≤ L / 2 := by positivity
      have hblog : 0 ≤ Real.log (b : ℝ) :=
        le_trans (le_trans hLhalf hdata.2.1) hdata.2.2.1
      exact surplusProfile_le_one_of_mul_le hL hblog hdata.2.2.2.1
    _ = (D.card : ℝ) := by simp
    _ ≤ ((Nat.floor (Real.exp (T / (k : ℝ))) + 1 -
        (Nat.floor (Real.exp ((T - Real.log 2) / (k : ℝ))) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard

/- A width-weighted companion for the preceding floor count.  If all logarithmic bases lie above
`u` and below `L`, the profile contributes at most `(L-u)/L` per base.  This retains the endpoint
decay that the report uses before performing its global exponent-band sum. -/
theorem sum_surplusProfile_le_width_mul_card
    (D : Finset ℕ) {T L u : ℝ} {k : ℕ}
    (hL : 0 < L)
    (hD : ∀ b ∈ D,
      0 ≤ Real.log (b : ℝ) ∧ u < Real.log (b : ℝ) ∧
        Real.log (b : ℝ) ≤ L ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ T) :
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
      ((L - u) / L) * (D.card : ℝ) := by
  have hpoint : ∀ b ∈ D,
      surplusProfile T L k (Real.log (b : ℝ)) ≤ (L - u) / L := by
    intro b hb
    have hdata := hD b hb
    have hprofile := surplusProfile_le_one_sub_div_of_mul_le hL
      hdata.1 hdata.2.2.1 hdata.2.2.2
    have hwidth : (L - Real.log (b : ℝ)) / L ≤ (L - u) / L := by
      apply (div_le_div_iff_of_pos_right hL).2
      linarith [hdata.2.1]
    exact hprofile.trans hwidth
  calc
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
        ∑ _b ∈ D, ((L - u) / L) := by
      apply Finset.sum_le_sum
      exact hpoint
    _ = ((L - u) / L) * (D.card : ℝ) := by
      simp [mul_comm]

/- Combining the endpoint-decay factor with the exact integer count gives the finite bound that
the global report argument needs for one logarithmic band.  The analytic input is deliberately
left in the hypotheses: later work only has to provide a suitable finite collection `D` and the
upper logarithmic endpoint `v`. -/
theorem sum_surplusProfile_le_width_mul_floor_band
    (D : Finset ℕ) {T L u v : ℝ} {k : ℕ}
    (hL : 0 < L) (huL : u ≤ L)
    (hD : ∀ b ∈ D,
      b ≠ 0 ∧ 0 ≤ Real.log (b : ℝ) ∧ u < Real.log (b : ℝ) ∧
        Real.log (b : ℝ) ≤ v ∧ Real.log (b : ℝ) ≤ L ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ T) :
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
      ((L - u) / L) *
        ((Nat.floor (Real.exp v) + 1 -
          (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := by
  have hwidth := sum_surplusProfile_le_width_mul_card D hL (by
    intro b hb
    have hdata := hD b hb
    exact ⟨hdata.2.1, hdata.2.2.1, hdata.2.2.2.2.1, hdata.2.2.2.2.2⟩)
  have hcard : D.card ≤
      Nat.floor (Real.exp v) + 1 - (Nat.floor (Real.exp u) + 1) := by
    apply card_le_of_log_band D
    intro b hb
    have hdata := hD b hb
    exact ⟨hdata.1, hdata.2.2.1, hdata.2.2.2.1⟩
  have hcardR : (D.card : ℝ) ≤
      ((Nat.floor (Real.exp v) + 1 -
        (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hnonneg : 0 ≤ (L - u) / L :=
    div_nonneg (sub_nonneg.mpr huL) hL.le
  exact hwidth.trans (mul_le_mul_of_nonneg_left hcardR hnonneg)

/- A floor-free corollary of the finite band estimate.  It is often more convenient for the
global parameter calculation, while the preceding theorem remains the exact integer statement. -/
theorem sum_surplusProfile_le_width_mul_exp_width_add_one
    (D : Finset ℕ) {T L u v : ℝ} {k : ℕ}
    (hL : 0 < L) (huL : u ≤ L) (huv : u ≤ v)
    (hD : ∀ b ∈ D,
      b ≠ 0 ∧ 0 ≤ Real.log (b : ℝ) ∧ u < Real.log (b : ℝ) ∧
        Real.log (b : ℝ) ≤ v ∧ Real.log (b : ℝ) ≤ L ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ T) :
    (∑ b ∈ D, surplusProfile T L k (Real.log (b : ℝ))) ≤
      ((L - u) / L) * (Real.exp v - Real.exp u + 1) := by
  have hfloor := sum_surplusProfile_le_width_mul_floor_band
    D (T := T) (L := L) (u := u) (v := v) (k := k) hL huL hD
  have hcount := floor_log_band_count_le_exp_width_add_one huv
  have hnonneg : 0 ≤ (L - u) / L :=
    div_nonneg (sub_nonneg.mpr huL) hL.le
  exact hfloor.trans (mul_le_mul_of_nonneg_left hcount hnonneg)

/- The preceding generic statement can be instantiated directly on the natural exponent fiber
`surplusBand n L k`.  This adapter discharges the floor-exponent budget and the conversion from
the normalized integer weight to `surplusProfile`; an eventual analytic proof can therefore work
with this theorem without repeating any cast or `Nat.log` bookkeeping. -/
theorem normalized_surplusBand_sum_le_width_mul_floor_band
    {n : ℕ} (hn : n ≠ 0) {L u v : ℝ} (hL : 0 < L) (huL : u ≤ L) (k : ℕ)
    (hband : ∀ b ∈ surplusBand n L k,
      u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v ∧
        Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b) ≤
      ((L - u) / L) *
        ((Nat.floor (Real.exp v) + 1 -
          (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := by
  have hD : ∀ b ∈ surplusBand n L k,
      b ≠ 0 ∧ 0 ≤ Real.log (b : ℝ) ∧ u < Real.log (b : ℝ) ∧
        Real.log (b : ℝ) ≤ v ∧ Real.log (b : ℝ) ≤ L ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
    intro b hb
    have hbI := (mem_surplusBand_iff.mp hb).1
    have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbI).1
    have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
    have hb0 : 0 < b := by omega
    have hblog : 0 ≤ Real.log (b : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
    have hpow : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
    have hpowR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.log_le_log
      (by positivity : 0 < ((b ^ Nat.log b n : ℕ) : ℝ)) hpowR
    rw [show ((b ^ Nat.log b n : ℕ) : ℝ) = (b : ℝ) ^ Nat.log b n by norm_num,
      Real.log_pow] at hlog
    have hka : (Nat.log b n : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [mul_comm] using hlog
    have hk : Nat.log b n = k := (mem_surplusBand_iff.mp hb).2
    have hbk : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [hk] using hka
    have hband' := hband b hb
    exact ⟨by omega, hblog, hband'.1, hband'.2.1, hband'.2.2, hbk⟩
  have hprofile := sum_surplusProfile_le_width_mul_floor_band
    (surplusBand n L k) (T := Real.log (n : ℝ)) (L := L) (u := u) (v := v)
      (k := k) hL huL hD
  calc
    (∑ b ∈ surplusBand n L k, normalizedPositiveSurplus n L b) =
        ∑ b ∈ surplusBand n L k,
          surplusProfile (Real.log (n : ℝ)) L k (Real.log (b : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbI := (mem_surplusBand_iff.mp hb).1
      have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbI).1
      have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
      have hk : Nat.log b n = k := (mem_surplusBand_iff.mp hb).2
      rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2, hk]
    _ ≤ ((L - u) / L) *
        ((Nat.floor (Real.exp v) + 1 -
          (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := hprofile

/- A subset adapter for endpoint-tail filters.  The finite collection need only be contained in
the relevant `Nat.log` fiber; this is the form used when the lower endpoint `A` is imposed by a
separate filter rather than by the whole `surplusBand`. -/
theorem normalized_subset_surplusBand_sum_le_width_mul_floor_band
    {n : ℕ} (hn : n ≠ 0) (D : Finset ℕ) {L u v : ℝ} (hL : 0 < L) (huL : u ≤ L) (k : ℕ)
    (hsub : D ⊆ surplusBand n L k)
    (hband : ∀ b ∈ D,
      u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v ∧
        Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ D, normalizedPositiveSurplus n L b) ≤
      ((L - u) / L) *
        ((Nat.floor (Real.exp v) + 1 -
          (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := by
  have hD : ∀ b ∈ D,
      b ≠ 0 ∧ 0 ≤ Real.log (b : ℝ) ∧ u < Real.log (b : ℝ) ∧
        Real.log (b : ℝ) ≤ v ∧ Real.log (b : ℝ) ≤ L ∧
        (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
    intro b hb
    have hbS := hsub hb
    have hbI := (mem_surplusBand_iff.mp hbS).1
    have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbI).1
    have hblog : 0 ≤ Real.log (b : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
    have hpow : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
    have hpowR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.log_le_log
      (by positivity : 0 < ((b ^ Nat.log b n : ℕ) : ℝ)) hpowR
    rw [show ((b ^ Nat.log b n : ℕ) : ℝ) = (b : ℝ) ^ Nat.log b n by norm_num,
      Real.log_pow] at hlog
    have hka : (Nat.log b n : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [mul_comm] using hlog
    have hk : Nat.log b n = k := (mem_surplusBand_iff.mp hbS).2
    have hbk : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [hk] using hka
    have hband' := hband b hb
    exact ⟨by omega, hblog, hband'.1, hband'.2.1, hband'.2.2, hbk⟩
  have hprofile := sum_surplusProfile_le_width_mul_floor_band
    D (T := Real.log (n : ℝ)) (L := L) (u := u) (v := v) (k := k) hL huL hD
  calc
    (∑ b ∈ D, normalizedPositiveSurplus n L b) =
        ∑ b ∈ D, surplusProfile (Real.log (n : ℝ)) L k (Real.log (b : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbS := hsub hb
      have hbI := (mem_surplusBand_iff.mp hbS).1
      have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbI).1
      have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
      have hk : Nat.log b n = k := (mem_surplusBand_iff.mp hbS).2
      rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2, hk]
    _ ≤ ((L - u) / L) *
        ((Nat.floor (Real.exp v) + 1 -
          (Nat.floor (Real.exp u) + 1) : ℕ) : ℝ) := hprofile

theorem normalized_subset_surplusBand_sum_le_width_mul_exp_width_add_one
    {n : ℕ} (hn : n ≠ 0) (D : Finset ℕ) {L u v : ℝ} {k : ℕ} (hL : 0 < L)
    (huL : u ≤ L) (huv : u ≤ v) (hsub : D ⊆ surplusBand n L k)
    (hband : ∀ b ∈ D,
      u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v ∧
        Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ D, normalizedPositiveSurplus n L b) ≤
      ((L - u) / L) * (Real.exp v - Real.exp u + 1) := by
  have hfloor := normalized_subset_surplusBand_sum_le_width_mul_floor_band
    hn D hL huL k hsub hband
  have hcount := floor_log_band_count_le_exp_width_add_one huv
  have hnonneg : 0 ≤ (L - u) / L :=
    div_nonneg (sub_nonneg.mpr huL) hL.le
  exact hfloor.trans (mul_le_mul_of_nonneg_left hcount hnonneg)

/- The large-base tail used in the report, split by the same exponent fibers as the full base
interval.  The strict floor inequality is chosen so that it is definitionally equivalent to the
integer interval `[floor(exp A)+1, floor(exp L)]`. -/
noncomputable def surplusTailBand (n : ℕ) (A L : ℝ) (k : ℕ) : Finset ℕ :=
  (surplusBand n L k).filter (fun b ↦ Nat.floor (Real.exp A) < b)

noncomputable def positiveSurplusTailBand (n : ℕ) (A L : ℝ) (k : ℕ) : Finset ℕ :=
  (surplusTailBand n A L k).filter
    (fun b ↦ 0 < normalizedPositiveSurplus n L b)

theorem mem_surplusTailBand_iff {n k b : ℕ} {A L : ℝ} :
    b ∈ surplusTailBand n A L k ↔
      b ∈ surplusBand n L k ∧ Nat.floor (Real.exp A) < b := by
  simp [surplusTailBand]

theorem surplusTailBand_subset_surplusBand
    {n : ℕ} {A L : ℝ} (k : ℕ) :
    surplusTailBand n A L k ⊆ surplusBand n L k := by
  intro b hb
  exact (mem_surplusTailBand_iff.mp hb).1

theorem surplusTailBand_zero_empty_of_exp_le
    {n : ℕ} {A L : ℝ} (hExp : Real.exp L ≤ (n : ℝ)) :
    surplusTailBand n A L 0 = ∅ := by
  classical
  apply (Finset.subset_empty).mp
  intro b hb
  have hbsurplus := surplusTailBand_subset_surplusBand 0 hb
  have hbdata := mem_surplusBand_iff.mp hbsurplus
  have hbbase := hbdata.1
  have hb2 : 1 < b := by
    exact lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hbbase).1
  have hfloorR : (Nat.floor (Real.exp L) : ℝ) ≤ Real.exp L :=
    Nat.floor_le (Real.exp_pos L).le
  have hbR : (b : ℝ) ≤ Real.exp L := by
    apply le_trans ?_ hfloorR
    exact_mod_cast (Finset.mem_Icc.mp hbbase).2
  have hbnR : (b : ℝ) ≤ (n : ℝ) := hbR.trans hExp
  have hbn : b ≤ n := by exact_mod_cast hbnR
  have hlogpos : 0 < Nat.log b n := Nat.log_pos hb2 hbn
  have hkzero : Nat.log b n = 0 := hbdata.2
  exact False.elim ((Nat.ne_of_gt hlogpos) hkzero)

theorem positiveSurplusTailBand_zero_empty_of_exp_le
    {n : ℕ} {A L : ℝ} (hExp : Real.exp L ≤ (n : ℝ)) :
    positiveSurplusTailBand n A L 0 = ∅ := by
  unfold positiveSurplusTailBand
  rw [surplusTailBand_zero_empty_of_exp_le hExp]
  simp

theorem positiveSurplusTailBand_subset_surplusTailBand
    {n : ℕ} {A L : ℝ} (k : ℕ) :
    positiveSurplusTailBand n A L k ⊆ surplusTailBand n A L k := by
  intro b hb
  exact (Finset.mem_filter.mp hb).1

/- The positive part of a tail fiber is empty when its endpoint `T/k` lies above `L`.  This is
the fiber-level companion to `surplusProfile_eq_zero_of_endpoint_above`; unlike the whole tail
fiber, only positive surplus terms need to be removed, which is exactly what the normalized sum
uses. -/
theorem positiveSurplusTailBand_empty_of_endpoint_above
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hL2 : 2 ≤ L) (hAhalf : L / 2 ≤ A)
    {k : ℕ} (hk : 0 < k)
    (hTkAbove : (k : ℝ) * L < Real.log (n : ℝ)) :
    positiveSurplusTailBand n A L k = ∅ := by
  apply (Finset.subset_empty).mp
  intro b hb
  have hbposdata := Finset.mem_filter.mp hb
  have hbTail := mem_surplusTailBand_iff.mp hbposdata.1
  have hbBase := mem_surplusBand_iff.mp hbTail.1
  have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbBase.1).1
  have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
  have hb0 : 0 < b := by omega
  have hfloorlt : Nat.floor (Real.exp A) < b := hbTail.2
  have hexpA : Real.exp A < (b : ℝ) :=
    (Nat.floor_lt' (Nat.ne_of_gt hb0)).1 hfloorlt
  have hapos : A ≤ Real.log (b : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast hb0)).2 hexpA.le
  have hfloorR : (Nat.floor (Real.exp L) : ℝ) ≤ Real.exp L :=
    Nat.floor_le (Real.exp_pos L).le
  have hbR : (b : ℝ) ≤ Real.exp L := by
    apply le_trans ?_ hfloorR
    exact_mod_cast (Finset.mem_Icc.mp hbBase.1).2
  have hblogL : Real.log (b : ℝ) ≤ L := by
    have hlogExp := Real.log_le_log (by exact_mod_cast hb0) hbR
    simpa using hlogExp
  have hprofpos : 0 <
      surplusProfile (Real.log (n : ℝ)) L k (Real.log (b : ℝ)) := by
    have hpos := hbposdata.2
    rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2] at hpos
    simpa [hbBase.2] using hpos
  have hzero := surplusProfile_eq_zero_of_endpoint_above
    hL2 (hAhalf.trans hapos) hblogL hk hTkAbove
  rw [hzero] at hprofpos
  exact False.elim (lt_irrefl 0 hprofpos)

theorem normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand
    {n : ℕ} {A L : ℝ} (k : ℕ) :
    (∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b) =
      ∑ b ∈ positiveSurplusTailBand n A L k, normalizedPositiveSurplus n L b := by
  symm
  apply Finset.sum_subset (positiveSurplusTailBand_subset_surplusTailBand k)
  intro b hb hnot
  have hnonneg : 0 ≤ normalizedPositiveSurplus n L b :=
    le_max_right _ _
  exact le_antisymm (not_lt.mp (by
    intro hpos
    exact hnot (Finset.mem_filter.mpr ⟨hb, hpos⟩))) hnonneg

/- On the positive part of a large-base fiber, the endpoint-band support lemma supplies the
canonical choices `u = T/k - log 2/k` and `v = T/k` automatically.  Thus an analytic argument
only needs to estimate the resulting endpoint count; positivity filtering and all arithmetic
bookkeeping are discharged here. -/
theorem positiveSurplusTailBand_sum_le_endpoint_floor_count
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ} (hL : 0 < L) (hAhalf : L / 2 ≤ A)
    (k : ℕ) (hk : 0 < k)
    (hTk : Real.log (n : ℝ) / (k : ℝ) ≤ L) :
    (∑ b ∈ positiveSurplusTailBand n A L k,
        normalizedPositiveSurplus n L b) ≤
      ((L - (Real.log (n : ℝ) / (k : ℝ) - Real.log 2 / (k : ℝ))) / L) *
        ((Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ))) + 1 -
          (Nat.floor (Real.exp ((Real.log (n : ℝ) - Real.log 2) / (k : ℝ))) + 1) : ℕ) : ℝ) := by
  let u : ℝ := Real.log (n : ℝ) / (k : ℝ) - Real.log 2 / (k : ℝ)
  let v : ℝ := Real.log (n : ℝ) / (k : ℝ)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have huv : u ≤ v := by
    dsimp [u, v]
    exact sub_le_self _ (div_nonneg hlog2 hkreal.le)
  have huL : u ≤ L := huv.trans (by simpa [v] using hTk)
  have hsub : positiveSurplusTailBand n A L k ⊆ surplusBand n L k := by
    intro b hb
    exact surplusTailBand_subset_surplusBand k
      (positiveSurplusTailBand_subset_surplusTailBand k hb)
  have hband : ∀ b ∈ positiveSurplusTailBand n A L k,
      u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v ∧
        Real.log (b : ℝ) ≤ L := by
    intro b hb
    have hbposdata := Finset.mem_filter.mp hb
    have hbTail := mem_surplusTailBand_iff.mp hbposdata.1
    have hbBase := mem_surplusBand_iff.mp hbTail.1
    have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbBase.1).1
    have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
    have hb0 : 0 < b := by omega
    have hfloorlt : Nat.floor (Real.exp A) < b := hbTail.2
    have hexpA : Real.exp A < (b : ℝ) :=
      (Nat.floor_lt' (Nat.ne_of_gt hb0)).1 hfloorlt
    have hapos : A ≤ Real.log (b : ℝ) :=
      (Real.le_log_iff_exp_le (by exact_mod_cast hb0)).2 hexpA.le
    have hpow : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
    have hpowR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.log_le_log
      (by positivity : 0 < ((b ^ Nat.log b n : ℕ) : ℝ)) hpowR
    rw [show ((b ^ Nat.log b n : ℕ) : ℝ) = (b : ℝ) ^ Nat.log b n by norm_num,
      Real.log_pow] at hlog
    have hkaNat : (Nat.log b n : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [mul_comm] using hlog
    have hkEq : Nat.log b n = k := hbBase.2
    have hka : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [hkEq] using hkaNat
    have hprofpos : 0 <
        surplusProfile (Real.log (n : ℝ)) L k (Real.log (b : ℝ)) := by
      have hpos := hbposdata.2
      rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2] at hpos
      simpa [hkEq] using hpos
    have hsupport := surplusProfile_pos_mem_band_of_half_le
      hL hAhalf hapos hk hka hprofpos
    have hupper : Real.log (b : ℝ) ≤ v := by
      simpa [v] using hsupport.2
    have hupperL : Real.log (b : ℝ) ≤ L := hupper.trans (by simpa [v] using hTk)
    exact ⟨by simpa [u] using hsupport.1, hupper, hupperL⟩
  have hbound := normalized_subset_surplusBand_sum_le_width_mul_floor_band
    hn (positiveSurplusTailBand n A L k) hL huL k hsub hband
  simpa [u, v, show Real.log (n : ℝ) / (k : ℝ) - Real.log 2 / (k : ℝ) =
    (Real.log (n : ℝ) - Real.log 2) / (k : ℝ) by ring] using hbound

/- Normalized adapter for the sharpened band.  This is the report-shaped interface: after the
   elementary profile lemma above, only the number of integer bases in the shorter interval remains
   to be estimated. -/
theorem positiveSurplusTailBand_sum_le_sharp_endpoint_floor_count
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ} (hL : 0 < L) (hAhalf : L / 2 ≤ A)
    (k : ℕ) (hk : 0 < k) (hT : 4 ≤ Real.log (n : ℝ))
    (hTk : Real.log (n : ℝ) / (k : ℝ) ≤ L) :
    (∑ b ∈ positiveSurplusTailBand n A L k,
        normalizedPositiveSurplus n L b) ≤
      ((L - (Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L) *
        ((Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ))) + 1 -
          (Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ) -
            4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) + 1) : ℕ) : ℝ) := by
  let T : ℝ := Real.log (n : ℝ)
  let r : ℝ := T / (k : ℝ)
  let u : ℝ := r - 4 * (L - r) / T
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hrL : r ≤ L := by simpa [T, r] using hTk
  have huL : u ≤ L := by
    dsimp [u]
    have hD : 0 ≤ L - r := sub_nonneg.mpr hrL
    have : r - 4 * (L - r) / T ≤ r := by
      exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) hD) hTpos.le)
    exact this.trans hrL
  have hsub : positiveSurplusTailBand n A L k ⊆ surplusBand n L k := by
    intro b hb
    exact surplusTailBand_subset_surplusBand k
      (positiveSurplusTailBand_subset_surplusTailBand k hb)
  have hband : ∀ b ∈ positiveSurplusTailBand n A L k,
      u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ r ∧
        Real.log (b : ℝ) ≤ L := by
    intro b hb
    have hbposdata := Finset.mem_filter.mp hb
    have hbTail := mem_surplusTailBand_iff.mp hbposdata.1
    have hbBase := mem_surplusBand_iff.mp hbTail.1
    have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbBase.1).1
    have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
    have hb0 : 0 < b := by omega
    have hfloorlt : Nat.floor (Real.exp A) < b := hbTail.2
    have hexpA : Real.exp A < (b : ℝ) :=
      (Nat.floor_lt' (Nat.ne_of_gt hb0)).1 hfloorlt
    have hapos : A ≤ Real.log (b : ℝ) :=
      (Real.le_log_iff_exp_le (by exact_mod_cast hb0)).2 hexpA.le
    have hpow : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
    have hpowR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.log_le_log
      (by positivity : 0 < ((b ^ Nat.log b n : ℕ) : ℝ)) hpowR
    rw [show ((b ^ Nat.log b n : ℕ) : ℝ) =
      (b : ℝ) ^ Nat.log b n by norm_num, Real.log_pow] at hlog
    have hkaNat : (Nat.log b n : ℝ) * Real.log (b : ℝ) ≤
        Real.log (n : ℝ) := by simpa [mul_comm] using hlog
    have hkEq : Nat.log b n = k := hbBase.2
    have hka : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [hkEq] using hkaNat
    have hprofpos : 0 <
        surplusProfile (Real.log (n : ℝ)) L k (Real.log (b : ℝ)) := by
      have hpos := hbposdata.2
      rw [normalizedPositiveSurplus_eq_surplusProfile hn hb2] at hpos
      simpa [hkEq] using hpos
    have hsupport := surplusProfile_pos_mem_sharp_band
      hT hL hAhalf hapos hk hTk hka hprofpos
    have hupper : Real.log (b : ℝ) ≤ r := by
      simpa [T, r] using hsupport.2
    have hupperL : Real.log (b : ℝ) ≤ L := hupper.trans hrL
    exact ⟨by simpa [T, r, u] using hsupport.1, hupper, hupperL⟩
  have hbound := normalized_subset_surplusBand_sum_le_width_mul_floor_band
    hn (positiveSurplusTailBand n A L k) hL huL k hsub hband
  simpa [T, r, u] using hbound

/- The tail fibers occupy a narrow exponent range.  The lower inequality comes from the strict
   upper side of `Nat.log b n = k` together with `log b ≤ L`; the upper product inequality comes
   from `b^k ≤ n` and the tail condition `exp A < b`.  These are elementary but useful when an
   analytic estimate is summed over `k`, since fibers outside this interval are empty. -/
theorem surplusTailBand_index_bounds
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (_hAL : A ≤ L) (hL : 0 < L)
    {k b : ℕ} (hk : 0 < k)
    (hb : b ∈ surplusTailBand n A L k) :
    Real.log (n : ℝ) / L - 1 < (k : ℝ) ∧
      (k : ℝ) * A < Real.log (n : ℝ) := by
  have hbTail := mem_surplusTailBand_iff.mp hb
  have hbBase := mem_surplusBand_iff.mp hbTail.1
  have hb2nat : 2 ≤ b := (Finset.mem_Icc.mp hbBase.1).1
  have hb2 : 1 < b := lt_of_lt_of_le (by norm_num) hb2nat
  have hb0 : 0 < b := by omega
  have hblog : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast hb2)
  have hblogL : Real.log (b : ℝ) ≤ L := by
    have hupperNat := (Finset.mem_Icc.mp hbBase.1).2
    have hfloorR : (Nat.floor (Real.exp L) : ℝ) ≤ Real.exp L :=
      Nat.floor_le (Real.exp_pos L).le
    have hbR : (b : ℝ) ≤ Real.exp L := by
      apply le_trans ?_ hfloorR
      exact_mod_cast hupperNat
    have hlogExp := Real.log_le_log (by exact_mod_cast hb0) hbR
    simpa using hlogExp
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hpowhi : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb2 n
  have hpowhiR : (n : ℝ) < ((b ^ (Nat.log b n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowhi
  have hloghi := Real.strictMonoOn_log (by positivity : (0 : ℝ) < (n : ℝ))
    (by positivity : (0 : ℝ) < ((b ^ (Nat.log b n + 1) : ℕ) : ℝ)) hpowhiR
  rw [show ((b ^ (Nat.log b n + 1) : ℕ) : ℝ) =
      (b : ℝ) ^ (Nat.log b n + 1) by norm_num, Real.log_pow] at hloghi
  have hkEq : Nat.log b n = k := hbBase.2
  have hloghi' : Real.log (n : ℝ) < ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
    simpa [hkEq, Nat.cast_add, Nat.cast_one, add_mul, mul_comm] using hloghi
  have hloghiL : Real.log (n : ℝ) < ((k + 1 : ℕ) : ℝ) * L := by
    exact hloghi'.trans_le (mul_le_mul_of_nonneg_left hblogL (by positivity))
  have hlower : Real.log (n : ℝ) / L < (k : ℝ) + 1 := by
    exact (div_lt_iff₀ hL).2 (by simpa [Nat.cast_add, Nat.cast_one, add_mul] using hloghiL)
  have hpowlo : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
  have hpowloR : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hpowlo
  have hloglo := Real.log_le_log (by positivity : (0 : ℝ) <
      ((b ^ Nat.log b n : ℕ) : ℝ)) hpowloR
  rw [show ((b ^ Nat.log b n : ℕ) : ℝ) =
      (b : ℝ) ^ Nat.log b n by norm_num, Real.log_pow] at hloglo
  have hloglo' : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
    simpa [hkEq, mul_comm] using hloglo
  have hfloorlt : Nat.floor (Real.exp A) < b := hbTail.2
  have hexpA : Real.exp A < (b : ℝ) :=
    (Nat.floor_lt' (Nat.ne_of_gt hb0)).1 hfloorlt
  have hAlog : A < Real.log (b : ℝ) := by
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hb0)).2 hexpA
  have hApos : 0 < A := by
    exact lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hA
  have hupper : (k : ℝ) * A < Real.log (n : ℝ) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hAlog (by exact_mod_cast hk)) hloglo'
  constructor
  · linarith
  · exact hupper

theorem surplusTailBand_empty_of_index_below
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    {k : ℕ} (hk : 0 < k)
    (hbelow : (k : ℝ) ≤ Real.log (n : ℝ) / L - 1) :
    surplusTailBand n A L k = ∅ := by
  apply (Finset.subset_empty).mp
  intro b hb
  have hidx := surplusTailBand_index_bounds hn hA hAL hL hk hb
  exact False.elim ((not_lt_of_ge hbelow) hidx.1)

theorem surplusTailBand_empty_of_index_above
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    {k : ℕ} (hk : 0 < k)
    (habove : Real.log (n : ℝ) ≤ (k : ℝ) * A) :
    surplusTailBand n A L k = ∅ := by
  apply (Finset.subset_empty).mp
  intro b hb
  have hidx := surplusTailBand_index_bounds hn hA hAL hL hk hb
  exact False.elim ((not_lt_of_ge habove) hidx.2)

/- Every nonempty tail fiber lies in a finite `k` window.  This is the discrete form of the
   report's change of variables: the lower endpoint comes from `log b ≤ L`, while the upper
   endpoint comes from `b^k ≤ n` and `log b > A`.  The theorem is intentionally independent of
   any prime-counting estimate, so later analytic work can sum only over this window. -/
theorem surplusTailBand_index_mem_window
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    {k b : ℕ} (hk : 0 < k)
    (hb : b ∈ surplusTailBand n A L k) :
    k ∈ Finset.Icc
      (Nat.floor (Real.log (n : ℝ) / L - 1) + 1)
      (Nat.floor (Real.log (n : ℝ) / A)) := by
  have hidx := surplusTailBand_index_bounds hn hA hAL hL hk hb
  have hApos : 0 < A :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hA
  apply Finset.mem_Icc.mpr
  constructor
  · have hfloorlt : Nat.floor (Real.log (n : ℝ) / L - 1) < k := by
      exact (Nat.floor_lt' (Nat.ne_of_gt hk)).2 hidx.1
    omega
  · apply Nat.le_floor
    have hkv : (k : ℝ) < Real.log (n : ℝ) / A := by
      apply (lt_div_iff₀ hApos).2
      simpa [mul_comm] using hidx.2
    exact le_of_lt hkv

theorem surplusTailBand_empty_of_index_outside_window
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hExp : Real.exp L ≤ (n : ℝ)) {k : ℕ}
    (hknot : k ∉ Finset.Icc
      (Nat.floor (Real.log (n : ℝ) / L - 1) + 1)
      (Nat.floor (Real.log (n : ℝ) / A))) :
    surplusTailBand n A L k = ∅ := by
  classical
  by_cases hk0 : k = 0
  · subst k
    exact surplusTailBand_zero_empty_of_exp_le hExp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hidx : k < Nat.floor (Real.log (n : ℝ) / L - 1) + 1 ∨
        Nat.floor (Real.log (n : ℝ) / A) < k := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hknot
    by_cases hbelow : k < Nat.floor (Real.log (n : ℝ) / L - 1) + 1
    · have hkfloor : k ≤ Nat.floor (Real.log (n : ℝ) / L - 1) := by omega
      have hfloorpos : 0 < Nat.floor (Real.log (n : ℝ) / L - 1) :=
        lt_of_lt_of_le hkpos hkfloor
      have hxnonneg : 0 ≤ Real.log (n : ℝ) / L - 1 :=
        (Nat.pos_of_floor_pos hfloorpos).le
      have hbelowR : (k : ℝ) ≤ Real.log (n : ℝ) / L - 1 := by
        exact le_trans (by exact_mod_cast hkfloor) (Nat.floor_le hxnonneg)
      exact surplusTailBand_empty_of_index_below hn hA hAL hL hkpos hbelowR
    · have habove : Nat.floor (Real.log (n : ℝ) / A) < k := by
        exact hidx.resolve_left (by omega)
      have hApos : 0 < A :=
        lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hA
      have hupperR : Real.log (n : ℝ) / A < (k : ℝ) := by
        calc
          Real.log (n : ℝ) / A <
              (Nat.floor (Real.log (n : ℝ) / A) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          _ ≤ (k : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt habove)
      have hupperMul : Real.log (n : ℝ) < (k : ℝ) * A := by
        exact (div_lt_iff₀ hApos).mp hupperR
      exact surplusTailBand_empty_of_index_above hn hA hAL hL hkpos hupperMul.le

theorem tail_interval_eq_biUnion_surplusTailBand
    {n : ℕ} {A L : ℝ} (hA : Real.log 2 ≤ A) (hAL : A ≤ L) :
    Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)) =
      (Finset.range (n + 1)).biUnion (fun k ↦ surplusTailBand n A L k) := by
  classical
  have hfloorA : 2 ≤ Nat.floor (Real.exp A) := by
    apply Nat.le_floor
    have htwo : (2 : ℝ) ≤ Real.exp A := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hA
    exact htwo
  have hfloorle : Nat.floor (Real.exp A) ≤ Nat.floor (Real.exp L) := by
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr hAL
  ext b
  constructor
  · intro hb
    have hbI := Finset.mem_Icc.mp hb
    have hbbase : b ∈ Finset.Icc 2 (Nat.floor (Real.exp L)) := by
      exact Finset.mem_Icc.mpr ⟨hfloorA.trans (Nat.le_succ _)
        |>.trans hbI.1, hbI.2⟩
    have hlog : Nat.log b n ≤ n := Nat.log_le_self b n
    refine Finset.mem_biUnion.mpr ⟨Nat.log b n,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hlog), ?_⟩
    exact mem_surplusTailBand_iff.mpr ⟨
      mem_surplusBand_iff.mpr ⟨hbbase, rfl⟩, by omega⟩
  · intro hb
    obtain ⟨k, hk, hbk⟩ := Finset.mem_biUnion.mp hb
    have htail := mem_surplusTailBand_iff.mp hbk
    have hbbaseI : b ∈ Finset.Icc 2 (Nat.floor (Real.exp L)) :=
      (mem_surplusBand_iff.mp htail.1).1
    have hbbase := Finset.mem_Icc.mp hbbaseI
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hbbase.2⟩

theorem surplus_tail_sum_eq_sum_surplusTailBands
    {n : ℕ} {A L : ℝ} (hA : Real.log 2 ≤ A) (hAL : A ≤ L) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) =
      ∑ k ∈ Finset.range (n + 1),
        ∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b := by
  classical
  have hdisj : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      i ≠ j → Disjoint (surplusTailBand n A L i) (surplusTailBand n A L j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro b hbi hbj
    have hki := (mem_surplusBand_iff.mp
      (surplusTailBand_subset_surplusBand i hbi)).2
    have hkj := (mem_surplusBand_iff.mp
      (surplusTailBand_subset_surplusBand j hbj)).2
    exact hij (hki.symm.trans hkj)
  rw [tail_interval_eq_biUnion_surplusTailBand hA hAL]
  exact Finset.sum_biUnion hdisj

/- The finite-window aggregation interface.  An analytic proof may choose any finite index set
   `K`; it only has to show that fibers outside `K` are empty and estimate the logarithmic width
   on fibers inside `K`.  This avoids carrying the ambient `range (n+1)` through the report's
   final finite summation. -/
theorem normalized_surplus_tail_sum_le_of_width_exp_bounds_on_index_set
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (K : Finset ℕ)
    (hKsub : K ⊆ Finset.range (n + 1))
    (hKsupport : ∀ k ∈ Finset.range (n + 1), k ∉ K →
      surplusTailBand n A L k = ∅)
    (u v : ℕ → ℝ)
    (hparams : ∀ k ∈ K, u k ≤ L ∧ u k ≤ v k)
    (hband : ∀ k ∈ K, ∀ b ∈ surplusTailBand n A L k,
      u k < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v k ∧
        Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ K, ((L - u k) / L) * (Real.exp (v k) - Real.exp (u k) + 1) := by
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  let g : ℕ → ℝ := fun k ↦
    ∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b
  have heq : (∑ k ∈ Finset.range (n + 1), g k) = ∑ k ∈ K, g k := by
    symm
    apply Finset.sum_subset hKsub
    intro k hk hkn
    dsimp [g]
    rw [hKsupport k hk hkn]
    simp
  rw [heq]
  apply Finset.sum_le_sum
  intro k hk
  have hpar := hparams k hk
  have hsub : surplusTailBand n A L k ⊆ surplusBand n L k :=
    surplusTailBand_subset_surplusBand k
  have hband' := hband k hk
  simpa [g] using
    (normalized_subset_surplusBand_sum_le_width_mul_exp_width_add_one
      hn (surplusTailBand n A L k) hL hpar.1 hpar.2 hsub hband')

/- Concrete report-shaped specialization.  The finite index set is the natural-number window
   `T/L - 1 < k ≤ T/A`; the preceding support lemma proves that every omitted fiber is empty.
   Thus the remaining analytic obligation is exactly a finite exponential-width sum on this
   window, with no ambient `range (n+1)` terms left over. -/
theorem normalized_surplus_tail_sum_le_of_width_exp_bounds_on_natural_window
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hExp : Real.exp L ≤ (n : ℝ))
    (u v : ℕ → ℝ)
    (hparams : ∀ k ∈ (Finset.range (n + 1)).filter (fun j ↦
        Nat.floor (Real.log (n : ℝ) / L - 1) + 1 ≤ j ∧
          j ≤ Nat.floor (Real.log (n : ℝ) / A)),
      u k ≤ L ∧ u k ≤ v k)
    (hband : ∀ k ∈ (Finset.range (n + 1)).filter (fun j ↦
        Nat.floor (Real.log (n : ℝ) / L - 1) + 1 ≤ j ∧
          j ≤ Nat.floor (Real.log (n : ℝ) / A)),
      ∀ b ∈ surplusTailBand n A L k,
        u k < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v k ∧
          Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ (Finset.range (n + 1)).filter (fun j ↦
        Nat.floor (Real.log (n : ℝ) / L - 1) + 1 ≤ j ∧
          j ≤ Nat.floor (Real.log (n : ℝ) / A)),
        ((L - u k) / L) * (Real.exp (v k) - Real.exp (u k) + 1) := by
  let K : Finset ℕ := (Finset.range (n + 1)).filter (fun j ↦
    Nat.floor (Real.log (n : ℝ) / L - 1) + 1 ≤ j ∧
      j ≤ Nat.floor (Real.log (n : ℝ) / A))
  have hKsub : K ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_filter.mp hk |>.1
  have hKsupport : ∀ k ∈ Finset.range (n + 1), k ∉ K →
      surplusTailBand n A L k = ∅ := by
    intro k hk hkn
    apply surplusTailBand_empty_of_index_outside_window hn hA hAL hL hExp
    intro hwindow
    apply hkn
    exact Finset.mem_filter.mpr ⟨hk, Finset.mem_Icc.mp hwindow⟩
  have h := normalized_surplus_tail_sum_le_of_width_exp_bounds_on_index_set
    hn hA hAL hL K hKsub hKsupport u v hparams hband
  simpa [K] using h

/- Sharp-width aggregation with support stated only for the positive-surplus fibers.  The whole
tail fiber may contain bases whose normalized surplus is zero, so requiring those fibers themselves
to be empty is unnecessarily strong.  This version first replaces each fiber sum by its positive
part, then removes positive fibers outside `K`, and finally applies the sharp endpoint estimate. -/
theorem normalized_surplus_tail_sum_le_of_sharp_exp_width_bounds_on_index_set
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAhalf : L / 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hT : 4 ≤ Real.log (n : ℝ)) (hExp : Real.exp L ≤ (n : ℝ))
    (K : Finset ℕ) (hKsub : K ⊆ Finset.range (n + 1))
    (hKsupport : ∀ k ∈ Finset.range (n + 1), k ∉ K →
      positiveSurplusTailBand n A L k = ∅)
    (C : ℕ → ℝ) (hC0 : 0 ≤ C 0)
    (hC : ∀ k ∈ K, 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ L ∧
      ((L - (Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L) *
        (Real.exp (Real.log (n : ℝ) / (k : ℝ)) -
          Real.exp (Real.log (n : ℝ) / (k : ℝ) -
            4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ)) + 1) ≤ C k) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ K, C k := by
  classical
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  let g : ℕ → ℝ := fun k ↦
    ∑ b ∈ positiveSurplusTailBand n A L k, normalizedPositiveSurplus n L b
  have hfiber : ∀ k : ℕ,
      (∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b) = g k := by
    intro k
    simpa [g] using (normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand k)
  have hreplace :
      (∑ k ∈ Finset.range (n + 1),
        ∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b) =
        ∑ k ∈ Finset.range (n + 1), g k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hfiber k
  rw [hreplace]
  have hsum : (∑ k ∈ Finset.range (n + 1), g k) = ∑ k ∈ K, g k := by
    symm
    apply Finset.sum_subset hKsub
    intro k hk hkn
    dsimp [g]
    rw [hKsupport k hk hkn]
    simp
  rw [hsum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    dsimp [g]
    rw [positiveSurplusTailBand_zero_empty_of_exp_le hExp]
    simpa using hC0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hdata := hC k hk hkpos
    have hTk := hdata.1
    rw [show g k =
        ∑ b ∈ positiveSurplusTailBand n A L k,
          normalizedPositiveSurplus n L b by rfl]
    have hband := positiveSurplusTailBand_sum_le_sharp_endpoint_floor_count
      hn hL hAhalf k hkpos hT hTk
    have hTpos : 0 < Real.log (n : ℝ) :=
      lt_of_lt_of_le (by norm_num) hT
    have hcorr : 0 ≤
        4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ) := by
      exact div_nonneg (mul_nonneg (by norm_num)
        (sub_nonneg.mpr hTk)) hTpos.le
    have huv :
        Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ) ≤
        Real.log (n : ℝ) / (k : ℝ) := by
      linarith
    have hcount := floor_log_band_count_le_exp_width_add_one huv
    have hcoef : 0 ≤
        (L - (Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L := by
      exact div_nonneg (sub_nonneg.mpr (by linarith)) hL.le
    have hmul := mul_le_mul_of_nonneg_left hcount hcoef
    exact hband.trans (hmul.trans hdata.2)

/- Concrete report adapter for the preceding positive-fiber aggregation.  The lower endpoint of
the index set is expressed as `T ≤ kL` rather than by a floor, so the possible one-step boundary
fiber is handled exactly by `positiveSurplusTailBand_empty_of_endpoint_above`.  The remaining
certificate is the finite width sum on this explicit natural-number window. -/
theorem normalized_surplus_tail_sum_le_of_report_sharp_width_certificate
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 4 ≤ T) (hlogn : Real.log (n : ℝ) = T)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hAhalf : (v + Real.log v) / 2 ≤ v - 3 * Real.log v)
    (hAL : v - 3 * Real.log v ≤ v + Real.log v)
    (hL : 0 < v + Real.log v) (hL2 : 2 ≤ v + Real.log v)
    (hExp : Real.exp (v + Real.log v) ≤ (n : ℝ))
    (hwindow :
      (∑ k ∈ (Finset.range (n + 1)).filter (fun j : ℕ ↦
        0 < j ∧ T ≤ (j : ℝ) * (v + Real.log v) ∧
          (j : ℝ) * (v - 3 * Real.log v) < T),
        ((v + Real.log v) -
            (T / (k : ℝ) -
              4 * ((v + Real.log v) - T / (k : ℝ)) / T)) /
          (v + Real.log v) *
          (Real.exp (T / (k : ℝ)) -
            Real.exp (T / (k : ℝ) -
              4 * ((v + Real.log v) - T / (k : ℝ)) / T) + 1)) ≤
        24 * T / v ^ 2) :
    (∑ p ∈ Finset.Icc
        (⌊Real.exp (v - 3 * Real.log v)⌋₊ + 1)
        (⌊Real.exp (v + Real.log v)⌋₊),
        normalizedPositiveSurplus n (v + Real.log v) p) ≤
      24 * T / v ^ 2 := by
  let K : Finset ℕ := (Finset.range (n + 1)).filter (fun j : ℕ ↦
    0 < j ∧ T ≤ (j : ℝ) * (v + Real.log v) ∧
      (j : ℝ) * (v - 3 * Real.log v) < T)
  let C : ℕ → ℝ := fun k ↦
    ((v + Real.log v) -
        (T / (k : ℝ) -
          4 * ((v + Real.log v) - T / (k : ℝ)) / T)) /
      (v + Real.log v) *
      (Real.exp (T / (k : ℝ)) -
        Real.exp (T / (k : ℝ) -
          4 * ((v + Real.log v) - T / (k : ℝ)) / T) + 1)
  have hKsub : K ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_filter.mp hk |>.1
  have hKsupport : ∀ k ∈ Finset.range (n + 1), k ∉ K →
      positiveSurplusTailBand n (v - 3 * Real.log v) (v + Real.log v) k = ∅ := by
    intro k hk hkn
    by_cases hk0 : k = 0
    · subst k
      exact positiveSurplusTailBand_zero_empty_of_exp_le hExp
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hlower : T ≤ (k : ℝ) * (v + Real.log v)
    · by_cases hupper : (k : ℝ) * (v - 3 * Real.log v) < T
      · exact False.elim (hkn (Finset.mem_filter.mpr ⟨hk, hkpos, hlower, hupper⟩))
      · have habove : T ≤ (k : ℝ) * (v - 3 * Real.log v) := le_of_not_gt hupper
        have hempty := surplusTailBand_empty_of_index_above hn hA hAL hL hkpos
          (by simpa [hlogn] using habove)
        unfold positiveSurplusTailBand
        rw [hempty]
        simp
    · have hTkAbove : (k : ℝ) * (v + Real.log v) < T := lt_of_not_ge hlower
      exact positiveSurplusTailBand_empty_of_endpoint_above
        hn hL2 hAhalf hkpos (by simpa [hlogn] using hTkAbove)
  have hC0 : 0 ≤ C 0 := by
    dsimp [C]
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hfrac : 0 ≤ 4 * (v + Real.log v) / T := by
      exact div_nonneg (mul_nonneg (by norm_num)
        (by linarith [hL])) hTpos.le
    have hcoef : 0 ≤
        ((v + Real.log v) + 4 * (v + Real.log v) / T) /
          (v + Real.log v) := by
      exact div_nonneg (by linarith [hL]) hL.le
    have hexp : Real.exp (-(4 * (v + Real.log v) / T)) ≤ 1 := by
      have hneg : -(4 * (v + Real.log v) / T) ≤ 0 := by
        exact neg_nonpos.mpr (div_nonneg (by positivity) hTpos.le)
      exact (Real.exp_le_exp.mpr hneg).trans_eq (by norm_num)
    have hwidth : 0 ≤ Real.exp 0 -
        Real.exp (-(4 * (v + Real.log v) / T)) + 1 := by
      norm_num
      linarith
    simpa [C] using mul_nonneg hcoef hwidth
  have hC : ∀ k ∈ K, 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ v + Real.log v ∧
      ((v + Real.log v) - (Real.log (n : ℝ) / (k : ℝ) -
          4 * ((v + Real.log v) - Real.log (n : ℝ) / (k : ℝ)) /
            Real.log (n : ℝ))) / (v + Real.log v) *
        (Real.exp (Real.log (n : ℝ) / (k : ℝ)) -
          Real.exp (Real.log (n : ℝ) / (k : ℝ) -
            4 * ((v + Real.log v) - Real.log (n : ℝ) / (k : ℝ)) /
              Real.log (n : ℝ)) + 1) ≤ C k := by
    intro k hk hkpos
    have hmem := Finset.mem_filter.mp hk
    constructor
    · rw [hlogn]
      exact (div_le_iff₀ (by exact_mod_cast hkpos)).2 (by
        simpa [mul_comm] using hmem.2.2.1)
    · dsimp [C]
      rw [hlogn]
  have h := normalized_surplus_tail_sum_le_of_sharp_exp_width_bounds_on_index_set
    hn hA hAhalf hAL hL (by simpa [hlogn] using hT) hExp K hKsub hKsupport C hC0 hC
  exact h.trans (by simpa [K, C, hlogn] using hwindow)

/- Global sharpened endpoint interface.  The caller supplies only the analytic estimate for the
   short floor interval in each nonzero fiber; all disjointness, the zero fiber, and the conversion
   to the full normalized prime-power tail are automatic. -/
theorem normalized_surplus_tail_sum_le_of_sharp_endpoint_floor_counts
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAhalf : L / 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hT : 4 ≤ Real.log (n : ℝ)) (hExp : Real.exp L ≤ (n : ℝ))
    (C : ℕ → ℝ) (hC0 : 0 ≤ C 0)
    (hC : ∀ k ∈ Finset.range (n + 1), 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ L ∧
      ((L - (Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L) *
        ((Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ))) + 1 -
          (Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ) -
            4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) + 1) : ℕ) : ℝ) ≤ C k) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ Finset.range (n + 1), C k := by
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  gcongr with k hk
  by_cases hk0 : k = 0
  · subst k
    rw [normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand 0]
    rw [positiveSurplusTailBand_zero_empty_of_exp_le hExp]
    simpa using hC0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hdata := hC k hk hkpos
    rw [normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand k]
    exact (positiveSurplusTailBand_sum_le_sharp_endpoint_floor_count
      hn hL hAhalf k hkpos hT hdata.1).trans hdata.2

/- The same global endpoint estimate with the floor-count hypothesis already replaced by the
   corresponding real exponential width.  This is the convenient interface for the analytic
   Track-C calculation: all floor arithmetic is discharged here, while the caller only supplies
   a bound for the finite sum of the displayed widths. -/
theorem normalized_surplus_tail_sum_le_of_sharp_exp_width_bounds
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAhalf : L / 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hT : 4 ≤ Real.log (n : ℝ)) (hExp : Real.exp L ≤ (n : ℝ))
    (C : ℕ → ℝ) (hC0 : 0 ≤ C 0)
    (hC : ∀ k ∈ Finset.range (n + 1), 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ L ∧
      ((L - (Real.log (n : ℝ) / (k : ℝ) -
          4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L) *
        (Real.exp (Real.log (n : ℝ) / (k : ℝ)) -
          Real.exp (Real.log (n : ℝ) / (k : ℝ) -
            4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ)) + 1) ≤ C k) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ Finset.range (n + 1), C k := by
  apply normalized_surplus_tail_sum_le_of_sharp_endpoint_floor_counts
    hn hA hAhalf hAL hL hT hExp C hC0
  intro k hk hkpos
  have hdata := hC k hk hkpos
  have hTk := hdata.1
  have hTpos : 0 < Real.log (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) hT
  have hcorr : 0 ≤
      4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr hTk)) hTpos.le
  have huL :
      Real.log (n : ℝ) / (k : ℝ) -
        4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ) ≤ L := by
    linarith
  have hcoef : 0 ≤
      (L - (Real.log (n : ℝ) / (k : ℝ) -
        4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ))) / L := by
    exact div_nonneg (sub_nonneg.mpr huL) hL.le
  have huv :
      Real.log (n : ℝ) / (k : ℝ) -
        4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ) ≤
      Real.log (n : ℝ) / (k : ℝ) := by
    linarith
  have hcount := floor_log_band_count_le_exp_width_add_one huv
  have hmul := mul_le_mul_of_nonneg_left hcount hcoef
  exact ⟨hTk, hmul.trans hdata.2⟩

/- The sharp endpoint coefficient has a uniform elementary simplification.  Writing
`r = T/k`, the numerator is `(L-r) * (1 + 4/T)`, hence it is at most `2*(L-r)` once
`T≥4`.  This is the useful first reduction when the remaining width sum is estimated over all
exponent fibers. -/
theorem report_sharp_width_coefficient_le_two
    {T L r : ℝ} (hT : 4 ≤ T) (hL : 0 < L) (hrL : r ≤ L) :
    (L - (r - 4 * (L - r) / T)) / L ≤ 2 * (L - r) / L := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hdiff : 0 ≤ L - r := sub_nonneg.mpr hrL
  have hfrac : 4 / T ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hTpos).2
    nlinarith
  have hfac : 1 + 4 / T ≤ (2 : ℝ) := by linarith
  have hmul : (L - r) * (1 + 4 / T) ≤ (L - r) * 2 :=
    mul_le_mul_of_nonneg_left hfac hdiff
  have hrewrite : L - (r - 4 * (L - r) / T) =
      (L - r) * (1 + 4 / T) := by ring
  rw [hrewrite]
  calc
    (L - r) * (1 + 4 / T) / L ≤ (L - r) * 2 / L :=
      div_le_div_of_nonneg_right hmul hL.le
    _ = 2 * (L - r) / L := by ring

/- The exponential width itself admits a derivative-free first-order bound.  This is the
elementary inequality used to expose the decisive `(L-r)` decay without invoking a mean-value
theorem: `1-exp(-d) ≤ d` follows from `1-d ≤ exp(-d)`. -/
theorem exp_sub_width_le_exp_mul
    {r d : ℝ} (_hd : 0 ≤ d) :
    Real.exp r - Real.exp (r - d) ≤ Real.exp r * d := by
  have hlin : 1 - d ≤ Real.exp (-d) := by
    simpa [sub_eq_add_neg, add_comm] using (Real.add_one_le_exp (-d))
  have hexp0 : 0 ≤ Real.exp r := (Real.exp_pos r).le
  have hmul : Real.exp r * (1 - d) ≤ Real.exp r * Real.exp (-d) :=
    mul_le_mul_of_nonneg_left hlin hexp0
  have hexp_sub : Real.exp (r - d) = Real.exp r * Real.exp (-d) := by
    rw [show r - d = r + (-d) by ring, Real.exp_add]
  rw [hexp_sub]
  nlinarith

/- A derivative-free polynomial/exponential envelope.  Writing `g² exp(-g)` as three factors
   of `exp(-g/3)` and applying the global bound `y exp(-y) ≤ exp(-1)` at `y=g/3` leaves a
   single decaying exponential while retaining the exact coefficient `9 exp(-2)`. -/
theorem sq_exp_neg_three_bound {g : ℝ} (hg : 0 ≤ g) :
    g ^ 2 * Real.exp (-g) ≤ 9 * Real.exp (-2) * Real.exp (-g / 3) := by
  have hbase := Real.mul_exp_neg_le_exp_neg_one (g / 3)
  have hfirst : g * Real.exp (-g / 3) ≤ 3 * Real.exp (-1) := by
    have heq : -(g / 3) = -g / 3 := by ring
    rw [heq] at hbase
    nlinarith
  have hprod : 0 ≤ g * Real.exp (-g / 3) :=
    mul_nonneg hg (Real.exp_pos _).le
  have hcoeff : 0 ≤ 3 * Real.exp (-1) := by positivity
  have hsq : (g * Real.exp (-g / 3)) ^ 2 ≤
      (3 * Real.exp (-1)) ^ 2 :=
    (sq_le_sq₀ hprod hcoeff).2 hfirst
  have hexp3 : Real.exp (-g / 3) * Real.exp (-g / 3) * Real.exp (-g / 3) =
      Real.exp (-g) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hsq' : g ^ 2 * Real.exp (-g) ≤
      (3 * Real.exp (-1)) ^ 2 * Real.exp (-g / 3) := by
    have hmul := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-g / 3)).le
    have hrewrite : (g * Real.exp (-g / 3)) ^ 2 * Real.exp (-g / 3) =
        g ^ 2 * Real.exp (-g) := by
      rw [pow_two]
      calc
        (g * Real.exp (-g / 3)) * (g * Real.exp (-g / 3)) * Real.exp (-g / 3) =
            g ^ 2 * (Real.exp (-g / 3) * Real.exp (-g / 3) *
              Real.exp (-g / 3)) := by ring
        _ = g ^ 2 * Real.exp (-g) := by rw [hexp3]
    rw [hrewrite] at hmul
    exact hmul
  have hcoeffeq : (3 * Real.exp (-1)) ^ 2 = 9 * Real.exp (-2) := by
    rw [pow_two]
    calc
      3 * Real.exp (-1) * (3 * Real.exp (-1)) =
          9 * (Real.exp (-1) * Real.exp (-1)) := by ring
      _ = 9 * Real.exp (-2) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  rw [hcoeffeq] at hsq'
  exact hsq'

/- The geometric denominator has an elementary reciprocal bound.  This is the safe form of
   `1/(1-exp(-x)) ~ 1/x`, obtained only from `1+x ≤ exp x`; it is useful for converting the
   geometric reduction into an explicit reciprocal-index estimate. -/
theorem inv_one_sub_exp_neg_le_one_add_inv {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + 1 / x := by
  have h1x : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le h1x hexp)
  have hden : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    calc
      x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
      _ ≤ 1 - (Real.exp x)⁻¹ := by linarith
      _ = 1 - Real.exp (-x) := by rw [Real.exp_neg]
  have hratio : 0 < x / (1 + x) := div_pos hx h1x
  have hdenpos : 0 < 1 - Real.exp (-x) := lt_of_lt_of_le hratio hden
  have hinvden : (1 - Real.exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ :=
    (inv_le_inv₀ hdenpos hratio).2 hden
  calc
    (1 - Real.exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ := hinvden
    _ = 1 + 1 / x := by field_simp; ring

/- If the gap at index `k` grows at least linearly from a base index `k₀`, the quadratic
   exponential gap sum is dominated by a geometric series.  This is the reusable discrete
   estimate needed to turn the report's window into an explicit `T/v²` bound; the caller still
   has to prove the concrete reciprocal-index growth and simplify the geometric denominator. -/
theorem sum_exp_gap_sq_le_geometric
    {T L c : ℝ} (K : Finset ℕ) (k₀ : ℕ)
    (hc : 0 < c)
    (hK : ∀ k ∈ K, k₀ ≤ k)
    (hgap : ∀ k ∈ K, 0 ≤ L - T / (k : ℝ))
    (hlin : ∀ k ∈ K, c * ((k - k₀ : ℕ) : ℝ) ≤ L - T / (k : ℝ)) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      9 * Real.exp (-2) * Real.exp L * (1 - Real.exp (-c / 3))⁻¹ := by
  let q : ℝ := Real.exp (-c / 3)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact (Real.exp_lt_exp).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ ↦ q ^ j) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hgeom' : Summable (fun j : ℕ ↦
      (9 * Real.exp (-2) * Real.exp L) * q ^ j) :=
    hgeom.mul_left (9 * Real.exp (-2) * Real.exp L)
  let J : Finset ℕ := K.image (fun k ↦ k - k₀)
  have hinj : Set.InjOn (fun k : ℕ ↦ k - k₀) (K : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hK a ha
    have hb' := hK b hb
    have hae : a - k₀ + k₀ = a := Nat.sub_add_cancel ha'
    have hbe : b - k₀ + k₀ = b := Nat.sub_add_cancel hb'
    change a - k₀ = b - k₀ at hab
    calc
      a = a - k₀ + k₀ := hae.symm
      _ = b - k₀ + k₀ := by rw [hab]
      _ = b := hbe
  have hsum :
      (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
        ∑ k ∈ K, (9 * Real.exp (-2) * Real.exp L) * q ^ (k - k₀) := by
    apply Finset.sum_le_sum
    intro k hk
    have hg := hgap k hk
    have hl := hlin k hk
    have harg : -(L - T / (k : ℝ)) / 3 ≤
        -(c * ((k - k₀ : ℕ) : ℝ)) / 3 := by
      linarith
    have hexp : Real.exp (-(L - T / (k : ℝ)) / 3) ≤
        Real.exp (-(c * ((k - k₀ : ℕ) : ℝ)) / 3) :=
      (Real.exp_le_exp).2 harg
    have hargq : -(c * ((k - k₀ : ℕ) : ℝ)) / 3 =
        ((k - k₀ : ℕ) : ℝ) * (-c / 3) := by ring
    have hpow : Real.exp (-(c * ((k - k₀ : ℕ) : ℝ)) / 3) =
        q ^ (k - k₀) := by
      rw [hargq]
      dsimp [q]
      exact Real.exp_nat_mul (-c / 3) (k - k₀)
    have hpoly := sq_exp_neg_three_bound hg
    have hterm : Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2 ≤
        9 * Real.exp (-2) * Real.exp L *
          Real.exp (-(L - T / (k : ℝ)) / 3) := by
      have hendpoint : Real.exp (T / (k : ℝ)) =
          Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by
        have harg : T / (k : ℝ) = L + (-(L - T / (k : ℝ))) := by ring
        calc
          Real.exp (T / (k : ℝ)) =
              Real.exp (L + (-(L - T / (k : ℝ)))) := congrArg Real.exp harg
          _ = Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by rw [Real.exp_add]
      rw [hendpoint]
      have hL0 : 0 ≤ Real.exp L := (Real.exp_pos L).le
      have hm := mul_le_mul_of_nonneg_left hpoly hL0
      nlinarith [hm]
    have hterm' := hterm.trans
      (mul_le_mul_of_nonneg_left hexp (by positivity))
    rw [hpow] at hterm'
    exact hterm'
  have hsumJ :
      (∑ k ∈ K, (9 * Real.exp (-2) * Real.exp L) * q ^ (k - k₀)) =
        ∑ j ∈ J, (9 * Real.exp (-2) * Real.exp L) * q ^ j := by
    dsimp [J]
    symm
    exact Finset.sum_image hinj
  have htsum := Summable.sum_le_tsum J (fun j hj ↦ by positivity) hgeom'
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at htsum
  calc
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
        ∑ k ∈ K, (9 * Real.exp (-2) * Real.exp L) * q ^ (k - k₀) := hsum
    _ = ∑ j ∈ J, (9 * Real.exp (-2) * Real.exp L) * q ^ j := hsumJ
    _ ≤ 9 * Real.exp (-2) * Real.exp L * (1 - q)⁻¹ := htsum
    _ = 9 * Real.exp (-2) * Real.exp L *
        (1 - Real.exp (-c / 3))⁻¹ := by rfl

/- A weighted geometric kernel.  The elementary inequality
`(j+1)^2 ≤ 2 * choose (j+2) 2` lets us use Mathlib's closed form for the
binomially weighted geometric series without proving a separate power-series identity. -/
theorem sum_succ_sq_mul_geometric_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J : Finset ℕ) :
    (∑ j ∈ J, (((j : ℝ) + 1) ^ 2) * q ^ j) ≤
      2 * (1 - q)⁻¹ ^ 3 := by
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hsum :
      (∑ j ∈ J, (((j : ℝ) + 1) ^ 2) * q ^ j) ≤
        ∑ j ∈ J, (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j := by
    have hchoose_all : ∀ j : ℕ, (j + 1) ^ 2 ≤ 2 * (j + 2).choose 2 := by
      intro j
      induction j with
      | zero => norm_num
      | succ j ih =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          nlinarith
    apply Finset.sum_le_sum
    intro j hj
    have hchoose := hchoose_all j
    have hqpow : 0 ≤ q ^ j := by positivity
    have hchooseR : (((j : ℝ) + 1) ^ 2) ≤
        (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    exact mul_le_mul_of_nonneg_right hchooseR hqpow
  have hgeom : Summable (fun j : ℕ ↦
      (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one 2 hqnorm)
  have htsum := Summable.sum_le_tsum J
    (fun j hj ↦ by positivity) hgeom
  have hclosed := tsum_choose_mul_geometric_of_norm_lt_one 2 hqnorm
  calc
    (∑ j ∈ J, (((j : ℝ) + 1) ^ 2) * q ^ j) ≤
        ∑ j ∈ J, (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j := hsum
    _ = 2 * (∑ j ∈ J, (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 2 * (∑' j : ℕ, (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
      gcongr
    _ = 2 * (1 - q)⁻¹ ^ 3 := by
      rw [hclosed]
      have hqne : 1 - q ≠ 0 := by linarith
      field_simp [hqne]

theorem tsum_succ_sq_mul_geometric_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, (((j : ℝ) + 1) ^ 2) * q ^ j) ≤
      2 * (1 - q)⁻¹ ^ 3 := by
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ ↦
      (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one 2 hqnorm)
  have hle : ∀ j : ℕ,
      (((j : ℝ) + 1) ^ 2) * q ^ j ≤
        (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j := by
    intro j
    have hchoose : (j + 1) ^ 2 ≤ 2 * (j + 2).choose 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          nlinarith
    have hchooseR : (((j : ℝ) + 1) ^ 2) ≤
        (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    exact mul_le_mul_of_nonneg_right hchooseR (by positivity)
  have hmajor : Summable (fun j : ℕ ↦
      (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
    simpa [mul_assoc] using hgeom.mul_left (2 : ℝ)
  have hweighted : Summable (fun j : ℕ ↦
      (((j : ℝ) + 1) ^ 2) * q ^ j) :=
    Summable.of_nonneg_of_le (fun j ↦ by positivity) hle hmajor
  have htsum := hweighted.tsum_le_tsum hle hmajor
  have hclosed := tsum_choose_mul_geometric_of_norm_lt_one 2 hqnorm
  calc
    (∑' j : ℕ, (((j : ℝ) + 1) ^ 2) * q ^ j) ≤
        ∑' j : ℕ, (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j := htsum
    _ = 2 * (∑' j : ℕ, (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left]
    _ = 2 * (1 - q)⁻¹ ^ 3 := by
      rw [hclosed]
      have hqne : 1 - q ≠ 0 := by linarith
      field_simp [hqne]

/- If a gap sequence has both lower and upper linear control, the weighted geometric
estimate keeps the `(j+1)^2` factor instead of paying a uniform `g^2 exp(-g)` envelope. -/
theorem sum_exp_gap_sq_le_weighted_geometric
    {T L c b : ℝ} (K : Finset ℕ) (k₀ : ℕ)
    (hc : 0 < c) (hb : 0 ≤ b)
    (hK : ∀ k ∈ K, k₀ ≤ k)
    (hgap : ∀ k ∈ K, 0 ≤ L - T / (k : ℝ))
    (hlin : ∀ k ∈ K, c * ((k - k₀ : ℕ) : ℝ) ≤ L - T / (k : ℝ))
    (hupper : ∀ k ∈ K,
      L - T / (k : ℝ) ≤ b * (((k - k₀ : ℕ) : ℝ) + 1)) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      2 * Real.exp L * b ^ 2 * (1 - Real.exp (-c))⁻¹ ^ 3 := by
  let q : ℝ := Real.exp (-c)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact (Real.exp_lt_exp).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ ↦
      (((j : ℝ) + 1) ^ 2) * q ^ j) := by
    have hchoose : Summable (fun j : ℕ ↦
        (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j) := by
      have hbase := summable_choose_mul_geometric_of_norm_lt_one 2 hqnorm
      simpa [mul_assoc] using hbase.mul_left (2 : ℝ)
    apply Summable.of_nonneg_of_le
      (fun j ↦ by positivity)
      (fun j ↦ by
        have hchoose_all : (j + 1) ^ 2 ≤ 2 * (j + 2).choose 2 := by
          induction j with
          | zero => norm_num
          | succ j ih =>
              rw [Nat.choose_succ_succ, Nat.choose_one_right]
              nlinarith
        have hchooseR : (((j : ℝ) + 1) ^ 2) ≤
            (2 : ℝ) * (((j + 2).choose 2 : ℕ) : ℝ) := by
          exact_mod_cast hchoose_all
        exact mul_le_mul_of_nonneg_right hchooseR (by positivity))
      hchoose
  let J : Finset ℕ := K.image (fun k ↦ k - k₀)
  have hinj : Set.InjOn (fun k : ℕ ↦ k - k₀) (K : Set ℕ) := by
    intro a ha b hb hab
    change a - k₀ = b - k₀ at hab
    have ha' := hK a ha
    have hb' := hK b hb
    have hae : a - k₀ + k₀ = a := Nat.sub_add_cancel ha'
    have hbe : b - k₀ + k₀ = b := Nat.sub_add_cancel hb'
    calc
      a = a - k₀ + k₀ := hae.symm
      _ = b - k₀ + k₀ := by rw [hab]
      _ = b := hbe
  have hsum :
      (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
        ∑ k ∈ K, Real.exp L * b ^ 2 *
          (((k - k₀ : ℕ) : ℝ) + 1) ^ 2 * q ^ (k - k₀) := by
    apply Finset.sum_le_sum
    intro k hk
    let j : ℕ := k - k₀
    have hg := hgap k hk
    have hl := hlin k hk
    have hu := hupper k hk
    have hexp : Real.exp (-(L - T / (k : ℝ))) ≤ q ^ j := by
      have harg : -(L - T / (k : ℝ)) ≤ -(c * (j : ℝ)) := by
        dsimp [j]
        linarith
      have he : Real.exp (-(L - T / (k : ℝ))) ≤
          Real.exp (-(c * (j : ℝ))) := (Real.exp_le_exp).2 harg
      have hpow : Real.exp (-(c * (j : ℝ))) = q ^ j := by
        dsimp [q]
        rw [show -(c * (j : ℝ)) = (j : ℝ) * (-c) by ring]
        exact Real.exp_nat_mul (-c) j
      simpa [j, hpow] using he
    have hsq : (L - T / (k : ℝ)) ^ 2 ≤
        (b * ((j : ℝ) + 1)) ^ 2 := by
      have hright : 0 ≤ b * ((j : ℝ) + 1) := by positivity
      exact (sq_le_sq₀ hg hright).2 (by simpa [j] using hu)
    have hmul : Real.exp (-(L - T / (k : ℝ))) *
        (L - T / (k : ℝ)) ^ 2 ≤
        Real.exp (-(L - T / (k : ℝ))) *
          (b * ((j : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    have hpoly : 0 ≤ (b * ((j : ℝ) + 1)) ^ 2 := by positivity
    have hmul' := mul_le_mul_of_nonneg_right hexp hpoly
    have hendpoint : Real.exp (T / (k : ℝ)) =
        Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by
      have harg : T / (k : ℝ) = L + (-(L - T / (k : ℝ))) := by ring
      calc
        Real.exp (T / (k : ℝ)) =
            Real.exp (L + (-(L - T / (k : ℝ)))) := congrArg Real.exp harg
        _ = Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by rw [Real.exp_add]
    calc
      Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2 =
          (Real.exp L * Real.exp (-(L - T / (k : ℝ)))) *
            (L - T / (k : ℝ)) ^ 2 := by rw [hendpoint]
      _ ≤ (Real.exp L * Real.exp (-(L - T / (k : ℝ)))) *
          (b * ((j : ℝ) + 1)) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (Real.exp_pos L).le
              (Real.exp_pos _).le)
      _ ≤ (Real.exp L * q ^ j) * (b * ((j : ℝ) + 1)) ^ 2 := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left hmul' (Real.exp_pos L).le)
      _ = Real.exp L * b ^ 2 * (((k - k₀ : ℕ) : ℝ) + 1) ^ 2 * q ^ (k - k₀) := by
            simp [j, q]
            ring
  have hsumJ :
      (∑ k ∈ K, Real.exp L * b ^ 2 *
          (((k - k₀ : ℕ) : ℝ) + 1) ^ 2 * q ^ (k - k₀)) =
        ∑ j ∈ J, Real.exp L * b ^ 2 * (((j : ℝ) + 1) ^ 2) * q ^ j := by
    dsimp [J]
    symm
    apply Finset.sum_image hinj
  have htsum := Summable.sum_le_tsum J
    (fun j hj ↦ by positivity) hgeom
  calc
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
        ∑ k ∈ K, Real.exp L * b ^ 2 *
          (((k - k₀ : ℕ) : ℝ) + 1) ^ 2 * q ^ (k - k₀) := hsum
    _ = ∑ j ∈ J, Real.exp L * b ^ 2 * (((j : ℝ) + 1) ^ 2) * q ^ j := hsumJ
    _ ≤ Real.exp L * b ^ 2 *
        (∑' j : ℕ, (((j : ℝ) + 1) ^ 2) * q ^ j) := by
      calc
        (∑ j ∈ J, Real.exp L * b ^ 2 * (((j : ℝ) + 1) ^ 2) * q ^ j) =
            Real.exp L * b ^ 2 *
              (∑ j ∈ J, (((j : ℝ) + 1) ^ 2) * q ^ j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ ≤ Real.exp L * b ^ 2 *
            (∑' j : ℕ, (((j : ℝ) + 1) ^ 2) * q ^ j) := by
              gcongr
    _ ≤ Real.exp L * b ^ 2 * (2 * (1 - q)⁻¹ ^ 3) := by
      gcongr
      exact tsum_succ_sq_mul_geometric_le hq0 hq1
    _ = 2 * Real.exp L * b ^ 2 * (1 - Real.exp (-c))⁻¹ ^ 3 := by
      dsimp [q]
      ring

/- On the report window itself, the reciprocal identity gives the required linear gap growth.
   Taking `k₀ = ceil(T/L)`, one has `L - T/k ≥ (A L/T)(k-k₀)` whenever
   `T ≤ kL` and `kA < T`.  This is the concrete bridge that feeds the geometric estimate above;
   it uses no prime-distribution input. -/
theorem report_window_gap_ge_linear
    {T A L : ℝ} (hT : 0 < T) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    ∀ k ∈ K,
      Nat.ceil (T / L) ≤ k ∧ 0 ≤ L - T / (k : ℝ) ∧
        (A * L / T) * ((k - Nat.ceil (T / L) : ℕ) : ℝ) ≤
          L - T / (k : ℝ) := by
  intro k hk
  have hdata := hK k hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hdata.1
  have hk0 : Nat.ceil (T / L) ≤ k := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hL).2
    simpa [mul_comm] using hdata.2.1
  have hceilT : T ≤ (Nat.ceil (T / L) : ℝ) * L := by
    have hceil := Nat.le_ceil (T / L)
    exact (div_le_iff₀ hL).mp hceil
  have hgap : 0 ≤ L - T / (k : ℝ) := by
    have hTk : T / (k : ℝ) ≤ L := by
      apply (div_le_iff₀ hkpos).2
      simpa [mul_comm] using hdata.2.1
    linarith
  have hAk : A < T / (k : ℝ) := by
    apply (lt_div_iff₀ hkpos).2
    simpa [mul_comm] using hdata.2.2
  have hAover : A / T ≤ 1 / (k : ℝ) := by
    apply (div_le_iff₀ hT).2
    calc
      A ≤ T / (k : ℝ) := hAk.le
      _ = (1 / (k : ℝ)) * T := by ring
  have hcoef : A * L / T ≤ L / (k : ℝ) := by
    calc
      A * L / T = L * (A / T) := by ring
      _ ≤ L * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left hAover hL.le
      _ = L / (k : ℝ) := by ring
  have hsub0 : 0 ≤ ((k - Nat.ceil (T / L) : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcoef hsub0
  have hdecomp : (k : ℝ) =
      ((k - Nat.ceil (T / L) : ℕ) : ℝ) + (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hk0).symm
  have hnum : L * ((k - Nat.ceil (T / L) : ℕ) : ℝ) ≤
      L * (k : ℝ) - T := by
    rw [hdecomp]
    nlinarith [hceilT]
  have hdiv :
      (L * ((k - Nat.ceil (T / L) : ℕ) : ℝ)) / (k : ℝ) ≤
        (L * (k : ℝ) - T) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkpos).2 hnum
  have hdiv' : (L / (k : ℝ)) * ((k - Nat.ceil (T / L) : ℕ) : ℝ) ≤
      L - T / (k : ℝ) := by
    calc
      (L / (k : ℝ)) * ((k - Nat.ceil (T / L) : ℕ) : ℝ) =
          (L * ((k - Nat.ceil (T / L) : ℕ) : ℝ)) / (k : ℝ) := by ring
      _ ≤ (L * (k : ℝ) - T) / (k : ℝ) := hdiv
      _ = L - T / (k : ℝ) := by field_simp [ne_of_gt hkpos]
  exact ⟨hk0, hgap, hmul.trans hdiv'⟩

/- The same window also gives an upper linear control from the ceiling endpoint.  This
is the complementary estimate needed by the weighted geometric kernel: with
`k₀ = ceil(T/L)`, the numerator `L*k-T` is at most `L*(k-k₀+1)` and the denominator
is at least `k₀`. -/
theorem report_window_gap_le_linear
    {T A L : ℝ} (hT : 0 < T) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    ∀ k ∈ K,
      L - T / (k : ℝ) ≤
        (L / (Nat.ceil (T / L) : ℝ)) *
          (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) := by
  intro k hk
  have hdata := hK k hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hdata.1
  have hbridge := report_window_gap_ge_linear hT hL K hK
  have hk0 : Nat.ceil (T / L) ≤ k := (hbridge k hk).1
  have hratio : 0 < T / L := div_pos hT hL
  have hk0pos : 0 < (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr hratio)
  have hceil : (Nat.ceil (T / L) : ℝ) < T / L + 1 :=
    Nat.ceil_lt_add_one (le_of_lt hratio)
  have hnum : L * (k : ℝ) - T ≤
      L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) := by
    have hdecomp : (k : ℝ) =
        ((k - Nat.ceil (T / L) : ℕ) : ℝ) + (Nat.ceil (T / L) : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hk0).symm
    have hceil' : L * (Nat.ceil (T / L) : ℝ) < T + L := by
      have hmul := mul_lt_mul_of_pos_left hceil hL
      field_simp [ne_of_gt hL] at hmul
      nlinarith
    rw [hdecomp]
    nlinarith
  have hdiv : (L * (k : ℝ) - T) / (k : ℝ) ≤
      (L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkpos).2 hnum
  have hk0le : (Nat.ceil (T / L) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hrec : (1 / (k : ℝ)) ≤ 1 / (Nat.ceil (T / L) : ℝ) :=
    one_div_le_one_div_of_le hk0pos hk0le
  have hmul : (L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) /
      (k : ℝ) ≤
      (L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) /
        (Nat.ceil (T / L) : ℝ) := by
    have hnonneg : 0 ≤ L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) := by positivity
    simpa [div_eq_mul_inv, one_div] using
      (mul_le_mul_of_nonneg_left hrec hnonneg)
  calc
    L - T / (k : ℝ) = (L * (k : ℝ) - T) / (k : ℝ) := by
      field_simp [ne_of_gt hkpos]
    _ ≤ (L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) / (k : ℝ) := hdiv
    _ ≤ (L * (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) /
        (Nat.ceil (T / L) : ℝ) := hmul
    _ = (L / (Nat.ceil (T / L) : ℝ)) *
        (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) := by ring

/- Direct report-window specialization of the preceding geometric estimate.  The only
   remaining simplification is the elementary lower bound on the geometric denominator and the
   endpoint substitution `exp L = T*v`; no finite-fibre bookkeeping is hidden here. -/
theorem report_window_quadratic_gap_le_geometric
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      9 * Real.exp (-2) * Real.exp L *
        (1 - Real.exp (-(A * L / T) / 3))⁻¹ := by
  have hbridge := report_window_gap_ge_linear hT hL K hK
  have hK0 : ∀ k ∈ K, Nat.ceil (T / L) ≤ k := by
    intro k hk
    exact (hbridge k hk).1
  have hgap : ∀ k ∈ K, 0 ≤ L - T / (k : ℝ) := by
    intro k hk
    exact (hbridge k hk).2.1
  have hlin : ∀ k ∈ K,
      (A * L / T) * ((k - Nat.ceil (T / L) : ℕ) : ℝ) ≤
        L - T / (k : ℝ) := by
    intro k hk
    exact (hbridge k hk).2.2
  exact sum_exp_gap_sq_le_geometric K (Nat.ceil (T / L))
    (by positivity) hK0 hgap hlin

/- Weighted report-window specialization.  The lower and upper ceiling controls are both
elementary, so the quadratic term can be sent to the exact `(j+1)^2` geometric kernel. -/
theorem report_window_quadratic_gap_le_weighted_geometric
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
        (1 - Real.exp (-(A * L / T)))⁻¹ ^ 3 := by
  have hbridge := report_window_gap_ge_linear hT hL K hK
  have hupper := report_window_gap_le_linear hT hL K hK
  have hK0 : ∀ k ∈ K, Nat.ceil (T / L) ≤ k := by
    intro k hk
    exact (hbridge k hk).1
  have hgap : ∀ k ∈ K, 0 ≤ L - T / (k : ℝ) := by
    intro k hk
    exact (hbridge k hk).2.1
  have hlin : ∀ k ∈ K,
      (A * L / T) * ((k - Nat.ceil (T / L) : ℕ) : ℝ) ≤
        L - T / (k : ℝ) := by
    intro k hk
    exact (hbridge k hk).2.2
  have hupper' : ∀ k ∈ K,
      L - T / (k : ℝ) ≤ (L / (Nat.ceil (T / L) : ℝ)) *
        (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) := by
    intro k hk
    exact hupper k hk
  exact sum_exp_gap_sq_le_weighted_geometric K (Nat.ceil (T / L))
    (by positivity) (by positivity) hK0 hgap hlin hupper'

theorem report_window_quadratic_gap_le_weighted_explicit
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
        (1 + T / (A * L)) ^ 3 := by
  have hraw := report_window_quadratic_gap_le_weighted_geometric hT hA hL K hK
  have hx : 0 < A * L / T := by positivity
  have hden := inv_one_sub_exp_neg_le_one_add_inv hx
  have hden' : (1 - Real.exp (-(A * L / T)))⁻¹ ≤
      1 + T / (A * L) := by
    calc
      (1 - Real.exp (-(A * L / T)))⁻¹ ≤
          1 + 1 / (A * L / T) := hden
      _ = 1 + T / (A * L) := by
        field_simp [ne_of_gt hT, ne_of_gt hA, ne_of_gt hL]
  have hdenbase : 0 ≤ 1 - Real.exp (-(A * L / T)) := by
    have hexp : Real.exp (-(A * L / T)) ≤ Real.exp 0 := by
      apply (Real.exp_le_exp).2
      linarith
    norm_num at hexp ⊢
    linarith
  have hden0 : 0 ≤ (1 - Real.exp (-(A * L / T)))⁻¹ :=
    inv_nonneg.mpr hdenbase
  have hdenpow : (1 - Real.exp (-(A * L / T)))⁻¹ ^ 3 ≤
      (1 + T / (A * L)) ^ 3 := by
    exact pow_le_pow_left₀ hden0 hden' 3
  have hfactor : 0 ≤ 2 * Real.exp L *
      (L / (Nat.ceil (T / L) : ℝ)) ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hdenpow hfactor
  calc
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
        2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
          (1 - Real.exp (-(A * L / T)))⁻¹ ^ 3 := hraw
    _ ≤ 2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
        (1 + T / (A * L)) ^ 3 := hm

theorem report_window_quadratic_gap_le_explicit
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) ≤
      9 * Real.exp (-2) * Real.exp L * (1 + 3 * T / (A * L)) := by
  have hraw := report_window_quadratic_gap_le_geometric hT hA hL K hK
  have hx : 0 < A * L / (3 * T) := by positivity
  have hden0 := inv_one_sub_exp_neg_le_one_add_inv hx
  have hden : (1 - Real.exp (-(A * L / T) / 3))⁻¹ ≤
      1 + 3 * T / (A * L) := by
    calc
      (1 - Real.exp (-(A * L / T) / 3))⁻¹ =
          (1 - Real.exp (-(A * L / (3 * T))))⁻¹ := by
            congr 2
            ring_nf
      _ ≤ 1 + 1 / (A * L / (3 * T)) := hden0
      _ = 1 + 3 * T / (A * L) := by
        field_simp [ne_of_gt hT, ne_of_gt hA, ne_of_gt hL]
  have hfactor : 0 ≤ 9 * Real.exp (-2) * Real.exp L := by positivity
  have hm := mul_le_mul_of_nonneg_left hden hfactor
  exact hraw.trans hm

/- Pointwise Track-C majorant after the sharp endpoint reduction.  The caller only needs
`T≥4`, `0<L`, and `r≤L`; all sign checks are discharged here. -/
theorem report_sharp_width_term_le_gap_majorant
    {T L r : ℝ} (hT : 4 ≤ T) (hL : 0 < L) (hrL : r ≤ L) :
    ((L - (r - 4 * (L - r) / T)) / L) *
        (Real.exp r -
          Real.exp (r - 4 * (L - r) / T) + 1) ≤
      (2 * (L - r) / L) *
        (Real.exp r * (4 * (L - r) / T) + 1) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hdiff : 0 ≤ L - r := sub_nonneg.mpr hrL
  have hd : 0 ≤ 4 * (L - r) / T := by
    exact div_nonneg (mul_nonneg (by norm_num) hdiff) hTpos.le
  have hwidth : Real.exp r -
      Real.exp (r - 4 * (L - r) / T) ≤
      Real.exp r * (4 * (L - r) / T) := by
    exact exp_sub_width_le_exp_mul hd
  have hcoef : 0 ≤ (L - (r - 4 * (L - r) / T)) / L := by
    exact div_nonneg (by linarith) hL.le
  have hwidth0 : 0 ≤ Real.exp r -
      Real.exp (r - 4 * (L - r) / T) + 1 := by
    have hexpmono : Real.exp (r - 4 * (L - r) / T) ≤ Real.exp r := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  have hwidth' : Real.exp r -
      Real.exp (r - 4 * (L - r) / T) + 1 ≤
      Real.exp r * (4 * (L - r) / T) + 1 := by
    linarith
  have hleft := mul_le_mul_of_nonneg_left hwidth' hcoef
  have hcoeftwo : (L - (r - 4 * (L - r) / T)) / L ≤
      2 * (L - r) / L := report_sharp_width_coefficient_le_two hT hL hrL
  have hright0 : 0 ≤ Real.exp r * (4 * (L - r) / T) + 1 := by
    positivity
  have hright := mul_le_mul_of_nonneg_right hcoeftwo hright0
  exact hleft.trans hright

/- Named forms of the two pointwise width expressions.  Naming them keeps later window-sum
certificates readable and makes it possible to swap in the gap majorant without repeating the
long endpoint formula. -/
noncomputable def reportSharpWidthTerm (T L : ℝ) (k : ℕ) : ℝ :=
  ((L - (T / (k : ℝ) - 4 * (L - T / (k : ℝ)) / T)) / L) *
    (Real.exp (T / (k : ℝ)) -
      Real.exp (T / (k : ℝ) - 4 * (L - T / (k : ℝ)) / T) + 1)

noncomputable def reportGapMajorantTerm (T L : ℝ) (k : ℕ) : ℝ :=
  (2 * (L - T / (k : ℝ)) / L) *
    (Real.exp (T / (k : ℝ)) * (4 * (L - T / (k : ℝ)) / T) + 1)

theorem report_sharp_width_sum_le_gap_majorant_sum
    {T L : ℝ} (hT : 4 ≤ T) (hL : 0 < L) (K : Finset ℕ)
    (hK : ∀ k ∈ K, T / (k : ℝ) ≤ L) :
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
      ∑ k ∈ K, reportGapMajorantTerm T L k := by
  apply Finset.sum_le_sum
  intro k hk
  simpa [reportSharpWidthTerm, reportGapMajorantTerm] using
    (report_sharp_width_term_le_gap_majorant hT hL (hK k hk))

theorem reportGapMajorantTerm_eq_quadratic_add_linear
    (T L : ℝ) (k : ℕ) :
    reportGapMajorantTerm T L k =
      8 * Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2 / (L * T) +
        2 * (L - T / (k : ℝ)) / L := by
  simp only [reportGapMajorantTerm]
  ring

/- Scaled form of the geometric gap estimate, matching the quadratic summand in the named
   report majorant.  The factor `8/(L*T)` is kept outside the proof so later endpoint arithmetic
   can simplify it independently. -/
theorem sum_report_quadratic_gap_le_geometric
    {T L c : ℝ} (K : Finset ℕ) (k₀ : ℕ)
    (hT : 0 < T) (hL : 0 < L) (hc : 0 < c)
    (hK : ∀ k ∈ K, k₀ ≤ k)
    (hgap : ∀ k ∈ K, 0 ≤ L - T / (k : ℝ))
    (hlin : ∀ k ∈ K, c * ((k - k₀ : ℕ) : ℝ) ≤ L - T / (k : ℝ)) :
    (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2 /
        (L * T)) ≤
      72 * Real.exp (-2) * Real.exp L / (L * T) *
        (1 - Real.exp (-c / 3))⁻¹ := by
  have hraw := sum_exp_gap_sq_le_geometric K k₀ hc hK hgap hlin
  have hfactor : 0 ≤ (8 : ℝ) / (L * T) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hraw hfactor
  calc
    (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2 /
        (L * T)) =
        (8 / (L * T)) *
          (∑ k ∈ K, Real.exp (T / (k : ℝ)) * (L - T / (k : ℝ)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (8 / (L * T)) *
        (9 * Real.exp (-2) * Real.exp L * (1 - Real.exp (-c / 3))⁻¹) := hscaled
    _ = 72 * Real.exp (-2) * Real.exp L / (L * T) *
        (1 - Real.exp (-c / 3))⁻¹ := by ring

/- A purely arithmetic cardinality bound for the exponent window.  If every index satisfies
`T ≤ kL` and `kA < T`, then the number of such natural indices is at most the real interval
length `T/A - T/L` plus two floor-endpoint units.  This is the cardinality factor needed by a
coarse treatment of the linear `(L-r)` part of the gap majorant. -/
theorem card_real_window_le_length_add_two
    {T A L : ℝ} (hT0 : 0 ≤ T) (hA : 0 < A) (hAL : A ≤ L) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (K.card : ℝ) ≤ T / A - T / L + 2 := by
  let lo : ℕ := Nat.floor (T / L)
  let hi : ℕ := Nat.floor (T / A)
  have hTL0 : 0 ≤ T / L := div_nonneg hT0 hL.le
  have hTA0 : 0 ≤ T / A := div_nonneg hT0 hA.le
  have hsub : K ⊆ Finset.Icc lo hi := by
    intro k hk
    have hdata := hK k hk
    have hlowR : T / L ≤ (k : ℝ) := by
      apply (div_le_iff₀ hL).2
      simpa [mul_comm] using hdata.2.1
    have hfloorlow : (lo : ℝ) ≤ T / L := by
      dsimp [lo]
      exact Nat.floor_le hTL0
    have hlow : lo ≤ k := by
      exact_mod_cast hfloorlow.trans hlowR
    have huppR : (k : ℝ) < T / A := by
      apply (lt_div_iff₀ hA).2
      simpa [mul_comm] using hdata.2.2
    have hupp : (k : ℝ) ≤ T / A := le_of_lt huppR
    have hfloorupp : k ≤ hi := by
      dsimp [hi]
      exact Nat.le_floor hupp
    exact Finset.mem_Icc.mpr ⟨hlow, hfloorupp⟩
  have hcardNat : K.card ≤ hi + 1 - lo := by
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    exact hcard
  have hcardR : (K.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by
    by_cases hKempty : K = ∅
    · have hratio : T / L ≤ T / A := by
        apply (div_le_div_iff₀ hL hA).2
        nlinarith
      have hfloor : lo ≤ hi := by
        dsimp [lo, hi]
        exact Nat.floor_mono hratio
      have hfloorR : (lo : ℝ) ≤ (hi : ℝ) + 1 := by
        exact_mod_cast hfloor.trans (Nat.le_succ _)
      simp [hKempty]
      linarith
    · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hKempty
      have hsubk := hsub hk
      have hlohi : lo ≤ hi := (Finset.mem_Icc.mp hsubk).1.trans
        (Finset.mem_Icc.mp hsubk).2
      have hcast : (K.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      rw [Nat.cast_sub (Nat.le_succ_of_le hlohi)] at hcast
      simpa [Nat.cast_add] using hcast
  have hhi : (hi : ℝ) ≤ T / A := by
    dsimp [hi]
    exact Nat.floor_le hTA0
  have hlo : T / L - 1 < (lo : ℝ) := by
    have h := Nat.lt_floor_add_one (T / L)
    dsimp [lo]
    linarith
  linarith

/- The corresponding coarse linear-gap estimate.  On the window, `A < T/k ≤ L`, hence every
normalized gap `(L-T/k)/L` is bounded by `(L-A)/L`; summing uses only the finite-cardinality
lemma above. -/
theorem sum_normalized_gap_le_card_mul
    {T A L : ℝ} (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
      (K.card : ℝ) * ((L - A) / L) := by
  have hsum := Finset.sum_le_card_nsmul K
    (fun k ↦ (L - T / (k : ℝ)) / L) ((L - A) / L) ?_
  · simpa [nsmul_eq_mul] using hsum
  · intro k hk
    have hdata := hK k hk
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hdata.1
    have hTk : T / (k : ℝ) ≤ L := by
      apply (div_le_iff₀ hkreal).2
      simpa [mul_comm] using hdata.2.1
    have hAk : A < T / (k : ℝ) := by
      apply (lt_div_iff₀ hkreal).2
      simpa [mul_comm] using hdata.2.2
    apply (div_le_div_iff₀ hL hL).2
    have hnum : L - T / (k : ℝ) ≤ L - A :=
      sub_le_sub_left hAk.le L
    exact mul_le_mul_of_nonneg_right hnum hL.le

theorem sum_normalized_gap_le_explicit_window
    {T A L : ℝ} (hT0 : 0 ≤ T) (hA : 0 < A) (hAL : A ≤ L) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
      (T / A - T / L + 2) * ((L - A) / L) := by
  have hsum := sum_normalized_gap_le_card_mul hL K hK
  have hcard := card_real_window_le_length_add_two hT0 hA hAL hL K hK
  have hfactor : 0 ≤ (L - A) / L :=
    div_nonneg (sub_nonneg.mpr hAL) hL.le
  exact hsum.trans (mul_le_mul_of_nonneg_right hcard hfactor)

/- A sharper finite bound for the linear piece.  The upper gap control gives each normalized
gap at most `(j+1)/k₀`; bounding the window by `k≤floor(T/A)` then costs only a quadratic
endpoint factor, rather than the maximum-gap times cardinality product. -/
theorem sum_normalized_gap_le_quadratic_window
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
      (((Nat.floor (T / A) : ℕ) : ℝ) + 1) ^ 2 /
        (Nat.ceil (T / L) : ℝ) := by
  have hbridge := report_window_gap_le_linear hT hL K hK
  have hK0 : ∀ k ∈ K, Nat.ceil (T / L) ≤ k := by
    intro k hk
    exact (report_window_gap_ge_linear hT hL K hK k hk).1
  have hk0pos : 0 < (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (div_pos hT hL))
  have hhi : ∀ k ∈ K, k ≤ Nat.floor (T / A) := by
    intro k hk
    have hdata := hK k hk
    have hupp : (k : ℝ) < T / A := by
      apply (lt_div_iff₀ hA).2
      simpa [mul_comm] using hdata.2.2
    exact Nat.le_floor hupp.le
  have hsub : K ⊆ Finset.range (Nat.floor (T / A) + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hhi k hk))
  have hcard : (K.card : ℝ) ≤ ((Nat.floor (T / A) : ℕ) : ℝ) + 1 := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    exact_mod_cast hc
  have hpoint : ∀ k ∈ K,
      (L - T / (k : ℝ)) / L ≤
        (((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ) := by
    intro k hk
    have hu := hbridge k hk
    have hj : (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ≤
        ((Nat.floor (T / A) : ℕ) : ℝ) + 1 := by
      have hsubk : (k - Nat.ceil (T / L) : ℕ) ≤ k := Nat.sub_le _ _
      have hplus : k - Nat.ceil (T / L) + 1 ≤
          (Nat.floor (T / A) : ℕ) + 1 :=
        (Nat.add_le_add_right hsubk 1).trans
          (Nat.add_le_add_right (hhi k hk) 1)
      exact_mod_cast hplus
    have hnorm : (L - T / (k : ℝ)) / L ≤
        (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ) := by
      calc
        (L - T / (k : ℝ)) / L ≤
            ((L / (Nat.ceil (T / L) : ℝ)) *
              (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) / L := by
                exact div_le_div_of_nonneg_right hu hL.le
        _ = (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ) := by
              field_simp [ne_of_gt hL, ne_of_gt hk0pos]
    calc
      (L - T / (k : ℝ)) / L ≤
          (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ) := hnorm
      _ ≤ (((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ) := by
            apply (div_le_div_iff_of_pos_right hk0pos).2
            exact hj
  have hsum := Finset.sum_le_card_nsmul K
    (fun k ↦ (L - T / (k : ℝ)) / L)
    ((((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
      (Nat.ceil (T / L) : ℝ)) (fun k hk ↦ hpoint k hk)
  have hsum' : (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
      (K.card : ℝ) * ((((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
        (Nat.ceil (T / L) : ℝ)) := by
    simpa [nsmul_eq_mul] using hsum
  have hfactor : 0 ≤ (((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
      (Nat.ceil (T / L) : ℝ) := by positivity
  calc
    (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
        (K.card : ℝ) * ((((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ)) := hsum'
    _ ≤ (((Nat.floor (T / A) : ℕ) : ℝ) + 1) *
        ((((Nat.floor (T / A) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = (((Nat.floor (T / A) : ℕ) : ℝ) + 1) ^ 2 /
        (Nat.ceil (T / L) : ℝ) := by ring

/- A sharper endpoint version of the preceding finite bound.  The lower endpoint
   `ceil (T/L)` is subtracted before counting the window, so the quadratic factor
   depends on the actual window width rather than the whole upper endpoint. -/
theorem sum_normalized_gap_le_quadratic_window_tight
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A) (hL : 0 < L)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
      (((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
        (Nat.ceil (T / L) : ℝ) := by
  have hbridge := report_window_gap_le_linear hT hL K hK
  have hk0pos : 0 < (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (div_pos hT hL))
  have hhi : ∀ k ∈ K, k ≤ Nat.floor (T / A) := by
    intro k hk
    have hdata := hK k hk
    have hupp : (k : ℝ) < T / A := by
      apply (lt_div_iff₀ hA).2
      simpa [mul_comm] using hdata.2.2
    exact Nat.le_floor hupp.le
  by_cases hKempty : K = ∅
  · simp [hKempty]
    positivity
  · obtain ⟨k₁, hk₁⟩ := Finset.nonempty_iff_ne_empty.mpr hKempty
    have hk0 : Nat.ceil (T / L) ≤ k₁ :=
      (report_window_gap_ge_linear hT hL K hK k₁ hk₁).1
    have hk0hi : Nat.ceil (T / L) ≤ Nat.floor (T / A) :=
      hk0.trans (hhi k₁ hk₁)
    have hsub : K ⊆ Finset.Icc (Nat.ceil (T / L)) (Nat.floor (T / A)) := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨
        (report_window_gap_ge_linear hT hL K hK k hk).1, hhi k hk⟩
    have hcardNat : K.card ≤
        Nat.floor (T / A) + 1 - Nat.ceil (T / L) := by
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hc
      exact hc
    have hcard : (K.card : ℝ) ≤
        ((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1 := by
      have hcast : (K.card : ℝ) ≤
          ((Nat.floor (T / A) + 1 - Nat.ceil (T / L) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      have hnatEq : Nat.floor (T / A) + 1 - Nat.ceil (T / L) =
          (Nat.floor (T / A) - Nat.ceil (T / L)) + 1 := by omega
      rw [hnatEq] at hcast
      simpa [Nat.cast_add, Nat.cast_one] using hcast
    have hpoint : ∀ k ∈ K,
        (L - T / (k : ℝ)) / L ≤
          (((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ) := by
      intro k hk
      have hu := hbridge k hk
      have hj : (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ≤
          ((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1 := by
        have hsubk : k - Nat.ceil (T / L) ≤
            Nat.floor (T / A) - Nat.ceil (T / L) :=
          Nat.sub_le_sub_right (hhi k hk) _
        exact_mod_cast (Nat.add_le_add_right hsubk 1)
      have hnorm : (L - T / (k : ℝ)) / L ≤
          (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ) := by
        calc
          (L - T / (k : ℝ)) / L ≤
              ((L / (Nat.ceil (T / L) : ℝ)) *
                (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1)) / L := by
                  exact div_le_div_of_nonneg_right hu hL.le
          _ = (((k - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
              (Nat.ceil (T / L) : ℝ) := by
                field_simp [ne_of_gt hL, ne_of_gt hk0pos]
      exact hnorm.trans ((div_le_div_iff_of_pos_right hk0pos).2 hj)
    have hsum := Finset.sum_le_card_nsmul K
      (fun k ↦ (L - T / (k : ℝ)) / L)
      ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
        (Nat.ceil (T / L) : ℝ)) (fun k hk ↦ hpoint k hk)
    have hsum' : (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
        (K.card : ℝ) * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
          (Nat.ceil (T / L) : ℝ)) := by
      simpa [nsmul_eq_mul] using hsum
    have hfactor : 0 ≤ (((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
        (Nat.ceil (T / L) : ℝ) := by positivity
    calc
      (∑ k ∈ K, (L - T / (k : ℝ)) / L) ≤
          (K.card : ℝ) * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ)) := hsum'
      _ ≤ (((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) *
          ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) /
            (Nat.ceil (T / L) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hfactor
      _ = (((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
          (Nat.ceil (T / L) : ℝ) := by ring

/- Combine the two pieces of the report majorant.  This is a fully explicit finite-window
   bound: the first summand is controlled by the geometric reduction, and the second by the
   cardinality estimate above.  Only the final numerical simplification to `24*T/v²` remains. -/
theorem report_sharp_width_sum_le_explicit_window
    {T A L : ℝ} (hT : 4 ≤ T) (hTpos : 0 < T) (hA : 0 < A)
    (hAL : A ≤ L) (hL : 0 < L) (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
      72 * Real.exp (-2) * Real.exp L / (L * T) *
        (1 + 3 * T / (A * L)) +
        2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
  have hKratio : ∀ k ∈ K, T / (k : ℝ) ≤ L := by
    intro k hk
    have hdata := hK k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hdata.1
    apply (div_le_iff₀ hkpos).2
    simpa [mul_comm] using hdata.2.1
  have hmajor := report_sharp_width_sum_le_gap_majorant_sum hT hL K hKratio
  have hquadraw := report_window_quadratic_gap_le_explicit hTpos hA hL K hK
  have hquadfactor : 0 ≤ (8 : ℝ) / (L * T) := by positivity
  have hquadscaled := mul_le_mul_of_nonneg_left hquadraw hquadfactor
  have hquad :
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
        (L - T / (k : ℝ)) ^ 2 / (L * T)) ≤
        72 * Real.exp (-2) * Real.exp L / (L * T) *
          (1 + 3 * T / (A * L)) := by
    calc
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) =
          (8 / (L * T)) *
            (∑ k ∈ K, Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (8 / (L * T)) *
          (9 * Real.exp (-2) * Real.exp L * (1 + 3 * T / (A * L))) := hquadscaled
      _ = 72 * Real.exp (-2) * Real.exp L / (L * T) *
          (1 + 3 * T / (A * L)) := by ring
  have hlinear := sum_normalized_gap_le_explicit_window
    (le_trans (by norm_num) hT) hA hAL hL K hK
  calc
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
        ∑ k ∈ K, reportGapMajorantTerm T L k := hmajor
    _ =
        (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) +
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
      calc
        (∑ k ∈ K, reportGapMajorantTerm T L k) =
            ∑ k ∈ K,
              (8 * Real.exp (T / (k : ℝ)) *
                (L - T / (k : ℝ)) ^ 2 / (L * T) +
                2 * (L - T / (k : ℝ)) / L) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact reportGapMajorantTerm_eq_quadratic_add_linear T L k
        _ =
            (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2 / (L * T)) +
              (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
          rw [Finset.sum_add_distrib]
    _ ≤
        72 * Real.exp (-2) * Real.exp L / (L * T) *
          (1 + 3 * T / (A * L)) +
          2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
      have hlinear' :
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) ≤
            2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
        have hlin := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2)
        calc
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) =
              2 * (∑ k ∈ K, (L - T / (k : ℝ)) / L) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ ≤ 2 * ((T / A - T / L + 2) * ((L - A) / L)) := hlin
      exact add_le_add hquad hlinear'

/- Combining the weighted quadratic estimate with the existing cardinality bound gives a
second explicit finite-window certificate.  It is asymptotically sharper than the uniform
`9 exp(-2)` envelope and is the preferred starting point for the final numerical check. -/
theorem report_sharp_width_sum_le_weighted_explicit_window
    {T A L : ℝ} (hT : 4 ≤ T) (hTpos : 0 < T) (hA : 0 < A)
    (hAL : A ≤ L) (hL : 0 < L) (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
      16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
          (L * T) * (1 + T / (A * L)) ^ 3 +
        2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
  have hKratio : ∀ k ∈ K, T / (k : ℝ) ≤ L := by
    intro k hk
    have hdata := hK k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hdata.1
    apply (div_le_iff₀ hkpos).2
    simpa [mul_comm] using hdata.2.1
  have hmajor := report_sharp_width_sum_le_gap_majorant_sum hT hL K hKratio
  have hquadraw := report_window_quadratic_gap_le_weighted_explicit hTpos hA hL K hK
  have hquadfactor : 0 ≤ (8 : ℝ) / (L * T) := by positivity
  have hquadscaled := mul_le_mul_of_nonneg_left hquadraw hquadfactor
  have hquad :
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
        (L - T / (k : ℝ)) ^ 2 / (L * T)) ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 := by
    calc
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) =
          (8 / (L * T)) *
            (∑ k ∈ K, Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (8 / (L * T)) *
          (2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
            (1 + T / (A * L)) ^ 3) := hquadscaled
      _ = 16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 := by ring
  have hlinear := sum_normalized_gap_le_explicit_window
    (le_trans (by norm_num) hT) hA hAL hL K hK
  calc
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
        ∑ k ∈ K, reportGapMajorantTerm T L k := hmajor
    _ =
        (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) +
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
      calc
        (∑ k ∈ K, reportGapMajorantTerm T L k) =
            ∑ k ∈ K,
              (8 * Real.exp (T / (k : ℝ)) *
                (L - T / (k : ℝ)) ^ 2 / (L * T) +
                2 * (L - T / (k : ℝ)) / L) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact reportGapMajorantTerm_eq_quadratic_add_linear T L k
        _ =
            (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2 / (L * T)) +
              (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
          rw [Finset.sum_add_distrib]
    _ ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 +
          2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
      have hlinear' :
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) ≤
            2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
        have hlin := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2)
        calc
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) =
              2 * (∑ k ∈ K, (L - T / (k : ℝ)) / L) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ ≤ 2 * ((T / A - T / L + 2) * ((L - A) / L)) := hlin
      exact add_le_add hquad hlinear'

/- The same weighted certificate with the endpoint-sharp linear term.  This version retains the
   full finite window width `floor (T/A) - ceil (T/L)` in the linear contribution and is the
   preferred interface for a final scalar proof of the source constant. -/
theorem report_sharp_width_sum_le_weighted_explicit_window_tight
    {T A L : ℝ} (hT : 4 ≤ T) (hTpos : 0 < T) (hA : 0 < A)
    (_hAL : A ≤ L) (hL : 0 < L) (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T) :
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
      16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
          (L * T) * (1 + T / (A * L)) ^ 3 +
        2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
          (Nat.ceil (T / L) : ℝ)) := by
  have hKratio : ∀ k ∈ K, T / (k : ℝ) ≤ L := by
    intro k hk
    have hdata := hK k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hdata.1
    apply (div_le_iff₀ hkpos).2
    simpa [mul_comm] using hdata.2.1
  have hmajor := report_sharp_width_sum_le_gap_majorant_sum hT hL K hKratio
  have hquadraw := report_window_quadratic_gap_le_weighted_explicit hTpos hA hL K hK
  have hquadfactor : 0 ≤ (8 : ℝ) / (L * T) := by positivity
  have hquadscaled := mul_le_mul_of_nonneg_left hquadraw hquadfactor
  have hquad :
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
        (L - T / (k : ℝ)) ^ 2 / (L * T)) ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 := by
    calc
      (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) =
          (8 / (L * T)) *
            (∑ k ∈ K, Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (8 / (L * T)) *
          (2 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 *
            (1 + T / (A * L)) ^ 3) := hquadscaled
      _ = 16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 := by ring
  have hlinear := sum_normalized_gap_le_quadratic_window_tight hTpos hA hL K hK
  calc
    (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
        ∑ k ∈ K, reportGapMajorantTerm T L k := hmajor
    _ =
        (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
          (L - T / (k : ℝ)) ^ 2 / (L * T)) +
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
      calc
        (∑ k ∈ K, reportGapMajorantTerm T L k) =
            ∑ k ∈ K,
              (8 * Real.exp (T / (k : ℝ)) *
                (L - T / (k : ℝ)) ^ 2 / (L * T) +
                2 * (L - T / (k : ℝ)) / L) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact reportGapMajorantTerm_eq_quadratic_add_linear T L k
        _ =
            (∑ k ∈ K, 8 * Real.exp (T / (k : ℝ)) *
              (L - T / (k : ℝ)) ^ 2 / (L * T)) +
              (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) := by
          rw [Finset.sum_add_distrib]
    _ ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 +
          2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
            (Nat.ceil (T / L) : ℝ)) := by
      have hlinear' :
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) ≤
            2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
              (Nat.ceil (T / L) : ℝ)) := by
        have hlin := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2)
        calc
          (∑ k ∈ K, 2 * (L - T / (k : ℝ)) / L) =
              2 * (∑ k ∈ K, (L - T / (k : ℝ)) / L) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ ≤ 2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
              (Nat.ceil (T / L) : ℝ)) := hlin
      exact add_le_add hquad hlinear'

theorem exp_endpoint_eq_upper_mul_gap
    (T L : ℝ) (k : ℕ) :
    Real.exp (T / (k : ℝ)) =
      Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by
  have harg : T / (k : ℝ) = L + (-(L - T / (k : ℝ))) := by ring
  calc
    Real.exp (T / (k : ℝ)) =
        Real.exp (L + (-(L - T / (k : ℝ)))) := congrArg Real.exp harg
    _ = Real.exp L * Real.exp (-(L - T / (k : ℝ))) := by rw [Real.exp_add]

/- The preceding pointwise inequality can be fed directly into the positive-fiber aggregator.  This
adapter leaves the caller with the simpler `(L-r)`-weighted exponential majorant rather than the
original difference of exponentials. -/
theorem normalized_surplus_tail_sum_le_of_gap_majorant_on_index_set
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAhalf : L / 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hT : 4 ≤ Real.log (n : ℝ)) (hExp : Real.exp L ≤ (n : ℝ))
    (K : Finset ℕ) (hKsub : K ⊆ Finset.range (n + 1))
    (hKsupport : ∀ k ∈ Finset.range (n + 1), k ∉ K →
      positiveSurplusTailBand n A L k = ∅)
    (D : ℕ → ℝ) (hD0 : 0 ≤ D 0)
    (hD : ∀ k ∈ K, 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ L ∧
      ((2 * (L - Real.log (n : ℝ) / (k : ℝ)) / L) *
        (Real.exp (Real.log (n : ℝ) / (k : ℝ)) *
          (4 * (L - Real.log (n : ℝ) / (k : ℝ)) / Real.log (n : ℝ)) + 1)) ≤ D k) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ K, D k := by
  apply normalized_surplus_tail_sum_le_of_sharp_exp_width_bounds_on_index_set
    hn hA hAhalf hAL hL hT hExp K hKsub hKsupport D hD0
  intro k hk hkpos
  have hdata := hD k hk hkpos
  refine ⟨hdata.1, ?_⟩
  exact (report_sharp_width_term_le_gap_majorant hT hL hdata.1).trans hdata.2

/- The endpoint-count interface packaged over all exponent fibers.  A caller supplies the
   concrete finite count estimate `C k`; this theorem performs the disjoint-fiber summation and
   handles the zero fiber (which is empty once `exp L ≤ n`). -/
theorem normalized_surplus_tail_sum_le_of_endpoint_floor_counts
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAhalf : L / 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hExp : Real.exp L ≤ (n : ℝ)) (C : ℕ → ℝ) (hC0 : 0 ≤ C 0)
    (hC : ∀ k ∈ Finset.range (n + 1), 0 < k →
      Real.log (n : ℝ) / (k : ℝ) ≤ L ∧
      ((L - (Real.log (n : ℝ) / (k : ℝ) - Real.log 2 / (k : ℝ))) / L) *
          ((Nat.floor (Real.exp (Real.log (n : ℝ) / (k : ℝ))) + 1 -
            (Nat.floor (Real.exp ((Real.log (n : ℝ) - Real.log 2) / (k : ℝ))) + 1) : ℕ) : ℝ) ≤ C k) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ Finset.range (n + 1), C k := by
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  gcongr with k hk
  by_cases hk0 : k = 0
  · subst k
    rw [normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand 0]
    rw [positiveSurplusTailBand_zero_empty_of_exp_le hExp]
    simpa using hC0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hdata := hC k hk hkpos
    rw [normalizedPositiveSurplus_sum_eq_positiveSurplusTailBand k]
    exact (positiveSurplusTailBand_sum_le_endpoint_floor_count
      hn hL hAhalf k hkpos hdata.1).trans hdata.2

theorem surplus_tail_sum_le_of_band_bounds
    {n : ℕ} {A L : ℝ} {C : ℕ → ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L)
    (hband : ∀ k ∈ Finset.range (n + 1),
      (∑ b ∈ surplusTailBand n A L k, normalizedPositiveSurplus n L b) ≤ C k) :
    ∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b ≤
      ∑ k ∈ Finset.range (n + 1), C k := by
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  gcongr with k hk
  exact hband k hk

/- Global finite endpoint interface.  Supplying a lower/upper logarithmic window `(u k,v k]`
for each exponent fiber automatically yields the corresponding sum of exponential widths.  This
is the exact place where the report's remaining analytic estimate can be attached. -/
theorem normalized_surplus_tail_sum_le_of_width_exp_bounds
    {n : ℕ} (hn : n ≠ 0) {A L : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (u v : ℕ → ℝ)
    (hparams : ∀ k ∈ Finset.range (n + 1), u k ≤ L ∧ u k ≤ v k)
    (hband : ∀ k ∈ Finset.range (n + 1),
      ∀ b ∈ surplusTailBand n A L k,
        u k < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ v k ∧
          Real.log (b : ℝ) ≤ L) :
    (∑ b ∈ Finset.Icc (Nat.floor (Real.exp A) + 1) (Nat.floor (Real.exp L)),
        normalizedPositiveSurplus n L b) ≤
      ∑ k ∈ Finset.range (n + 1),
        ((L - u k) / L) * (Real.exp (v k) - Real.exp (u k) + 1) := by
  rw [surplus_tail_sum_eq_sum_surplusTailBands hA hAL]
  gcongr with k hk
  obtain ⟨huL, huv⟩ := hparams k hk
  exact normalized_subset_surplusBand_sum_le_width_mul_exp_width_add_one
    hn (surplusTailBand n A L k) hL huL huv
    (surplusTailBand_subset_surplusBand k) (hband k hk)

/-! A direct consequence for the normalized prime-power sum: once the endpoint tail has any
explicit bound `C`, the full pointwise estimate is just the budget term plus `exp A + C`.  The
definition of the source function `f` in the main file is a cast of this sum. -/
noncomputable def normalizedPrimePowerSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, normalizedPrimePowerWeight n p

theorem normalizedPrimePowerSum_le_of_tail_surplus_bound
    {n : ℕ} (hn : n ≠ 0) {A L C : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hTail :
      ∑ p ∈ Finset.Icc (⌊Real.exp A⌋₊ + 1) (⌊Real.exp L⌋₊),
        normalizedPositiveSurplus n L p ≤ C) :
    normalizedPrimePowerSum n ≤ Real.log (n : ℝ) / L + Real.exp A + C := by
  have hrel := relaxed_prime_power_upper_exp_interval hn hL
  have hsplit := surplus_sum_split_small_tail hn hA hAL hL
  have hsurplus :
      ∑ p ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L p ≤
      Real.exp A + C := by
    exact hsplit.trans (add_le_add_right hTail (Real.exp A))
  have hf :
      normalizedPrimePowerSum n ≤ Real.log (n : ℝ) / L +
        ∑ p ∈ Finset.Icc 2 (⌊Real.exp L⌋₊), normalizedPositiveSurplus n L p := by
    simpa [normalizedPrimePowerSum] using hrel
  exact hf.trans (by
    simpa [add_assoc] using
      (add_le_add_right hsurplus (Real.log (n : ℝ) / L)))

/-! The report's concrete choice is
`A = v - 3 log v`, `L = v + log v`, with `T = log n` and `v = log T`.
The next two lemmas perform only the exact endpoint arithmetic and the resulting reduction.
They intentionally leave the short-interval estimate as one explicit hypothesis; this keeps the
unproved analytic input visible instead of silently treating the candidate as a theorem. -/
theorem exp_report_lower_endpoint_eq
    {T v : ℝ} (hT : 0 < T) (hv : 0 < v)
    (hlogT : Real.log T = v) :
    Real.exp (v - 3 * Real.log v) = T / v ^ 3 := by
  have hvpow : Real.exp (3 * Real.log v) = v ^ 3 := by
    calc
      Real.exp (3 * Real.log v) = Real.exp (Real.log v) ^ 3 := by
        simpa using (Real.exp_nat_mul (Real.log v) 3)
      _ = v ^ 3 := by rw [Real.exp_log hv]
  calc
    Real.exp (v - 3 * Real.log v) =
        Real.exp v / Real.exp (3 * Real.log v) := by
      rw [Real.exp_sub]
    _ = T / Real.exp (3 * Real.log v) := by
      rw [show Real.exp v = T by rw [← hlogT, Real.exp_log hT]]
    _ = T / v ^ 3 := by rw [hvpow]

theorem exp_report_upper_endpoint_eq
    {T v : ℝ} (hT : 0 < T) (hv : 0 < v)
    (hlogT : Real.log T = v) :
    Real.exp (v + Real.log v) = T * v := by
  rw [Real.exp_add, Real.exp_log hv]
  have hTv : Real.exp v = T := by
    rw [← hlogT, Real.exp_log hT]
  rw [hTv]

theorem normalizedPrimePowerSum_le_report_bound
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 0 < T) (hv : 0 < v) (hv1 : 1 ≤ v)
    (hlogT : Real.log T = v)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hTail :
      ∑ p ∈ Finset.Icc
          (⌊Real.exp (v - 3 * Real.log v)⌋₊ + 1)
          (⌊Real.exp (v + Real.log v)⌋₊),
          normalizedPositiveSurplus n (v + Real.log v) p ≤ 24 * T / v ^ 2) :
    normalizedPrimePowerSum n ≤
      Real.log (n : ℝ) / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2 := by
  have hvlog : 0 ≤ Real.log v := Real.log_nonneg hv1
  have hAL : v - 3 * Real.log v ≤ v + Real.log v := by linarith
  have hL : 0 < v + Real.log v := by linarith
  have hbase := normalizedPrimePowerSum_le_of_tail_surplus_bound hn
    hA hAL hL hTail
  rw [exp_report_lower_endpoint_eq hT hv hlogT] at hbase
  exact hbase

end Erdos878

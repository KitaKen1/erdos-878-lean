import Erdos878.RelaxedBound

set_option maxHeartbeats 800000

open scoped BigOperators
open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

noncomputable def tightReportScalar (T v : ℝ) : ℝ :=
  16 * Real.exp (v + Real.log v) *
      ((v + Real.log v) /
        (Nat.ceil (T / (v + Real.log v)) : ℝ)) ^ 2 /
        ((v + Real.log v) * T) *
          (1 + T / ((v - 3 * Real.log v) * (v + Real.log v))) ^ 3 +
    2 * ((((Nat.floor (T / (v - 3 * Real.log v)) -
      Nat.ceil (T / (v + Real.log v)) : ℕ) : ℝ) + 1) ^ 2 /
        (Nat.ceil (T / (v + Real.log v)) : ℝ))

/- Exploratory eventual scalar certificate for the endpoint-sharp Track-C bound.  This file is
   intentionally separate from the build target while the elementary constant bookkeeping is
   developed. -/
theorem eventually_tight_report_scalar_bound :
    ∀ᶠ v : ℝ in atTop,
      tightReportScalar (Real.exp v) v ≤
        24 * Real.exp v / v ^ 2 := by
  simp only [tightReportScalar]
  have hlogv : ∀ᶠ v : ℝ in atTop, 0 ≤ Real.log v := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
    exact Real.log_nonneg hv
  have hlogsmall : ∀ᶠ v : ℝ in atTop, Real.log v / v ≤ (1 / 1000 : ℝ) := by
    have hlim : Tendsto (fun v : ℝ ↦ Real.log v / v) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact hlim.eventually (eventually_le_nhds (by norm_num))
  have hlogsqsmall : ∀ᶠ v : ℝ in atTop,
      (Real.log v) ^ 2 / v ≤ (1 / 1000 : ℝ) := by
    have hlim : Tendsto (fun v : ℝ ↦ (Real.log v) ^ 2 / v) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    exact hlim.eventually (eventually_le_nhds (by norm_num))
  have hloglarge : ∀ᶠ v : ℝ in atTop, 1 ≤ Real.log v := by
    have hlim : Tendsto (fun v : ℝ ↦ Real.log v) atTop atTop := Real.tendsto_log_atTop
    exact hlim.eventually (eventually_ge_atTop (1 : ℝ))
  have hexpratio : Tendsto (fun v : ℝ ↦ Real.exp v / v ^ 2) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 2
  have hexplarge : ∀ᶠ v : ℝ in atTop,
      (1001 / 10 : ℝ) ≤ Real.exp v / v ^ 2 :=
    hexpratio.eventually (eventually_ge_atTop (1001 / 10 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlogv, hlogsmall, hlogsqsmall,
    hloglarge, hexplarge] with
    v hvge hl hvsmall hvsq hl1 hev
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hvge
  let T : ℝ := Real.exp v
  let A : ℝ := v - 3 * Real.log v
  let L : ℝ := v + Real.log v
  have hlpos : 0 ≤ Real.log v := hl
  have hApos : 0 < A := by
    dsimp [A]
    have hsmall' : Real.log v ≤ v / 1000 := by
      calc
        Real.log v ≤ (1 / 1000 : ℝ) * v := (div_le_iff₀ hvpos).mp hvsmall
        _ = v / 1000 := by ring
    nlinarith
  have hLpos : 0 < L := by
    dsimp [L]
    nlinarith [hlpos]
  have hAle : A ≤ v := by
    dsimp [A]
    linarith
  have hLle : L ≤ (1001 / 1000 : ℝ) * v := by
    dsimp [L]
    have hsmall' : Real.log v ≤ v / 1000 := by
      calc
        Real.log v ≤ (1 / 1000 : ℝ) * v := (div_le_iff₀ hvpos).mp hvsmall
        _ = v / 1000 := by ring
    nlinarith
  have hAge : (997 / 1000 : ℝ) * v ≤ A := by
    dsimp [A]
    have hsmall' : Real.log v ≤ v / 1000 := by
      calc
        Real.log v ≤ (1 / 1000 : ℝ) * v := (div_le_iff₀ hvpos).mp hvsmall
        _ = v / 1000 := by ring
    nlinarith
  have hALpos : 0 < A * L := mul_pos hApos hLpos
  have hALle : A * L ≤ (1001 / 1000 : ℝ) * v ^ 2 := by
    have hAnonneg : 0 ≤ A := hApos.le
    have hvnonneg : 0 ≤ v := hvpos.le
    have hmul := mul_le_mul hAle hLle hLpos.le hvnonneg
    nlinarith
  have hx : 100 ≤ T / (A * L) := by
    dsimp [T]
    apply (le_div_iff₀ hALpos).2
    have hv2pos : 0 < v ^ 2 := sq_pos_of_pos hvpos
    have hev' : (1001 / 10 : ℝ) * v ^ 2 ≤ Real.exp v :=
      (le_div_iff₀ hv2pos).mp hev
    nlinarith
  have hy : 2 ≤ T / A - T / L := by
    have hdiff : L - A = 4 * Real.log v := by dsimp [A, L]; ring
    have hfrac : T / A - T / L = T * (L - A) / (A * L) := by
      field_simp [ne_of_gt hApos, ne_of_gt hLpos]
    rw [hfrac, hdiff]
    have hTpos : 0 < T := by positivity
    have hratio : 100 ≤ T / (A * L) := hx
    have hlogone : 1 ≤ Real.log v := hl1
    have hprod : 2 ≤ (T / (A * L)) * (Real.log v * 4) := by nlinarith
    convert hprod using 1; ring
  have hk0pos : 0 < (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (div_pos (by positivity) hLpos))
  have hk0ge : T / L ≤ (Nat.ceil (T / L) : ℝ) := by
    exact_mod_cast (Nat.le_ceil (T / L))
  have hceil_le_floor : Nat.ceil (T / L) ≤ Nat.floor (T / A) := by
    apply Nat.ceil_le.mpr
    have hfloor : (T / A : ℝ) - 1 < (Nat.floor (T / A) : ℝ) := by
      have h := Nat.lt_floor_add_one (T / A)
      linarith
    have hceil : (Nat.ceil (T / L) : ℝ) < T / L + 1 := Nat.ceil_lt_add_one (by positivity)
    have hdiff : 2 ≤ T / A - T / L := hy
    nlinarith
  have hTpos : 0 < T := by positivity
  have hwidth :
      ((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1 ≤
        2 * (T / A - T / L) := by
    rw [Nat.cast_sub hceil_le_floor]
    have hfloor : (Nat.floor (T / A) : ℝ) ≤ T / A := Nat.floor_le (by positivity)
    have hceil : T / L ≤ (Nat.ceil (T / L) : ℝ) := Nat.le_ceil _
    nlinarith [hy]
  have hQ :
      16 * Real.exp (v + Real.log v) *
          (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 ≤
      17 * T / v ^ 2 := by
    have hTpos : 0 < T := by positivity
    have hceilinv : L / (Nat.ceil (T / L) : ℝ) ≤ L ^ 2 / T := by
      have hinv : 1 / (Nat.ceil (T / L) : ℝ) ≤ L / T :=
        (one_div_le_one_div_of_le (div_pos (by positivity) hLpos) hk0ge).trans_eq (by
          field_simp [ne_of_gt hTpos, ne_of_gt hLpos])
      have hmul := mul_le_mul_of_nonneg_left hinv hLpos.le
      calc
        L / (Nat.ceil (T / L) : ℝ) = L * (1 / (Nat.ceil (T / L) : ℝ)) := by ring
        _ ≤ L * (L / T) := hmul
        _ = L ^ 2 / T := by ring
    have hratio : 1 + T / (A * L) ≤ (101 / 100 : ℝ) * (T / (A * L)) := by
      nlinarith [hx]
    have hratio3 : (1 + T / (A * L)) ^ 3 ≤
        ((101 / 100 : ℝ) * (T / (A * L))) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hratio 3
    have heL : Real.exp (v + Real.log v) = T * v := by
      dsimp [T]
      rw [Real.exp_add, Real.exp_log hvpos]
    have hqraw :
        16 * Real.exp (v + Real.log v) *
            (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
              (L * T) * (1 + T / (A * L)) ^ 3 ≤
          16 * (T * v) * (L ^ 2 / T) ^ 2 /
            (L * T) * (((101 / 100 : ℝ) * (T / (A * L))) ^ 3) := by
      rw [heL]
      gcongr
    have hAinv : 0 < A := hApos
    have hcalc :
        16 * (T * v) * (L ^ 2 / T) ^ 2 /
            (L * T) * (((101 / 100 : ℝ) * (T / (A * L))) ^ 3) ≤
          17 * T / v ^ 2 := by
      have hAge' : 0 < (997 / 1000 : ℝ) := by norm_num
      have hconst :
          16 * (101 / 100) ^ 3 / (997 / 1000) ^ 3 ≤ (17 : ℝ) := by norm_num
      have hLnonneg : 0 ≤ L := hLpos.le
      have hL3 : L ^ 3 ≤ ((1001 / 1000 : ℝ) * v) ^ 3 := by
        exact pow_le_pow_left₀ hLpos.le hLle 3
      have hvnonneg : 0 ≤ v := hvpos.le
      have hA3 : ((997 / 1000 : ℝ) * v) ^ 3 ≤ A ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) hAge 3
      field_simp [ne_of_gt hTpos, ne_of_gt hApos, ne_of_gt hLpos, ne_of_gt hvpos]
      nlinarith [hconst, hL3, hA3]
    exact hqraw.trans hcalc
  have hLin :
      2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
            (Nat.ceil (T / L) : ℝ)) ≤
        1 * T / v ^ 2 := by
    let w : ℝ := ((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1
    let y : ℝ := T / A - T / L
    have hwidth2 : w ^ 2 ≤ (2 * y) ^ 2 := by
      dsimp [w, y]
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hwidth
    have hdenpos : 0 < T / L := div_pos hTpos hLpos
    have hinv : 1 / (Nat.ceil (T / L) : ℝ) ≤ L / T := by
      exact (one_div_le_one_div_of_le hdenpos hk0ge).trans_eq (by
        field_simp [ne_of_gt hTpos, ne_of_gt hLpos])
    have hstep :
        2 * w ^ 2 / (Nat.ceil (T / L) : ℝ) ≤
          8 * y ^ 2 * (L / T) := by
      calc
        2 * w ^ 2 / (Nat.ceil (T / L) : ℝ) =
            2 * w ^ 2 * (1 / (Nat.ceil (T / L) : ℝ)) := by ring
        _ ≤ 2 * (2 * y) ^ 2 * (1 / (Nat.ceil (T / L) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hwidth2 (by norm_num)) (by positivity)
        _ ≤ 2 * (2 * y) ^ 2 * (L / T) := by
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 8 * y ^ 2 * (L / T) := by ring
    have hdiff : y = T * (L - A) / (A * L) := by
      dsimp [y]
      field_simp [ne_of_gt hApos, ne_of_gt hLpos]
    have hLminus : L - A = 4 * Real.log v := by dsimp [A, L]; ring
    have hstep' :
        8 * y ^ 2 * (L / T) =
          128 * T * (Real.log v) ^ 2 / (A ^ 2 * L) := by
      rw [hdiff, hLminus]
      field_simp [ne_of_gt hTpos, ne_of_gt hApos, ne_of_gt hLpos]
      ring
    have hA2 : ((997 / 1000 : ℝ) * v) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by positivity) hAge 2
    have hLlower : v ≤ L := by dsimp [L]; linarith
    have hdenom :
        ((997 / 1000 : ℝ) * v) ^ 2 * v ≤ A ^ 2 * L := by
      exact mul_le_mul hA2 hLlower (by positivity) (by positivity)
    have hfrac :
        128 * (Real.log v) ^ 2 / (A ^ 2 * L) ≤
          128 * (Real.log v) ^ 2 /
            (((997 / 1000 : ℝ) * v) ^ 2 * v) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hdenom
    have hvsq' : (Real.log v) ^ 2 ≤ (1 / 1000 : ℝ) * v := by
      exact (div_le_iff₀ hvpos).mp hvsq
    have hnum : 128 * (Real.log v) ^ 2 ≤
        (997 / 1000 : ℝ) ^ 2 * v := by
      have hc : (128 / 1000 : ℝ) ≤ (997 / 1000 : ℝ) ^ 2 := by norm_num
      nlinarith
    have hfrac' :
        128 * (Real.log v) ^ 2 /
            (((997 / 1000 : ℝ) * v) ^ 2 * v) ≤ 1 / v ^ 2 := by
      apply (div_le_iff₀ (by positivity : 0 <
        ((997 / 1000 : ℝ) * v) ^ 2 * v)).2
      have hv2 : 0 < v ^ 2 := sq_pos_of_pos hvpos
      field_simp [ne_of_gt hvpos]
      nlinarith [hnum]
    have hcore :
        8 * y ^ 2 * (L / T) ≤ T / v ^ 2 := by
      rw [hstep']
      have hmul := mul_le_mul_of_nonneg_left hfrac hTpos.le
      have hmul' := hmul.trans (mul_le_mul_of_nonneg_left hfrac' hTpos.le)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul'
    have hfinal := hstep.trans hcore
    simpa [w, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfinal
  have hsum := add_le_add hQ hLin
  have hsum' :
      16 * Real.exp (v + Real.log v) *
          ((v + Real.log v) /
            (Nat.ceil (Real.exp v / (v + Real.log v)) : ℝ)) ^ 2 /
            ((v + Real.log v) * Real.exp v) *
              (1 + Real.exp v / ((v - 3 * Real.log v) * (v + Real.log v))) ^ 3 +
        2 * ((((Nat.floor (Real.exp v / (v - 3 * Real.log v)) -
          Nat.ceil (Real.exp v / (v + Real.log v)) : ℕ) : ℝ) + 1) ^ 2 /
            (Nat.ceil (Real.exp v / (v + Real.log v)) : ℝ)) ≤
      17 * Real.exp v / v ^ 2 + 1 * Real.exp v / v ^ 2 := by
    simpa [T, A, L] using hsum
  calc
    _ ≤ 17 * Real.exp v / v ^ 2 + 1 * Real.exp v / v ^ 2 := hsum'
    _ = 18 * (Real.exp v / v ^ 2) := by ring
    _ ≤ 24 * (Real.exp v / v ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 24 * Real.exp v / v ^ 2 := by ring

end Erdos878

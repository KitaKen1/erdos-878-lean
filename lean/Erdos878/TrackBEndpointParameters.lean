import Erdos878.TrackBEndpointBridge

/-!
# Track B: concrete endpoint parameters

The remaining scalar construction starts here. The prime scale is the natural
ceiling of `log X * (log log X)^128`.
-/

namespace Erdos878.TrackB
open Filter
open scoped Topology
noncomputable section

def endpointT (X : ℕ) : ℝ := Real.log (X : ℝ)

def endpointV (X : ℕ) : ℝ := Real.log (endpointT X)

def endpointPrimeReal (X : ℕ) : ℝ := endpointT X * endpointV X ^ 128

def endpointPrimeScale (X : ℕ) : ℕ := Nat.ceil (endpointPrimeReal X)

def endpointLogScale (X : ℕ) : ℝ := Real.log (endpointPrimeScale X : ℝ)

def endpointSelectedCount (δ : ℝ) (X : ℕ) : ℕ :=
  Nat.floor ((1-δ)*endpointT X / Real.log ((16*endpointPrimeScale X : ℕ) : ℝ))

theorem tendsto_endpointT : Tendsto endpointT atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_endpointV : Tendsto endpointV atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (endpointT X)) atTop atTop
  exact Real.tendsto_log_atTop.comp tendsto_endpointT

theorem tendsto_endpointV_div_endpointT :
    Tendsto (fun X : ℕ => endpointV X / endpointT X) atTop (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, endpointV] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_endpointT

theorem eventually_endpointPrimeReal_ge_endpointT :
    ∀ᶠ X : ℕ in atTop, endpointT X ≤ endpointPrimeReal X := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop (1 : ℝ))] with X hT hV
  rw [endpointPrimeReal]
  exact le_mul_of_one_le_right hT (one_le_pow₀ hV)

theorem tendsto_endpointPrimeReal : Tendsto endpointPrimeReal atTop atTop :=
  Filter.tendsto_atTop_mono' atTop eventually_endpointPrimeReal_ge_endpointT tendsto_endpointT

theorem tendsto_endpointPrimeScale : Tendsto endpointPrimeScale atTop atTop := by
  change Tendsto (fun X : ℕ => Nat.ceil (endpointPrimeReal X)) atTop atTop
  exact tendsto_nat_ceil_atTop.comp tendsto_endpointPrimeReal

theorem eventually_endpointPrimeReal_nonneg :
    ∀ᶠ X : ℕ in atTop, 0 ≤ endpointPrimeReal X :=
  tendsto_endpointPrimeReal.eventually (eventually_ge_atTop 0)

theorem endpointPrimeScale_bounds {X : ℕ} (hA : 0 ≤ endpointPrimeReal X) :
    endpointPrimeReal X ≤ (endpointPrimeScale X : ℝ) ∧
      (endpointPrimeScale X : ℝ) < endpointPrimeReal X + 1 := by
  exact ⟨Nat.le_ceil _, by simpa only [endpointPrimeScale] using Nat.ceil_lt_add_one hA⟩

theorem tendsto_endpointLogScale : Tendsto endpointLogScale atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (endpointPrimeScale X : ℝ)) atTop atTop
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp tendsto_endpointPrimeScale)

theorem tendsto_log_endpointPrimeReal_div_endpointV :
    Tendsto (fun X : ℕ => Real.log (endpointPrimeReal X) / endpointV X)
      atTop (𝓝 1) := by
  have hlogdiv : Tendsto
      (fun X : ℕ => Real.log (endpointV X) / endpointV X) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_endpointV
  have hmain : Tendsto
      (fun X : ℕ => 1 + 128*(Real.log (endpointV X)/endpointV X))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (hlogdiv.const_mul 128))
  apply hmain.congr'
  filter_upwards [tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hT hV
  rw [endpointPrimeReal, Real.log_mul hT.ne' (pow_ne_zero 128 hV.ne'), Real.log_pow]
  have hTV : Real.log (endpointT X) = endpointV X := by rfl
  rw [hTV]
  field_simp
  ring

theorem tendsto_endpointLogScale_div_endpointV :
    Tendsto (fun X : ℕ => endpointLogScale X / endpointV X) atTop (𝓝 1) := by
  have hlower := tendsto_log_endpointPrimeReal_div_endpointV
  have hinv : Tendsto (fun X : ℕ => (endpointV X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointV
  have hconst : Tendsto (fun X : ℕ => Real.log 2 / endpointV X) atTop (𝓝 0) := by
    have hc : Tendsto (fun _X : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hc.mul hinv
  have hupper : Tendsto (fun X : ℕ =>
      Real.log (endpointPrimeReal X) / endpointV X + Real.log 2 / endpointV X)
      atTop (𝓝 1) := by
    simpa using hlower.add hconst
  have hbounds : ∀ᶠ X : ℕ in atTop,
      Real.log (endpointPrimeReal X) / endpointV X ≤
        endpointLogScale X / endpointV X ∧
      endpointLogScale X / endpointV X ≤
        Real.log (endpointPrimeReal X) / endpointV X + Real.log 2 / endpointV X := by
    filter_upwards [tendsto_endpointPrimeReal.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hA hV
    have hA0 : 0 ≤ endpointPrimeReal X := hA.trans' zero_le_one
    obtain ⟨hceilLo, hceilHi⟩ := endpointPrimeScale_bounds hA0
    have hceilUpper : (endpointPrimeScale X : ℝ) ≤ 2*endpointPrimeReal X := by linarith
    have hPpos : (0 : ℝ) < endpointPrimeScale X :=
      zero_lt_one.trans_le (hA.trans hceilLo)
    have hlogLo : Real.log (endpointPrimeReal X) ≤
        Real.log (endpointPrimeScale X : ℝ) :=
      Real.log_le_log (zero_lt_one.trans_le hA) hceilLo
    have hlogHi : Real.log (endpointPrimeScale X : ℝ) ≤
        Real.log (2*endpointPrimeReal X) := Real.log_le_log hPpos hceilUpper
    have hlogMul : Real.log (2*endpointPrimeReal X) =
        Real.log 2 + Real.log (endpointPrimeReal X) :=
      Real.log_mul (by norm_num) (zero_lt_one.trans_le hA).ne'
    constructor
    · exact div_le_div_of_nonneg_right hlogLo hV.le
    · calc
        endpointLogScale X / endpointV X ≤
            Real.log (2*endpointPrimeReal X) / endpointV X := by
          exact div_le_div_of_nonneg_right (by simpa only [endpointLogScale] using hlogHi) hV.le
        _ = Real.log (endpointPrimeReal X) / endpointV X +
            Real.log 2 / endpointV X := by rw [hlogMul]; ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem tendsto_endpointBandLog_div_endpointV :
    Tendsto (fun X : ℕ =>
      Real.log ((16*endpointPrimeScale X : ℕ) : ℝ) / endpointV X)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun X : ℕ => (endpointV X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointV
  have hc : Tendsto (fun X : ℕ => Real.log 16 / endpointV X) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _X : ℕ => Real.log 16) atTop (𝓝 (Real.log 16)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hconst.mul hinv
  have hmain : Tendsto (fun X : ℕ =>
      endpointLogScale X / endpointV X + Real.log 16 / endpointV X)
      atTop (𝓝 1) := by
    simpa using tendsto_endpointLogScale_div_endpointV.add hc
  refine hmain.congr' ?_
  filter_upwards [tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hP
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hP
  rw [show (((16*endpointPrimeScale X : ℕ) : ℝ)) =
    (16 : ℝ)*(endpointPrimeScale X : ℝ) by norm_num, Real.log_mul (by norm_num) hPr.ne']
  simp only [endpointLogScale]
  ring

theorem eventually_endpointLogScale_between_half_two :
    ∀ᶠ X : ℕ in atTop,
      endpointV X/2 ≤ endpointLogScale X ∧ endpointLogScale X ≤ 2*endpointV X := by
  have hlo : ∀ᶠ X : ℕ in atTop,
      (1/2 : ℝ) < endpointLogScale X / endpointV X :=
    (tendsto_order.1 tendsto_endpointLogScale_div_endpointV).1 _ (by norm_num)
  have hhi : ∀ᶠ X : ℕ in atTop,
      endpointLogScale X / endpointV X < 2 :=
    (tendsto_order.1 tendsto_endpointLogScale_div_endpointV).2 _ (by norm_num)
  filter_upwards [hlo, hhi,
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hlo hhi hV
  have hlo' := (lt_div_iff₀ hV).mp hlo
  have hhi' := (div_lt_iff₀ hV).mp hhi
  constructor <;> nlinarith

theorem eventually_endpointT_in_frequencyWindow :
    ∀ᶠ X : ℕ in atTop,
      (endpointPrimeScale X : ℝ)/endpointLogScale X^130 ≤ endpointT X ∧
      endpointT X ≤ (endpointPrimeScale X : ℝ)/endpointLogScale X^126 := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop ((2 : ℝ)^66)),
    eventually_endpointLogScale_between_half_two] with X hT hV hLbounds
  let v := endpointV X
  let L := endpointLogScale X
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hL0 : 0 < L := by dsimp [L]; nlinarith [hLbounds.1]
  have hvv : (2 : ℝ)^132 ≤ v^2 := by
    have hm := mul_le_mul hV hV (by positivity : (0 : ℝ) ≤ (2 : ℝ)^66)
      (by positivity : 0 ≤ endpointV X)
    calc
      (2 : ℝ)^132 = (2 : ℝ)^66*(2 : ℝ)^66 := by ring
      _ ≤ endpointV X*endpointV X := hm
      _ = v^2 := by simp only [v]; ring
  have hA0 : 0 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    positivity
  obtain ⟨hPlo, hPhi⟩ := endpointPrimeScale_bounds hA0
  have hAone : 1 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    have hvpow : 1 ≤ endpointV X^128 := one_le_pow₀ (le_trans (by norm_num) hV)
    nlinarith [mul_le_mul hT hvpow (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans hT)]
  have hPupper : (endpointPrimeScale X : ℝ) ≤
      2*endpointT X*v^128 := by
    calc
      (endpointPrimeScale X : ℝ) ≤ 2*endpointPrimeReal X := by linarith
      _ = 2*endpointT X*v^128 := by simp only [endpointPrimeReal, v]; ring
  have h2lo : (2 : ℝ)^131 ≤ v^2 :=
    (show (2 : ℝ)^131 ≤ (2 : ℝ)^132 by norm_num).trans hvv
  have hcoefLower : 2*v^128 ≤ (v/2)^130 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos (by norm_num) 130)).2
    calc
      (2*v^128)*2^130 = v^128*(2 : ℝ)^131 := by ring
      _ ≤ v^128*v^2 := mul_le_mul_of_nonneg_left h2lo (pow_nonneg hv0.le 128)
      _ = v^130 := by ring
  have hpowLower : 2*v^128 ≤ L^130 := by
    exact hcoefLower.trans (pow_le_pow_left₀ (by positivity) (by simpa only [v, L] using hLbounds.1) 130)
  have hfrequencyLower : (endpointPrimeScale X : ℝ)/L^130 ≤ endpointT X := by
    apply (div_le_iff₀ (pow_pos hL0 130)).2
    calc
      (endpointPrimeScale X : ℝ) ≤ 2*endpointT X*v^128 := hPupper
      _ = endpointT X*(2*v^128) := by ring
      _ ≤ endpointT X*L^130 := mul_le_mul_of_nonneg_left hpowLower (zero_le_one.trans hT)
  have h2hi : (2 : ℝ)^126 ≤ v^2 :=
    (show (2 : ℝ)^126 ≤ (2 : ℝ)^132 by norm_num).trans hvv
  have hcoefUpper : (2*v)^126 ≤ v^128 := by
    rw [mul_pow]
    calc
      (2 : ℝ)^126*v^126 ≤ v^2*v^126 :=
        mul_le_mul_of_nonneg_right h2hi (pow_nonneg hv0.le 126)
      _ = v^128 := by ring
  have hpowUpper : L^126 ≤ v^128 := by
    exact (pow_le_pow_left₀ hL0.le (by simpa only [v, L] using hLbounds.2) 126).trans
      hcoefUpper
  have hfrequencyUpper : endpointT X ≤ (endpointPrimeScale X : ℝ)/L^126 := by
    apply (le_div_iff₀ (pow_pos hL0 126)).2
    calc
      endpointT X*L^126 ≤ endpointT X*v^128 :=
        mul_le_mul_of_nonneg_left hpowUpper (zero_le_one.trans hT)
      _ = endpointPrimeReal X := by rw [endpointPrimeReal]
      _ ≤ (endpointPrimeScale X : ℝ) := hPlo
  simpa only [L] using And.intro hfrequencyLower hfrequencyUpper

/-- The concrete number of selected primes is eventually far below the supply
`P / (2 log(P)^7)`.  The large exponent `128` makes this a purely elementary
comparison once `log P` is within fixed multiples of `log log X`. -/
theorem eventually_endpointSelectedCount_le_primeCapacity
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      (endpointSelectedCount δ X : ℝ) ≤
        (endpointPrimeScale X : ℝ) / (2 * endpointLogScale X ^ 7) := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_endpointV.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_endpointLogScale_between_half_two,
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with
      X hT hV hLbounds hPnat
  let v := endpointV X
  let L := endpointLogScale X
  let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
  have hv0 : 0 < v := by dsimp [v]; linarith
  have hL0 : 0 < L := by dsimp [L]; nlinarith [hLbounds.1]
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hPnat
  have hBformula : B = Real.log 16 + L := by
    dsimp only [B, L, endpointLogScale]
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact Real.log_mul (by norm_num) hPr.ne'
  have hLB : L ≤ B := by
    rw [hBformula]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 16)]
  have hvB : v / 2 ≤ B := hLbounds.1.trans hLB
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity : 0 < v / 2) hvB
  have hnum0 : 0 ≤ (1 - δ) * endpointT X :=
    mul_nonneg (sub_nonneg.mpr hδ1) (zero_le_one.trans hT)
  have hnum_le : (1 - δ) * endpointT X ≤ endpointT X := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - δ ≤ 1)
      (zero_le_one.trans hT)
    simpa using this
  have hraw0 : 0 ≤ (1 - δ) * endpointT X / B := div_nonneg hnum0 hB0.le
  have hfloor : (endpointSelectedCount δ X : ℝ) ≤
      (1 - δ) * endpointT X / B := by
    simpa only [endpointSelectedCount, B] using Nat.floor_le hraw0
  have hraw_le : (1 - δ) * endpointT X / B ≤ 2 * endpointT X / v := by
    calc
      (1 - δ) * endpointT X / B ≤ endpointT X / B :=
        div_le_div_of_nonneg_right hnum_le hB0.le
      _ ≤ endpointT X / (v / 2) :=
        div_le_div_of_nonneg_left (zero_le_one.trans hT) (by positivity) hvB
      _ = 2 * endpointT X / v := by field_simp
  have hv122 : (512 : ℝ) ≤ v ^ 122 := by
    calc
      (512 : ℝ) ≤ (2 : ℝ) ^ 122 := by norm_num
      _ ≤ v ^ 122 := pow_le_pow_left₀ (by norm_num) (by simpa only [v] using hV) 122
  have hwideDen0 : 0 < 2 * (2 * v) ^ 7 := by positivity
  have hcompare : 2 * endpointT X / v ≤
      endpointT X * v ^ 128 / (2 * (2 * v) ^ 7) := by
    apply (div_le_div_iff₀ hv0 hwideDen0).2
    have hm := mul_le_mul_of_nonneg_left hv122
      (mul_nonneg (zero_le_one.trans hT) (pow_nonneg hv0.le 7))
    calc
      (2 * endpointT X) * (2 * (2 * v) ^ 7) =
          (endpointT X * v ^ 7) * 512 := by ring
      _ ≤ (endpointT X * v ^ 7) * v ^ 122 := hm
      _ = (endpointT X * v ^ 128) * v := by ring
  have hA0 : 0 ≤ endpointPrimeReal X := by
    rw [endpointPrimeReal]
    positivity
  have hPlo : endpointT X * v ^ 128 ≤ (endpointPrimeScale X : ℝ) := by
    have := (endpointPrimeScale_bounds hA0).1
    simpa only [endpointPrimeReal, v] using this
  have hLpow : L ^ 7 ≤ (2 * v) ^ 7 :=
    pow_le_pow_left₀ hL0.le (by simpa only [L, v] using hLbounds.2) 7
  have hnarrowDen0 : 0 < 2 * L ^ 7 := by positivity
  have hden : 2 * L ^ 7 ≤ 2 * (2 * v) ^ 7 :=
    mul_le_mul_of_nonneg_left hLpow (by norm_num)
  have hcapacityLower : endpointT X * v ^ 128 / (2 * (2 * v) ^ 7) ≤
      (endpointPrimeScale X : ℝ) / (2 * L ^ 7) := by
    apply (div_le_div_iff₀ hwideDen0 hnarrowDen0).2
    calc
      (endpointT X * v ^ 128) * (2 * L ^ 7) ≤
          (endpointPrimeScale X : ℝ) * (2 * L ^ 7) :=
        mul_le_mul_of_nonneg_right hPlo hnarrowDen0.le
      _ ≤ (endpointPrimeScale X : ℝ) * (2 * (2 * v) ^ 7) :=
        mul_le_mul_of_nonneg_left hden hPr.le
  simpa only [L] using hfloor.trans (hraw_le.trans (hcompare.trans hcapacityLower))

/-- The power-sum upper endpoint and the product of the selected primes fit
simultaneously below `X`.  A fixed loss `δ` makes the product at most
`exp ((1-δ)T)`, while the shift `1/log P` leaves enough room below `exp T`. -/
theorem eventually_endpoint_additiveBudget
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      Real.exp (endpointT X - 1 / endpointLogScale X) +
          ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
        (X : ℝ) := by
  have hsmall : ∀ᶠ X : ℕ in atTop,
      endpointV X / endpointT X < δ / 4 :=
    (tendsto_order.1 tendsto_endpointV_div_endpointT).2 _ (by linarith)
  filter_upwards [hsmall,
    tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointLogScale.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_endpointLogScale_between_half_two,
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0),
    eventually_gt_atTop (0 : ℕ)] with X hsmallX hT hV hLone hLbounds hPnat hXnat
  let T := endpointT X
  let v := endpointV X
  let L := endpointLogScale X
  let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
  let a := 1 / L
  have hT0 : 0 < T := by simpa only [T] using hT
  have hv0 : 0 < v := by simpa only [v] using hV
  have hL0 : 0 < L := by dsimp [L]; linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one hL0).2 hLone
  have hPr : (0 : ℝ) < endpointPrimeScale X := by exact_mod_cast hPnat
  have hQnat : 0 < 16 * endpointPrimeScale X := Nat.mul_pos (by norm_num) hPnat
  have hQr : (0 : ℝ) < ((16 * endpointPrimeScale X : ℕ) : ℝ) := by
    exact_mod_cast hQnat
  have hB0 : 0 < B := by
    dsimp only [B]
    exact Real.log_pos (by exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega))
  have hfourv : 4 * v ≤ δ * T := by
    have hratio : v / T < δ / 4 := by simpa only [v, T] using hsmallX
    have hmul := (div_lt_iff₀ hT0).mp hratio
    nlinarith
  have htwoL : 2 * L ≤ Real.exp (δ * T) := by
    calc
      2 * L ≤ 4 * v := by
        have := mul_le_mul_of_nonneg_left
          (by simpa only [L, v] using hLbounds.2) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
      _ ≤ δ * T := hfourv
      _ ≤ δ * T + 1 := by linarith
      _ ≤ Real.exp (δ * T) := Real.add_one_le_exp _
  have htwoLpos : 0 < 2 * L := by positivity
  have hexpNegDelta : Real.exp (-δ * T) ≤ a / 2 := by
    have hinv := one_div_le_one_div_of_le htwoLpos htwoL
    calc
      Real.exp (-δ * T) = 1 / Real.exp (δ * T) := by
        rw [show -δ * T = -(δ * T) by ring, Real.exp_neg]
        simp only [one_div]
      _ ≤ 1 / (2 * L) := hinv
      _ = a / 2 := by dsimp only [a]; field_simp
  have hexpNegA : Real.exp (-a) ≤ 1 - a / 2 := by
    have hdenExp : 1 + a ≤ Real.exp a := by
      simpa only [add_comm] using Real.add_one_le_exp a
    have hrecip : Real.exp (-a) ≤ 1 / (1 + a) := by
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdenExp
    have hrational : 1 / (1 + a) ≤ 1 - a / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + a)).2
      have hprod : 0 ≤ a * (1 - a) := mul_nonneg ha0.le (sub_nonneg.mpr ha1)
      nlinarith
    exact hrecip.trans hrational
  have hmain : Real.exp (T - a) ≤ Real.exp T * (1 - a / 2) := by
    rw [show T - a = T + (-a) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hexpNegA (Real.exp_pos T).le
  have hraw0 : 0 ≤ (1 - δ) * T / B :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hδ1) hT0.le) hB0.le
  have hfloor : (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T / B := by
    simpa only [endpointSelectedCount, T, B] using Nat.floor_le hraw0
  have hexponent : B * (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T := by
    have := mul_le_mul_of_nonneg_left hfloor hB0.le
    field_simp at this
    exact this
  have hproduct :
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
        Real.exp ((1 - δ) * T) := by
    calc
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) =
          ((16 * endpointPrimeScale X : ℕ) : ℝ) ^ endpointSelectedCount δ X := by
            norm_num
      _ = Real.exp ((endpointSelectedCount δ X : ℝ) * B) := by
        symm
        rw [Real.exp_nat_mul]
        dsimp only [B]
        rw [Real.exp_log hQr]
      _ = Real.exp (B * (endpointSelectedCount δ X : ℝ)) := by
        congr 1
        exact mul_comm _ _
      _ ≤ Real.exp ((1 - δ) * T) := Real.exp_le_exp.mpr hexponent
  have hsecondary : Real.exp ((1 - δ) * T) ≤ Real.exp T * (a / 2) := by
    calc
      Real.exp ((1 - δ) * T) = Real.exp T * Real.exp (-δ * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp T * (a / 2) :=
        mul_le_mul_of_nonneg_left hexpNegDelta (Real.exp_pos T).le
  have hsum : Real.exp (T - a) +
      ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
      Real.exp T := by
    calc
      Real.exp (T - a) +
          ((((16 * endpointPrimeScale X) ^ endpointSelectedCount δ X : ℕ) : ℝ)) ≤
          Real.exp T * (1 - a / 2) + Real.exp ((1 - δ) * T) :=
        add_le_add hmain hproduct
      _ ≤ Real.exp T * (1 - a / 2) + Real.exp T * (a / 2) :=
        add_le_add_right hsecondary _
      _ = Real.exp T := by ring
  have hexpT : Real.exp T = (X : ℝ) := by
    dsimp only [T, endpointT]
    exact Real.exp_log (by exact_mod_cast hXnat)
  simpa only [T, L, a, hexpT] using hsum

theorem tendsto_endpointV_div_endpointBandLog :
    Tendsto (fun X : ℕ => endpointV X /
      Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hinv := tendsto_endpointBandLog_div_endpointV.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  have hinv' : Tendsto (fun X : ℕ =>
      (Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ) / endpointV X)⁻¹)
      atTop (𝓝 1) := by simpa using hinv
  apply hinv'.congr'
  filter_upwards [tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hV hP
  have hQ : (0 : ℝ) < ((16 * endpointPrimeScale X : ℕ) : ℝ) := by positivity
  have hlogQ : 0 < Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega)
  field_simp

/-- After normalization by `T/log log X`, the number of selected primes tends
to the intended density factor `1-δ`; the floor contributes only
`O(log log X / log X)`. -/
theorem tendsto_endpointSelectedCount_normalized
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X)
      atTop (𝓝 (1 - δ)) := by
  have hupper : Tendsto (fun X : ℕ =>
      (1 - δ) * (endpointV X /
        Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)))
      atTop (𝓝 (1 - δ)) := by
    simpa using tendsto_const_nhds.mul tendsto_endpointV_div_endpointBandLog
  have hlower : Tendsto (fun X : ℕ =>
      (1 - δ) * (endpointV X /
        Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
        endpointV X / endpointT X)
      atTop (𝓝 (1 - δ)) := by
    simpa using hupper.sub tendsto_endpointV_div_endpointT
  have hbounds : ∀ᶠ X : ℕ in atTop,
      (1 - δ) * (endpointV X /
          Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
          endpointV X / endpointT X ≤
        (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X ∧
      (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X ≤
        (1 - δ) * (endpointV X /
          Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) := by
    filter_upwards [tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_endpointPrimeScale.eventually (eventually_gt_atTop 0)] with X hT hV hPnat
    let T := endpointT X
    let v := endpointV X
    let B := Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)
    have hT0 : 0 < T := by simpa only [T] using hT
    have hv0 : 0 < v := by simpa only [v] using hV
    have hB0 : 0 < B := by
      dsimp only [B]
      apply Real.log_pos
      exact_mod_cast (show 1 < 16 * endpointPrimeScale X by omega)
    have hraw0 : 0 ≤ (1 - δ) * T / B :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hδ1) hT0.le) hB0.le
    have hfloorUpper : (endpointSelectedCount δ X : ℝ) ≤ (1 - δ) * T / B := by
      simpa only [endpointSelectedCount, T, B] using Nat.floor_le hraw0
    have hfloorLower : (1 - δ) * T / B - 1 ≤
        (endpointSelectedCount δ X : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((1 - δ) * T / B)
      have hlt' : (1 - δ) * T / B <
          (endpointSelectedCount δ X : ℝ) + 1 := by
        simpa only [endpointSelectedCount, T, B] using hlt
      linarith
    have hfactor0 : 0 ≤ v / T := div_nonneg hv0.le hT0.le
    have hlo := mul_le_mul_of_nonneg_right hfloorLower hfactor0
    have hhi := mul_le_mul_of_nonneg_right hfloorUpper hfactor0
    constructor
    · calc
        (1 - δ) * (endpointV X /
            Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) -
            endpointV X / endpointT X =
            ((1 - δ) * T / B - 1) * (v / T) := by
              simp only [T, v, B]
              field_simp
        _ ≤ (endpointSelectedCount δ X : ℝ) * (v / T) := hlo
        _ = (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X := by
          simp only [T, v]
          ring
    · calc
        (endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X =
            (endpointSelectedCount δ X : ℝ) * (v / T) := by
          simp only [T, v]
          ring
        _ ≤ ((1 - δ) * T / B) * (v / T) := hhi
        _ = (1 - δ) * (endpointV X /
            Real.log ((16 * endpointPrimeScale X : ℕ) : ℝ)) := by
          simp only [T, v, B]
          field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem tendsto_endpointExpShift :
    Tendsto (fun X : ℕ => Real.exp (-4 / endpointLogScale X))
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun X : ℕ => (endpointLogScale X)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_endpointLogScale
  have harg : Tendsto (fun X : ℕ => -4 / endpointLogScale X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (-4)
  simpa only [Function.comp_def, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp harg

/-- The explicit endpoint construction has limiting normalized weight
`1-δ`.  This is the final scalar asymptotic needed by the endpoint bridge. -/
theorem tendsto_endpointNormalizedWeight
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (endpointSelectedCount δ X : ℝ) *
          Real.exp (endpointT X - 4 / endpointLogScale X) /
        Erdos878.maximalOrderScale X)
      atTop (𝓝 (1 - δ)) := by
  have hprod := (tendsto_endpointSelectedCount_normalized hδ1).mul
    tendsto_endpointExpShift
  have hprod' : Tendsto (fun X : ℕ =>
      ((endpointSelectedCount δ X : ℝ) * endpointV X / endpointT X) *
        Real.exp (-4 / endpointLogScale X)) atTop (𝓝 (1 - δ)) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_endpointT.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_endpointV.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hT hV
  let T := endpointT X
  let v := endpointV X
  let L := endpointLogScale X
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hT0 : 0 < T := by simpa only [T] using hT
  have hv0 : 0 < v := by simpa only [v] using hV
  have hexpT : Real.exp T = (X : ℝ) := by
    dsimp only [T, endpointT]
    exact Real.exp_log hXr
  have hshift : Real.exp (T - 4 / L) =
      (X : ℝ) * Real.exp (-4 / L) := by
    rw [show T - 4 / L = T + (-4 / L) by ring, Real.exp_add, hexpT]
  have hscale : Erdos878.maximalOrderScale X = (X : ℝ) * T / v := by
    rfl
  rw [hshift, hscale]
  field_simp
  ring

theorem eventually_endpointNormalizedWeight_ge_one_sub
    {δ ε : ℝ} (hδ1 : δ ≤ 1) (hδε : δ < ε) :
    ∀ᶠ X : ℕ in atTop,
      1 - ε ≤
        (endpointSelectedCount δ X : ℝ) *
            Real.exp (endpointT X - 4 / endpointLogScale X) /
          Erdos878.maximalOrderScale X := by
  have hstrict : 1 - ε < 1 - δ := by linarith
  exact ((tendsto_order.1 (tendsto_endpointNormalizedWeight hδ1)).1 _ hstrict).mono
    (fun _ h => h.le)

/-- Every scalar condition required by `TrackBEndpointBridge` is met by the
explicit endpoint parameters. -/
theorem eventually_endpointConditions_concrete
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδε : δ < ε) :
    ∀ᶠ X : ℕ in atTop,
      endpointConditions ε X (endpointPrimeScale X)
        (endpointSelectedCount δ X) (endpointT X) := by
  filter_upwards [tendsto_endpointT.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_endpointT_in_frequencyWindow,
    eventually_endpointSelectedCount_le_primeCapacity hδ0.le hδ1,
    eventually_endpoint_additiveBudget hδ0 hδ1,
    Erdos878.eventually_maximalOrderScale_pos,
    eventually_endpointNormalizedWeight_ge_one_sub hδ1 hδε] with
      X hT hfrequency hcapacity hbudget hscale hnormalized
  exact ⟨hT, hfrequency.1, hfrequency.2, hcapacity, hbudget, hscale, hnormalized⟩

/-- The concrete prime scale and selection count prove Question 2. -/
theorem second_question_of_concreteEndpoints : erdos_878.parts.ii := by
  apply second_question_of_endpointParameters
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    exact lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ ≤ 1 := by
    exact (min_le_right (ε / 2) (1 / 2)).trans (by norm_num)
  have hδε : δ < ε := by
    exact (min_le_left (ε / 2) (1 / 2)).trans_lt (half_lt_self hε)
  exact ⟨endpointPrimeScale, endpointSelectedCount δ, endpointT,
    tendsto_endpointPrimeScale,
    eventually_endpointConditions_concrete hδ0 hδ1 hδε⟩

/-- Exact second-question name used by the complete FClike natural-language
statement package. -/
theorem erdos_878_parts_ii_proved : erdos_878.parts.ii := by
  exact second_question_of_concreteEndpoints

end
end Erdos878.TrackB

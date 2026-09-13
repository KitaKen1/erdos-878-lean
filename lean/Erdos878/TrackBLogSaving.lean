import Erdos878.TrackBParameters

/-!
# Track B: logarithmic saving on the concrete frequency window

All powers in the finite estimates are natural powers. The scale condition is
eventual, and the estimates are uniform in the frequency and partial endpoint.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

theorem trackBFrequency_positive_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) : 0 < a ∧ a ≤ (P : ℝ) := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P h; omega)
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  exact ⟨(div_pos hP (pow_pos hL _)).trans_le hlo,
    hhi.trans (div_le_self hP.le (one_le_pow₀ h.1))⟩

theorem trackBFrequency_sqrt_lower (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a) :
    Real.sqrt (P : ℝ) ≤ Real.sqrt a * Real.log (P : ℝ)^65 := by
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ a * Real.log (P : ℝ)^130 := (div_le_iff₀ (pow_pos hL _)).mp hlo
    _ = _ := by rw [mul_pow, Real.sq_sqrt ha.le]; ring

theorem trackBFrequencyRoot_upper (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    typeIIFrequencyRoot a P * Real.log (P : ℝ)^61 ≤ Real.sqrt (P : ℝ) := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hg := typeIIFrequencyRoot_pos a P ha h.1
  have hg2 : typeIIFrequencyRoot a P ^ 2 = a/(32*L^3) := Real.sq_sqrt (by positivity)
  have he : (typeIIFrequencyRoot a P * L^61)^2 = a*L^119/32 := by
    rw [mul_pow, hg2]
    field_simp
  have ha120 : a*L^120 ≤ (P : ℝ) := (le_div_iff₀ (pow_pos hL _)).mp hhi
  have ha119 : a*L^119 ≤ (P : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.1 (show 119 ≤ 120 by decide)) ha.le).trans ha120
  have hs := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hS := Real.sqrt_nonneg (P : ℝ)
  change typeIIFrequencyRoot a P * L^61 ≤ Real.sqrt (P : ℝ)
  nlinarith

theorem trackBFrequencyRoot_lower (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (ha : 0 < a) (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a) :
    Real.sqrt (P : ℝ) ≤ 6 * typeIIFrequencyRoot a P * Real.log (P : ℝ)^67 := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hg := typeIIFrequencyRoot_pos a P ha h.1
  have hg2 : typeIIFrequencyRoot a P ^ 2 = a/(32*L^3) := Real.sq_sqrt (by positivity)
  have he : (6*typeIIFrequencyRoot a P * L^67)^2 = (36/32 : ℝ)*(a*L^130)*L := by
    rw [mul_pow, mul_pow, hg2]
    field_simp
    ring
  have ha130 : (P : ℝ) ≤ a*L^130 := (div_le_iff₀ (pow_pos hL _)).mp hlo
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  change (P : ℝ) ≤ (6*typeIIFrequencyRoot a P * L^67)^2
  rw [he]
  have hm := mul_le_mul_of_nonneg_left h.1 (show 0 ≤ a*L^130 by positivity)
  nlinarith

/-- The complete normalized Type-II error is at most a square with integer powers. -/
theorem typeIIUniformError_logSaving_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    typeIIUniformError a P (trackBCutoff P) ≤ 22500 / Real.log (P : ℝ)^60 := by
  let L := Real.log (P : ℝ)
  let g := typeIIFrequencyRoot a P
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have ha := (trackBFrequency_positive_le a P h hlo hhi).1
  have hg : 0 < g := typeIIFrequencyRoot_pos a P ha h.1
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P h; omega)
  have hS : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP
  have hK : L^60 ≤ (trackBCutoff P : ℝ) :=
    (pow_le_pow_right₀ h.1 (show 60 ≤ 64 by decide)).trans (trackBCutoff_bounds P h.1).1
  have hd : 2/(trackBCutoff P : ℝ) ≤ 2/L^60 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hL _) hK
  have hgu : g*L^60 ≤ Real.sqrt (P : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.1 (show 60 ≤ 61 by decide)) hg.le).trans
      (trackBFrequencyRoot_upper a P h ha hhi)
  have hu : 20480*g/Real.sqrt (P : ℝ) ≤ 20480/L^60 := by
    apply (div_le_div_iff₀ hS (pow_pos hL _)).2
    nlinarith
  have hp : 4*L^127 ≤ 6*g*L^67 := by
    calc
      _ ≤ 4*L^200 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ Real.sqrt (P : ℝ) := trackBScaleCondition_sqrt_lower P h
      _ ≤ _ := trackBFrequencyRoot_lower a P h ha hlo
  have hp' : (4*L^60)*L^67 ≤ (6*g)*L^67 := by convert hp using 1; ring
  have hgl := le_of_mul_le_mul_right hp' (pow_pos hL 67)
  have hl : 40/g ≤ 60/L^60 := by
    apply (div_le_div_iff₀ hg (pow_pos hL _)).2
    nlinarith
  change 2/(trackBCutoff P : ℝ) + 20480*g/Real.sqrt (P : ℝ) + 40/g ≤ 22500/L^60
  have hsum := add_le_add (add_le_add hd hu) hl
  have hden : 0 < L^60 := pow_pos hL _
  calc
    _ ≤ 2/L^60 + 20480/L^60 + 60/L^60 := hsum
    _ ≤ _ := by rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hden.le

theorem sqrt_typeIIUniformError_logSaving_le (a : ℝ) (P : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120) :
    Real.sqrt (typeIIUniformError a P (trackBCutoff P)) ≤ 150/Real.log (P : ℝ)^30 := by
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, (typeIIUniformError_logSaving_le a P h hlo hhi).trans_eq ?_⟩
  field_simp
  ring

/-- All endpoint logarithms are controlled by `log P`, uniformly in `X ≤ CP`. -/
theorem trackBEndpoint_log_bounds (C : ℝ) (P X : ℕ) (h : trackBScaleCondition P)
    (hCP : C ≤ (P : ℝ)) (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) :
    Real.log (X : ℝ) ≤ 2*Real.log (P : ℝ) ∧
    Real.log (X+1 : ℕ) ≤ 3*Real.log (P : ℝ) ∧
    typeIICommonLog X ≤ 4*Real.log (P : ℝ) := by
  have hP16 : (16 : ℝ) ≤ P := by exact_mod_cast trackBScaleCondition_sixteen_le P h
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hX0 : (0 : ℝ) < X := hP0.trans_le (by exact_mod_cast hPX)
  have hXs : (X : ℝ) ≤ (P : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_right hCP hP0.le]
  have hp2 : (1 : ℝ) ≤ (P : ℝ)^2 := one_le_pow₀ hP1
  have hp3 := mul_le_mul_of_nonneg_right hP16 (sq_nonneg (P : ℝ))
  have hX3 : (X+1 : ℕ) ≤ (P : ℝ)^3 := by push_cast; nlinarith
  have hX23 : 2*(X : ℝ)+1 ≤ (P : ℝ)^3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ Real.log ((P : ℝ)^2) := Real.log_le_log hX0 hXs
      _ = _ := by rw [Real.log_pow]; norm_num
  · calc
      _ ≤ Real.log ((P : ℝ)^3) := Real.log_le_log (by positivity) hX3
      _ = _ := by rw [Real.log_pow]; norm_num
  · have ht := Real.log_le_log (by positivity : (0 : ℝ) < 2*X+1) hX23
    rw [Real.log_pow] at ht
    dsimp [typeIICommonLog]
    norm_num at ht
    linarith [h.1]

/-- The Type-II contribution now has the required 25 logarithms of saving. -/
theorem norm_weightedArithmeticSum_typeII_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
      (vaughanTypeII (trackBCutoff P) (trackBCutoff P))‖ ≤
      691200 * C * P / Real.log (P : ℝ)^25 := by
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have ht := norm_weightedArithmeticSum_typeII_le_uniform_endpoint a C
    (trackBCutoff P) (trackBCutoff P) P Y X ha.1 ha.2 hCr hP h.1 hCP hX hYX
    (trackBCutoff_pos P h.1) (trackBCutoff_pos P h.1)
  simp only [min_self] at ht
  obtain ⟨hlogX, hlogX1, hHX⟩ := trackBEndpoint_log_bounds C P X h hCP hPX hX
  have herr := sqrt_typeIIUniformError_logSaving_le a P h hlo hhi
  have hlogX0 := Real.log_natCast_nonneg X
  have hHX0 : 0 ≤ typeIICommonLog X := zero_le_one.trans (one_le_typeIICommonLog X)
  refine ht.trans ?_
  calc
    _ ≤ 18*(C*P)*(2*Real.log (P : ℝ))^2*(4*Real.log (P : ℝ))^3*
        (150/Real.log (P : ℝ)^30) := by gcongr
    _ = _ := by field_simp; ring

/-- A coarse Type-I outer bound suffices with the polylogarithmic cutoff. -/
theorem typeIOuterBound_le_polylog (a C : ℝ) (P D : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hD : 0 < D) (hDP : D ≤ P)
    (hDb : (D : ℝ) ≤ 4*Real.log (P : ℝ)^128) :
    typeIOuterBound a C P D ≤
      280*C^2*Real.sqrt (P : ℝ)*Real.log (P : ℝ)^128 := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hCC : C ≤ C^2 := by nlinarith
  have hA : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha.1
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hAS : Real.sqrt a / L ≤ S :=
    (div_le_self (Real.sqrt_nonneg _) h.1).trans (Real.sqrt_le_sqrt ha.2)
  have hlogD : Real.log (D : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hD) (by exact_mod_cast hDP)
  have hlogD0 := Real.log_natCast_nonneg D
  have hlogD1 : 1+Real.log (D : ℝ) ≤ 2*L := by linarith [h.1]
  have hPA : (P : ℝ)/Real.sqrt a ≤ S*L^65 := by
    apply (div_le_iff₀ hA).2
    calc
      _ = S*S := by dsimp [S]; nlinarith [Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)]
      _ ≤ S*(Real.sqrt a * L^65) := mul_le_mul_of_nonneg_left
        (trackBFrequency_sqrt_lower a P h ha.1 hlo) hS
      _ = _ := by ring
  have hfirst : 60*C^2*Real.sqrt a/L*D ≤ 240*C^2*S*L^128 := by
    calc
      _ = 60*C^2*(Real.sqrt a/L)*D := by ring
      _ ≤ 60*C^2*S*(4*L^128) := by gcongr
      _ = _ := by ring
  have hsecond : (20*C*P*L/Real.sqrt a)*(1+Real.log (D : ℝ)) ≤ 40*C^2*S*L^128 := by
    calc
      _ = 20*C*((P : ℝ)/Real.sqrt a)*L*(1+Real.log (D : ℝ)) := by ring
      _ ≤ 20*C*(S*L^65)*L*(2*L) := by gcongr
      _ = 40*C*S*L^67 := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCC (by norm_num)) hS)
        (pow_le_pow_right₀ h.1 (by decide)) (pow_nonneg hL.le _) (by positivity)
  calc
    _ ≤ 240*C^2*S*L^128 + 40*C^2*S*L^128 := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Polynomial room in the scale condition absorbs every remaining Type-I logarithm. -/
theorem sqrt_mul_log_pow_le_logSaving (P : ℕ) (h : trackBScaleCondition P) :
    Real.sqrt (P : ℝ)*Real.log (P : ℝ)^129 ≤ (P : ℝ)/Real.log (P : ℝ)^25 := by
  let L := Real.log (P : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hp : L^154 ≤ Real.sqrt (P : ℝ) := by
    calc
      _ ≤ L^200 := pow_le_pow_right₀ h.1 (by decide)
      _ ≤ 4*L^200 := by nlinarith [pow_nonneg hL.le 200]
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  apply (le_div_iff₀ (pow_pos hL 25)).2
  calc
    _ = Real.sqrt (P : ℝ)*L^154 := by ring
    _ ≤ Real.sqrt (P : ℝ)^2 := by nlinarith [Real.sqrt_nonneg (P : ℝ)]
    _ = _ := Real.sq_sqrt (Nat.cast_nonneg P)

/-- Both actual Type-I terms enjoy the saving, including their coefficient sums. -/
theorem norm_weightedArithmeticSum_typeI_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog (trackBCutoff P))‖ +
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
        (vaughanTypeILambda (trackBCutoff P) (trackBCutoff P))‖ ≤
      1960*C^2*P/Real.log (P : ℝ)^25 := by
  let K := trackBCutoff P
  let L := Real.log (P : ℝ)
  let B := 280*C^2*Real.sqrt (P : ℝ)*L^128
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have ha := trackBFrequency_positive_le a P h hlo hhi
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have hK : 0 < K := trackBCutoff_pos P h.1
  have hKK : 0 < K*K := Nat.mul_pos hK hK
  have hKKsq : (K*K)^2 ≤ P := trackBCutoff_sq_sq_le P h
  have hKKP : K*K ≤ P := (Nat.le_self_pow (by decide) (K*K)).trans hKKsq
  have hKK' : K^2 ≤ P := by simpa [pow_two] using hKKP
  have hKleKK : K ≤ K*K := Nat.le_mul_of_pos_right K hK
  have hKP : K ≤ P := hKleKK.trans hKKP
  have hKKb : (K*K : ℕ) ≤ 4*L^128 := by
    calc
      ((K*K : ℕ) : ℝ) = (K : ℝ)^2 := by push_cast; ring
      _ ≤ (2*L^64)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (trackBCutoff_bounds P h.1).2 2
      _ = _ := by ring
  have hKb : (K : ℝ) ≤ 4*L^128 := (by exact_mod_cast hKleKK : (K : ℝ) ≤ (K*K : ℕ)).trans hKKb
  have hB1 : typeIOuterBound a C P K ≤ B := typeIOuterBound_le_polylog a C P K
    h hlo hhi hC hK hKP hKb
  have hB2 : typeIOuterBound a C P (K*K) ≤ B := typeIOuterBound_le_polylog a C P (K*K)
    h hlo hhi hC hKK hKKP hKKb
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB10 := typeIOuterBound_nonneg a C P K hC0.le
  have hB20 := typeIOuterBound_nonneg a C P (K*K) hC0.le
  have hY : (Y : ℝ) ≤ C*P := (show (Y : ℝ) ≤ X by exact_mod_cast hYX).trans hX
  have hlogX1 := (trackBEndpoint_log_bounds C P X h hCP hPX hX).2.1
  have hlogY1 : Real.log (Y+1 : ℕ) ≤ 3*L :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hYX 1)).trans hlogX1
  have hlogKK : Real.log (K*K : ℕ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hKK) (by exact_mod_cast hKKP)
  have hlogY0 := Real.log_natCast_nonneg (Y+1)
  have hlogKK0 := Real.log_natCast_nonneg (K*K)
  have hI1 := norm_weightedArithmeticSum_typeILog_le a C K P Y
    ha.1 ha.2 hC hP h.1 hCP hY hKK'
  have hI2 := norm_weightedArithmeticSum_typeILambda_le a C K K P Y
    ha.1 ha.2 hC hP h.1 hCP hY hKKsq
  calc
    _ ≤ 2*Real.log (Y+1 : ℕ)*typeIOuterBound a C P K +
        Real.log (K*K : ℕ)*typeIOuterBound a C P (K*K) := add_le_add hI1 hI2
    _ ≤ 2*(3*L)*B + L*B := by gcongr
    _ = 1960*C^2*(Real.sqrt (P : ℝ)*L^129) := by dsimp [B]; ring
    _ ≤ 1960*C^2*((P : ℝ)/L^25) := mul_le_mul_of_nonneg_left
      (sqrt_mul_log_pow_le_logSaving P h) (by positivity)
    _ = _ := by ring

/-- The target logarithmic saving for the complete von Mangoldt phase sum.
It is uniform in `a`, `X`, and every partial endpoint `Y ≤ X`. -/
theorem norm_weightedArithmeticSum_vonMangoldt_le_logSaving
    (a C : ℝ) (P Y X : ℕ) (h : trackBScaleCondition P)
    (hlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ a)
    (hhi : a ≤ (P : ℝ)/Real.log (P : ℝ)^120)
    (hC : 1 ≤ C) (hCP : C ≤ (P : ℝ))
    (hPX : P ≤ X) (hX : (X : ℝ) ≤ C*P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
      1000000*C^2*P/Real.log (P : ℝ)^25 := by
  let K := trackBCutoff P
  have hK : 0 < K := trackBCutoff_pos P h.1
  have hKKP : K*K ≤ P :=
    (Nat.le_self_pow (by decide) (K*K)).trans (trackBCutoff_sq_sq_le P h)
  have hKP : K ≤ P := (Nat.le_mul_of_pos_right K hK).trans hKKP
  have hlow := weightedArithmeticSum_lambdaLE_eq_zero K (Ioc P Y) (reciprocalLogWeight a)
    (fun n hn => hKP.trans_lt (mem_Ioc.mp hn).1)
  have hI := norm_weightedArithmeticSum_typeI_le_logSaving a C P Y X h hlo hhi hC hCP hPX hX hYX
  have hII := norm_weightedArithmeticSum_typeII_le_logSaving a C P Y X h hlo hhi hC hCP hPX hX hYX
  rw [vaughan_weighted_sum K K, hlow, zero_add]
  have ht := (norm_add_le
    (weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog K) -
      weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILambda K K))
    (weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII K K))).trans
    (add_le_add ((norm_sub_le _ _).trans hI) hII)
  refine ht.trans ?_
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hCC : C ≤ C^2 := by nlinarith
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hCC hP0, mul_nonneg (sq_nonneg C) hP0]

/-- No scale hypothesis remains: the estimate holds for all sufficiently large `P`.
The threshold depends only on the fixed window ratio `C`, not on the frequency or endpoint. -/
theorem eventually_vonMangoldt_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ a : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ a → a ≤ (P : ℝ)/Real.log (P : ℝ)^120 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
        1000000*C^2*P/Real.log (P : ℝ)^25 := by
  have hCP : ∀ᶠ P : ℕ in atTop, C ≤ (P : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop C)
  filter_upwards [eventually_trackBScaleCondition, hCP] with P hp hcp
  intro a hlo hhi Y X hPX hX hYX
  exact norm_weightedArithmeticSum_vonMangoldt_le_logSaving a C P Y X hp hlo hhi hC hcp hPX hX hYX

end
end Erdos878.TrackB

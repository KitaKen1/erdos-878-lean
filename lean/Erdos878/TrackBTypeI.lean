import Erdos878.TrackBTypeIIBoxes

/-!
# Track B: Type-I sums on the full product band

The Type-I inner interval has bounded ratio `C`. Applying the second-derivative
test on that interval avoids another dyadic decomposition. The outer short
coefficients are then summed using a harmonic-sum estimate.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- The single-phase curvature on a fixed-ratio interval. -/
theorem reciprocalLogPhase_curvature_of_ratio (a n L R C x : ℝ)
    (ha : 0 ≤ a) (_hn : 0 < n) (hL : 1 ≤ L) (hR : 0 < R) (hC : 0 < C)
    (hxlo : R ≤ x) (hxhi : x ≤ C * R)
    (hloglo : L ≤ Real.log (n * x)) (hloghi : Real.log (n * x) ≤ 2 * L) :
    a / (4 * (C * R) ^ 2 * L ^ 2) ≤
        a / x ^ 2 * logCurvature (Real.log (n * x)) ∧
      a / x ^ 2 * logCurvature (Real.log (n * x)) ≤
        (12 * C ^ 2) * (a / (4 * (C * R) ^ 2 * L ^ 2)) := by
  have hx : 0 < x := hR.trans_le hxlo
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hw := logCurvature_bounds L (Real.log (n * x)) hL hloglo hloghi
  have hw0 : 0 ≤ logCurvature (Real.log (n * x)) := (by positivity : 0 ≤ 1 / (4*L^2)).trans hw.1
  have hlo := div_le_div_of_nonneg_left ha (pow_pos hx 2)
    (pow_le_pow_left₀ hx.le hxhi 2)
  have hhi := div_le_div_of_nonneg_left ha (pow_pos hR 2)
    (pow_le_pow_left₀ hR.le hxlo 2)
  constructor
  · convert mul_le_mul hlo hw.1 (by positivity) (by positivity) using 1 <;> first | rfl | ring
  · calc
      _ ≤ (a / R ^ 2) * (3 / L ^ 2) := mul_le_mul hhi hw.2 hw0 (by positivity)
      _ = _ := by field_simp; ring

/-- Second-derivative cancellation on one closed integer interval inside
`[R,C R]`. The ratio, rather than a dyadic decomposition, controls the constant. -/
theorem norm_sum_reciprocalLogPhase_Icc_le_of_ratio
    (a n L R C : ℝ) (A B : ℕ) (ha : 0 < a) (hn : 0 < n)
    (hL : 1 ≤ L) (hR : 0 < R) (hC : 0 < C) (hAB : A ≤ B)
    (hlam : a / (4 * (C * R) ^ 2 * L ^ 2) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), R ≤ x ∧ x ≤ C * R)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n * x) ∧ Real.log (n * x) ≤ 2 * L) :
    ‖∑ k ∈ Icc A B, phaseCharacter (reciprocalLogPhase a n k)‖ ≤
      10 * ((12 * C ^ 2) * (B - A : ℕ) *
          Real.sqrt (a / (4 * (C * R) ^ 2 * L ^ 2)) +
        1 / Real.sqrt (a / (4 * (C * R) ^ 2 * L ^ 2))) := by
  let lam := a / (4 * (C * R) ^ 2 * L ^ 2)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hend : (A : ℝ) + (B - A : ℕ) = B := by rw [Nat.cast_sub hAB]; ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      x ∈ Set.Icc (A : ℝ) (B : ℝ) := by rwa [hend] at hx
  have hdom (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      0 < x ∧ 1 < n * x := by
    have hxp := hR.trans_le (hbox x (hmem hx)).1
    exact ⟨hxp, (Real.log_pos_iff (mul_nonneg hn.le hxp.le)).mp
      (hLp.trans_le (hlog x (hmem hx)).1)⟩
  have hf (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :=
    hasDerivAt_reciprocalLogPhase a n x hn (hdom x hx).1 (hdom x hx).2
  have hh (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :=
    hasDerivAt_reciprocalLogSlope a n x hn (hdom x hx).1 (hdom x hx).2
  have ht := second_derivative_test_small (reciprocalLogPhase a n)
    (reciprocalLogSlope a n) (fun x => a / x ^ 2 * logCurvature (Real.log (n*x)))
    (A : ℝ) (B-A) lam (12*C^2) hlampos hlam (by positivity)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
    (fun x hx => hh x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => by
      have hx' := hmem (Set.Ioo_subset_Icc_self hx)
      exact reciprocalLogPhase_curvature_of_ratio a n L R C x ha.le hn hL hR hC
        (hbox x hx').1 (hbox x hx').2 (hlog x hx').1 (hlog x hx').2)
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  simpa only [Nat.cast_add] using ht

/-- Type-I unweighted inner envelope; its only dependence on the short
factor is through the reciprocal term. -/
def typeIInnerBound (a C : ℝ) (P n : ℕ) : ℝ :=
  60 * C ^ 2 * Real.sqrt a / Real.log (P : ℝ) +
    20 * C * P * Real.log (P : ℝ) / ((n : ℝ) * Real.sqrt a)

theorem typeIInnerBound_nonneg (a C : ℝ) (P n : ℕ) (hC : 0 ≤ C) :
    0 ≤ typeIInnerBound a C P n := by
  have hlog := Real.log_natCast_nonneg P
  unfold typeIInnerBound
  positivity

/-- One scalar condition controls the curvature for every short factor. -/
theorem typeI_lambda_le_one (a C : ℝ) (P n : ℕ)
    (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P) (hn : 0 < n)
    (hnP : n ^ 2 ≤ P) (hlog : 1 ≤ Real.log (P : ℝ)) :
    a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2) ≤ 1 := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnPr : (n : ℝ) ^ 2 ≤ P := by exact_mod_cast hnP
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  have heq : a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2) =
      a * (n : ℝ) ^ 2 / (4 * C ^ 2 * (P : ℝ) ^ 2 * Real.log (P : ℝ) ^ 2) := by
    field_simp
  rw [heq]
  apply (div_le_one (by positivity)).2
  have hC2 : (1 : ℝ) ≤ C ^ 2 := one_le_pow₀ hC
  have hL2 : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 2 := one_le_pow₀ hlog
  calc
    a * (n : ℝ) ^ 2 ≤ (P : ℝ) * n ^ 2 := mul_le_mul_of_nonneg_right haP (sq_nonneg _)
    _ ≤ (P : ℝ) ^ 2 := by nlinarith
    _ ≤ 4 * C ^ 2 * (P : ℝ) ^ 2 * Real.log (P : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg (P : ℝ)),
        mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 4*C^2*(P : ℝ)^2 by positivity)]

/-- Simplify the square root of the Type-I curvature scale. -/
theorem sqrt_typeI_lambda (a C : ℝ) (P n : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (P : ℝ)) :
    Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) =
      Real.sqrt a / (2 * C * ((P : ℝ) / n) * Real.log (P : ℝ)) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  rw [show 4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2 =
      (2 * C * ((P : ℝ) / n) * Real.log (P : ℝ)) ^ 2 by ring,
    Real.sqrt_div ha.le, Real.sqrt_sq (by positivity)]

/-- The interval length disappears from the inner bound after using
`length ≤ CP/n`. -/
theorem typeI_scalar_bound (a C t : ℝ) (P n : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hn : 0 < n)
    (hlog : 1 ≤ Real.log (P : ℝ)) (ht : t ≤ C * ((P : ℝ) / n)) :
    10 * ((12*C^2) * t *
        Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) +
      1 / Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2))) ≤
      typeIInnerBound a C P n := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hLr : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  calc
    _ ≤ 10 * ((12*C^2) * (C * ((P : ℝ) / n)) *
        Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2)) +
      1 / Real.sqrt (a / (4 * (C * ((P : ℝ) / n)) ^ 2 * Real.log (P : ℝ) ^ 2))) := by
      gcongr
    _ = _ := by
      rw [sqrt_typeI_lambda a C P n ha hC hP hn hlog]
      unfold typeIInnerBound
      field_simp
      ring

/-- Every integer subinterval of the original quotient interval obeys the
same unweighted bound. This uniformity is used by Abel summation. -/
theorem norm_sum_reciprocalLogWeight_subinterval_le
    (a C : ℝ) (P Y n A B : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P)
    (hA : P / n + 1 ≤ A) (hB : B ≤ Y / n) (hAB : A ≤ B) :
    ‖∑ k ∈ Icc A B, reciprocalLogWeight a (n*k)‖ ≤ typeIInnerBound a C P n := by
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      (P : ℝ) < (n : ℝ)*x ∧ (n : ℝ)*x ≤ Y :=
    real_product_bounds_of_div_hull P Y n hn x
      ((show ((P/n+1 : ℕ) : ℝ) ≤ A by exact_mod_cast hA).trans hx.1)
      (hx.2.trans (by exact_mod_cast hB))
  have hbox (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      (P : ℝ)/n ≤ x ∧ x ≤ C*((P : ℝ)/n) := by
    have hb := hbound x hx
    constructor
    · exact (div_le_iff₀ hnr).2 (by nlinarith)
    · calc
        x ≤ (C*(P : ℝ))/n := (le_div_iff₀ hnr).2 (by nlinarith [hb.2.trans hY])
        _ = C*((P : ℝ)/n) := by ring
  have hlogs (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) (B : ℝ)) :
      Real.log (P : ℝ) ≤ Real.log ((n : ℝ)*x) ∧
        Real.log ((n : ℝ)*x) ≤ 2*Real.log (P : ℝ) := by
    have hb := hbound x hx
    constructor
    · exact Real.log_le_log hPr hb.1.le
    · calc
        Real.log ((n : ℝ)*x) ≤ Real.log (C*(P : ℝ)) :=
          Real.log_le_log (hPr.trans hb.1) (hb.2.trans hY)
        _ = Real.log C + Real.log (P : ℝ) := Real.log_mul hCr.ne' hPr.ne'
        _ ≤ _ := by linarith [Real.log_le_log hCr hCP]
  have ht := norm_sum_reciprocalLogPhase_Icc_le_of_ratio
    a (n : ℝ) (Real.log (P : ℝ)) ((P : ℝ)/n) C A B ha hnr hPlog
    (div_pos hPr hnr) hCr hAB (typeI_lambda_le_one a C P n haP hC hP hn hnP hPlog)
    hbox hlogs
  have hlen : ((B-A : ℕ) : ℝ) ≤ C*((P : ℝ)/n) := by
    calc
      _ ≤ (B : ℝ) := by exact_mod_cast (Nat.sub_le B A)
      _ ≤ ((Y / n : ℕ) : ℝ) := by exact_mod_cast hB
      _ ≤ (Y : ℝ)/n := Nat.cast_div_le
      _ ≤ (C*(P : ℝ))/n := div_le_div_of_nonneg_right hY hnr.le
      _ = _ := by ring
  have hs := ht.trans (typeI_scalar_bound a C ((B-A : ℕ) : ℝ) P n ha hCr hP hn hPlog hlen)
  simpa only [reciprocalLogWeight, reciprocalLogPhase, Nat.cast_mul] using hs

/-- The original open-closed quotient interval, including empty intervals. -/
theorem norm_sum_reciprocalLogWeight_quotient_le
    (a C : ℝ) (P Y n : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P) :
    ‖∑ k ∈ Ioc (P/n) (Y/n), reciprocalLogWeight a (n*k)‖ ≤
      typeIInnerBound a C P n := by
  by_cases h : P/n < Y/n
  · rw [sum_Ioc_eq_sum_Icc_succ]
    exact norm_sum_reciprocalLogWeight_subinterval_le a C P Y n (P/n+1) (Y/n)
      ha haP hC hP hPlog hCP hY hn hnP le_rfl le_rfl (by omega)
  · rw [Ioc_eq_empty (by omega), sum_empty, norm_zero]
    exact typeIInnerBound_nonneg a C P n (by linarith)

/-- Abel summation supplies the logarithm in the first Vaughan Type-I term. -/
theorem norm_sum_log_mul_reciprocalLogWeight_quotient_le
    (a C : ℝ) (P Y n : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hn : 0 < n) (hnP : n ^ 2 ≤ P) :
    ‖∑ k ∈ Ioc (P/n) (Y/n), (Real.log (k : ℝ) : ℂ) *
      reciprocalLogWeight a (n*k)‖ ≤
      2 * Real.log (Y+1 : ℕ) * typeIInnerBound a C P n := by
  have hE := typeIInnerBound_nonneg a C P n (show 0 ≤ C by linarith)
  have hlogY := Real.log_natCast_nonneg (Y+1)
  by_cases h : P/n < Y/n
  · rw [sum_Ioc_eq_sum_Icc_succ]
    have ht := norm_sum_Icc_log_mul_le (fun k => reciprocalLogWeight a (n*k))
      (P/n+1) (Y/n) (typeIInnerBound a C P n) (Nat.le_add_left 1 (P/n))
      (Nat.succ_le_iff.mpr h) hE ?_
    · refine ht.trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self Y n
    · intro r hr
      by_cases hr0 : r = 0
      · simpa [hr0] using hE
      · let B := P/n+1+r-1
        have hQ := Nat.zero_le (P/n)
        have hAB : P/n+1 ≤ B := by dsimp [B]; omega
        have hBY : B ≤ Y/n := by dsimp [B]; omega
        have hlen : B-(P/n+1)+1 = r := by dsimp [B]; omega
        rw [← hlen, ← sum_Icc_eq_sum_range_shift
          (fun k => reciprocalLogWeight a (n*k)) _ _ hAB]
        exact norm_sum_reciprocalLogWeight_subinterval_le a C P Y n (P/n+1) B
          ha haP hC hP hPlog hCP hY hn hnP le_rfl hBY hAB
  · rw [Ioc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

/-- Summing the short factors costs only a linear term and a harmonic term. -/
def typeIOuterBound (a C : ℝ) (P D : ℕ) : ℝ :=
  60 * C ^ 2 * Real.sqrt a / Real.log (P : ℝ) * D +
    (20 * C * P * Real.log (P : ℝ) / Real.sqrt a) * (1 + Real.log (D : ℝ))

theorem typeIOuterBound_nonneg (a C : ℝ) (P D : ℕ) (hC : 0 ≤ C) :
    0 ≤ typeIOuterBound a C P D := by
  have hPlog := Real.log_natCast_nonneg P
  have hDlog := Real.log_natCast_nonneg D
  unfold typeIOuterBound
  positivity

theorem sum_typeIInnerBound_le (a C : ℝ) (P D : ℕ) (hC : 0 ≤ C) :
    (∑ n ∈ Ioc 0 D, typeIInnerBound a C P n) ≤ typeIOuterBound a C P D := by
  have hPlog := Real.log_natCast_nonneg P
  have hsum : (∑ n ∈ Ioc 0 D, (n : ℝ)⁻¹) ≤ 1+Real.log (D : ℝ) := by
    simpa only [sum_Ioc_eq_sum_Icc_succ, zero_add] using sum_Icc_inv_le_one_add_log D
  simp only [typeIInnerBound, sum_add_distrib,
    sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hsplit (n : ℕ) : 20*C*P*Real.log (P : ℝ)/((n : ℝ)*Real.sqrt a) =
      (20*C*P*Real.log (P : ℝ)/Real.sqrt a) * (n : ℝ)⁻¹ := by ring
  simp_rw [hsplit]
  rw [← mul_sum]
  unfold typeIOuterBound
  nlinarith [mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 20*C*P*Real.log (P : ℝ)/Real.sqrt a by positivity)]

/-- Exact Type-I hyperbola conversion, retaining both original product cutoffs. -/
theorem weightedArithmeticSum_convolution_band_eq_quotient
    (c b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (c*b) =
      ∑ n ∈ Ioc 0 Y, (c n : ℂ) *
        ∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * w (n*k) := by
  rw [weightedArithmeticSum_convolution_band]
  apply sum_congr rfl
  intro n hn
  have hn0 := (mem_Ioc.mp hn).1
  have hfilter : Ioc (P/n) (Y/n) =
      {k ∈ Ioc 0 Y | P < n*k ∧ n*k ≤ Y} := by
    ext k
    simp only [mem_Ioc, mem_filter]
    constructor
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨(Nat.zero_le _).trans_lt hlo, hhi.trans (Nat.div_le_self Y n)⟩, ?_, ?_⟩
      · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hn0).mp hlo
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hn0).mp hhi
    · rintro ⟨_, hlo, hhi⟩
      exact ⟨(Nat.div_lt_iff_lt_mul hn0).mpr (by simpa [Nat.mul_comm] using hlo),
        (Nat.le_div_iff_mul_le hn0).mpr (by simpa [Nat.mul_comm] using hhi)⟩
  rw [hfilter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro k _
  unfold productBandTerm
  split_ifs <;> simp [mul_assoc]

/-- Short support and a coefficient bound discharge the entire outer sum.
There is no assumption that `D ≤ Y`; support beyond the product band is harmless. -/
theorem norm_weightedArithmeticSum_short_convolution_le
    (c b : ArithmeticFunction ℝ) (a C K H : ℝ) (P Y D : ℕ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hsupport : ∀ n, D < n → c n = 0)
    (hcoeff : ∀ n ∈ Ioc 0 D, |c n| ≤ K)
    (hinner : ∀ n ∈ Ioc 0 D,
      ‖∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * reciprocalLogWeight a (n*k)‖ ≤
        H * typeIInnerBound a C P n) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (c*b)‖ ≤
      K * H * typeIOuterBound a C P D := by
  rw [weightedArithmeticSum_convolution_band_eq_quotient]
  calc
    _ ≤ ∑ n ∈ Ioc 0 Y, ‖(c n : ℂ) *
        ∑ k ∈ Ioc (P/n) (Y/n), (b k : ℂ) * reciprocalLogWeight a (n*k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc 0 Y, if n ≤ D then K*H*typeIInnerBound a C P n else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hnD : n ≤ D
      · rw [ite_eq_left hnD, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hn' : n ∈ Ioc 0 D := mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hnD⟩
        calc
          _ ≤ K * (H*typeIInnerBound a C P n) :=
            mul_le_mul (hcoeff n hn') (hinner n hn') (norm_nonneg _) hK
          _ = _ := by ring
      · simp [hnD, hsupport n (by omega)]
    _ = ∑ n ∈ {n ∈ Ioc 0 Y | n ≤ D}, K*H*typeIInnerBound a C P n :=
      (sum_filter _ _).symm
    _ ≤ ∑ n ∈ Ioc 0 D, K*H*typeIInnerBound a C P n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hnY, hnD⟩ := mem_filter.mp hn
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hnY).1, hnD⟩
      · intro n _ _
        exact mul_nonneg (mul_nonneg hK hH) (typeIInnerBound_nonneg a C P n hC)
    _ = K*H*∑ n ∈ Ioc 0 D, typeIInnerBound a C P n := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_typeIInnerBound_le a C P D hC)
      (mul_nonneg hK hH)

/-- Full logarithmic Vaughan Type-I term, with its actual Möbius coefficients. -/
theorem norm_weightedArithmeticSum_typeILog_le
    (a C : ℝ) (U P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hUP : U ^ 2 ≤ P) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILog U)‖ ≤
      2 * Real.log (Y+1 : ℕ) * typeIOuterBound a C P U := by
  have hH : 0 ≤ 2*Real.log (Y+1 : ℕ) := by positivity
  have ht := norm_weightedArithmeticSum_short_convolution_le
    (muLE U) ArithmeticFunction.log a C 1 (2*Real.log (Y+1 : ℕ)) P Y U
    (by linarith) zero_le_one hH
    (fun n hn => by simp [not_le.mpr hn])
    (fun n _ => abs_muLE_le_one U n) ?_
  · simpa only [one_mul, vaughanTypeILog] using ht
  · intro n hn
    obtain ⟨hn0, hnU⟩ := mem_Ioc.mp hn
    simpa only [ArithmeticFunction.log_apply] using
      norm_sum_log_mul_reciprocalLogWeight_quotient_le a C P Y n
        ha haP hC hP hPlog hCP hY hn0 ((Nat.pow_le_pow_left hnU 2).trans hUP)

/-- Full cross Type-I term. The grouped short coefficient costs only `log (UV)`. -/
theorem norm_weightedArithmeticSum_typeILambda_le
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hY : (Y : ℝ) ≤ C * P) (hUVP : (U*V) ^ 2 ≤ P) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeILambda U V)‖ ≤
      Real.log (U*V : ℕ) * typeIOuterBound a C P (U*V) := by
  rw [vaughanTypeILambda_eq]
  have ht := norm_weightedArithmeticSum_short_convolution_le
    (typeICoeff U V) (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    a C (Real.log (U*V : ℕ)) 1 P Y (U*V)
    (by linarith) (Real.log_natCast_nonneg _) zero_le_one
    (typeICoeff_eq_zero_of_mul_lt U V) ?_ ?_
  · simpa only [mul_one] using ht
  · intro n hn
    obtain ⟨hn0, hnUV⟩ := mem_Ioc.mp hn
    exact (abs_typeICoeff_le_log U V n).trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnUV))
  · intro n hn
    obtain ⟨hn0, hnUV⟩ := mem_Ioc.mp hn
    have heq : (∑ k ∈ Ioc (P/n) (Y/n),
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) k : ℂ) *
          reciprocalLogWeight a (n*k)) =
        ∑ k ∈ Ioc (P/n) (Y/n), reciprocalLogWeight a (n*k) := by
      apply sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := ne_of_gt ((Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1)
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hk0]
    rw [heq, one_mul]
    exact norm_sum_reciprocalLogWeight_quotient_le a C P Y n
      ha haP hC hP hPlog hCP hY hn0 ((Nat.pow_le_pow_left hnUV 2).trans hUVP)

end
end Erdos878.TrackB

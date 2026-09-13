import Erdos878.TrackBPhase

/-!
# Track B: explicit two-sided curvature bounds

The constants are uniform in the phase parameter, dyadic variables and endpoints.
On a box with logarithms in `[L,2L]`, the difference phase has the scale
`a * (n₂-n₁) / (N * M² * L³)`. This is the analytic input for the pending
discrete second-derivative estimate; it is not itself an exponential-sum estimate.
-/

namespace Erdos878.TrackB
open Set
noncomputable section

theorem logCurvature_bounds (L z : ℝ) (hL : 1 ≤ L) (hzL : L ≤ z)
    (hzU : z ≤ 2 * L) :
    1 / (4 * L ^ 2) ≤ logCurvature z ∧ logCurvature z ≤ 3 / L ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := hLpos.trans_le hzL
  have hl : 1 / (2 * L) ^ 2 ≤ 1 / z ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 2)
      (pow_le_pow_left₀ hzpos.le hzU 2)
  have hu₂ : 1 / z ^ 2 ≤ 1 / L ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 2)
      (pow_le_pow_left₀ hLpos.le hzL 2)
  have hu₃ : 2 / z ^ 3 ≤ 2 / L ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 2)
      ((pow_le_pow_right₀ hL (show 2 ≤ 3 by norm_num)).trans
        (pow_le_pow_left₀ hLpos.le hzL 3))
  constructor
  · calc
      1 / (4 * L ^ 2) = 1 / (2 * L) ^ 2 := by ring
      _ ≤ 1 / z ^ 2 := hl
      _ ≤ logCurvature z := le_add_of_nonneg_right (by positivity)
  · unfold logCurvature
    calc
      1 / z ^ 2 + 2 / z ^ 3 ≤ 1 / L ^ 2 + 2 / L ^ 2 := add_le_add hu₂ hu₃
      _ = 3 / L ^ 2 := by ring

/-- The Type-I curvature scale is `a/(M² L²)`. -/
theorem deriv2_reciprocalLogPhase_bounds (a n L M x : ℝ)
    (ha : 0 ≤ a) (hn : 0 < n) (hL : 1 ≤ L) (hM : 0 < M)
    (hxlo : M ≤ x) (hxhi : x ≤ 2 * M)
    (hloglo : L ≤ Real.log (n * x)) (hloghi : Real.log (n * x) ≤ 2 * L) :
    a / (16 * M ^ 2 * L ^ 2) ≤ deriv (deriv (reciprocalLogPhase a n)) x ∧
      deriv (deriv (reciprocalLogPhase a n)) x ≤ 3 * a / (M ^ 2 * L ^ 2) := by
  have hx := hM.trans_le hxlo
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hprod : 1 < n * x :=
    (Real.log_pos_iff (mul_nonneg hn.le hx.le)).mp (hLpos.trans_le hloglo)
  rw [deriv2_reciprocalLogPhase a n x hn hx hprod]
  have hw := logCurvature_bounds L (Real.log (n * x)) hL hloglo hloghi
  have hwpos : 0 ≤ logCurvature (Real.log (n * x)) :=
    (by positivity : 0 ≤ 1 / (4 * L ^ 2)).trans hw.1
  have hl : a / (4 * M ^ 2) ≤ a / x ^ 2 := by
    calc
      a / (4 * M ^ 2) = a / (2 * M) ^ 2 := by ring
      _ ≤ a / x ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hx 2)
        (pow_le_pow_left₀ hx.le hxhi 2)
  have hu : a / x ^ 2 ≤ a / M ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hM 2)
    (pow_le_pow_left₀ hM.le hxlo 2)
  constructor
  · convert mul_le_mul hl hw.1 (by positivity) (by positivity) using 1 <;> first | rfl | ring
  · convert mul_le_mul hu hw.2 hwpos (by positivity) using 1 <;> first | rfl | ring

theorem logCurvatureRate_bounds (L z : ℝ) (hL : 1 ≤ L) (hzL : L ≤ z)
    (hzU : z ≤ 2 * L) :
    1 / (4 * L ^ 3) ≤ logCurvatureRate z ∧ logCurvatureRate z ≤ 8 / L ^ 3 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := hLpos.trans_le hzL
  have hlower : 2 / (2 * L) ^ 3 ≤ 2 / z ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 3)
      (pow_le_pow_left₀ hzpos.le hzU 3)
  have hu₃ : 2 / z ^ 3 ≤ 2 / L ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 3)
      (pow_le_pow_left₀ hLpos.le hzL 3)
  have hu₄ : 6 / z ^ 4 ≤ 6 / L ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 3)
      ((pow_le_pow_right₀ hL (show 3 ≤ 4 by norm_num)).trans
        (pow_le_pow_left₀ hLpos.le hzL 4))
  constructor
  · calc
      1 / (4 * L ^ 3) = 2 / (2 * L) ^ 3 := by ring
      _ ≤ 2 / z ^ 3 := hlower
      _ ≤ logCurvatureRate z := le_add_of_nonneg_right (by positivity)
  · unfold logCurvatureRate
    calc
      2 / z ^ 3 + 6 / z ^ 4 ≤ 2 / L ^ 3 + 6 / L ^ 3 := add_le_add hu₃ hu₄
      _ = 8 / L ^ 3 := by ring

/-- Quantitative monotonicity from the mean value theorem, including equal endpoints. -/
theorem logCurvature_sub_bounds (L s t : ℝ) (hL : 1 ≤ L) (hs : L ≤ s)
    (hst : s ≤ t) (ht : t ≤ 2 * L) :
    (t - s) / (4 * L ^ 3) ≤ logCurvature s - logCurvature t ∧
      logCurvature s - logCurvature t ≤ 8 * (t - s) / L ^ 3 := by
  rcases lt_or_eq_of_le hst with hst' | rfl
  · have hspos : 0 < s := (lt_of_lt_of_le zero_lt_one hL).trans_le hs
    have hcont : ContinuousOn logCurvature (Icc s t) := by
      intro z hz
      exact (hasDerivAt_logCurvature z (hspos.trans_le hz.1)).continuousAt.continuousWithinAt
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope logCurvature
      (fun z ↦ -logCurvatureRate z) hst' hcont
      (fun z hz ↦ hasDerivAt_logCurvature z (hspos.trans hz.1))
    have heq : logCurvature s - logCurvature t = logCurvatureRate z * (t - s) := by
      have hh := (eq_div_iff (sub_ne_zero.mpr hst'.ne')).mp he
      nlinarith [hh]
    have hb := logCurvatureRate_bounds L z hL (hs.trans hz.1.le) (hz.2.le.trans ht)
    rw [heq]
    constructor
    · convert mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr hst) using 1 <;> first | rfl | ring
    · convert mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr hst) using 1 <;> first | rfl | ring
  · simp

theorem log_sub_bounds (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (v - u) / v ≤ Real.log v - Real.log u ∧
      Real.log v - Real.log u ≤ (v - u) / u := by
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  have hr := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at hl hr
  have hleft : 1 - (v / u)⁻¹ = (v - u) / v := by field_simp
  have hright : v / u - 1 = (v - u) / u := by field_simp
  exact ⟨hleft ▸ hl, hright ▸ hr⟩

theorem log_sub_bounds_on_dyadic (N u v : ℝ) (hN : 0 < N) (hu : N ≤ u)
    (huv : u ≤ v) (hv : v ≤ 2 * N) :
    (v - u) / (2 * N) ≤ Real.log v - Real.log u ∧
      Real.log v - Real.log u ≤ (v - u) / N := by
  have hupos := hN.trans_le hu
  have hvpos := hupos.trans_le huv
  have hb := log_sub_bounds u v hupos hvpos
  exact ⟨(div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hvpos hv).trans hb.1,
    hb.2.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hN hu)⟩

theorem logCurvature_log_gap_bounds (L N n₁ n₂ x : ℝ) (hL : 1 ≤ L)
    (hN : 0 < N) (hn₁ : N ≤ n₁) (hn₁₂ : n₁ ≤ n₂) (hn₂ : n₂ ≤ 2 * N)
    (hx : 0 < x) (hlow : L ≤ Real.log (n₁ * x)) (hhigh : Real.log (n₂ * x) ≤ 2 * L) :
    (n₂ - n₁) / (8 * N * L ^ 3) ≤
        logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) ∧
      logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) ≤
        8 * (n₂ - n₁) / (N * L ^ 3) := by
  have hn₁pos := hN.trans_le hn₁
  have hn₂pos := hn₁pos.trans_le hn₁₂
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlogs : Real.log (n₁ * x) ≤ Real.log (n₂ * x) :=
    Real.log_le_log (mul_pos hn₁pos hx) (mul_le_mul_of_nonneg_right hn₁₂ hx.le)
  have hdiff : Real.log (n₂ * x) - Real.log (n₁ * x) = Real.log n₂ - Real.log n₁ := by
    rw [Real.log_mul hn₂pos.ne' hx.ne', Real.log_mul hn₁pos.ne' hx.ne']
    ring
  have hw := logCurvature_sub_bounds L _ _ hL hlow hlogs hhigh
  rw [hdiff] at hw
  have hg := log_sub_bounds_on_dyadic N n₁ n₂ hN hn₁ hn₁₂ hn₂
  constructor
  · calc
      (n₂ - n₁) / (8 * N * L ^ 3) = ((n₂ - n₁) / (2 * N)) / (4 * L ^ 3) := by ring
      _ ≤ (Real.log n₂ - Real.log n₁) / (4 * L ^ 3) :=
        div_le_div_of_nonneg_right hg.1 (by positivity)
      _ ≤ _ := hw.1
  · calc
      _ ≤ 8 * (Real.log n₂ - Real.log n₁) / L ^ 3 := hw.2
      _ ≤ 8 * ((n₂ - n₁) / N) / L ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg.2 (by norm_num)) (by positivity)
      _ = _ := by ring

/-- Explicit curvature bounds for the actual difference phase on a dyadic box.
The lower bound is positive whenever `a > 0` and `n₁ < n₂`. -/
theorem deriv2_reciprocalLogCorrelation_bounds (a L M N n₁ n₂ x : ℝ)
    (ha : 0 ≤ a) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hxlo : M ≤ x) (hxhi : x ≤ 2 * M)
    (hnlo : N ≤ n₁) (hnord : n₁ ≤ n₂) (hnhi : n₂ ≤ 2 * N)
    (hloglo : L ≤ Real.log (n₁ * x)) (hloghi : Real.log (n₂ * x) ≤ 2 * L) :
    a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3) ≤
        deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x ∧
      deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x ≤
        8 * a * (n₂ - n₁) / (N * M ^ 2 * L ^ 3) := by
  have hx := hM.trans_le hxlo
  have hn₁ := hN.trans_le hnlo
  have hn₂ := hn₁.trans_le hnord
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hprod₁ : 1 < n₁ * x :=
    (Real.log_pos_iff (mul_nonneg hn₁.le hx.le)).mp (hLpos.trans_le hloglo)
  have hprod₂ : 1 < n₂ * x := hprod₁.trans_le (mul_le_mul_of_nonneg_right hnord hx.le)
  rw [deriv2_reciprocalLogCorrelation a n₁ n₂ x hn₁ hn₂ hx hprod₁ hprod₂]
  have hw := logCurvature_log_gap_bounds L N n₁ n₂ x hL hN hnlo hnord hnhi hx hloglo hloghi
  have hd : 0 ≤ n₂ - n₁ := sub_nonneg.mpr hnord
  have hwpos : 0 ≤ logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)) :=
    (by positivity : 0 ≤ (n₂ - n₁) / (8 * N * L ^ 3)).trans hw.1
  have hl : a / (4 * M ^ 2) ≤ a / x ^ 2 := by
    calc
      a / (4 * M ^ 2) = a / (2 * M) ^ 2 := by ring
      _ ≤ a / x ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hx 2)
        (pow_le_pow_left₀ hx.le hxhi 2)
  have hu : a / x ^ 2 ≤ a / M ^ 2 := div_le_div_of_nonneg_left ha (pow_pos hM 2)
    (pow_le_pow_left₀ hM.le hxlo 2)
  constructor
  · convert mul_le_mul hl hw.1 (by positivity) (by positivity) using 1 <;> first | rfl | ring
  · convert mul_le_mul hu hw.2 hwpos (by positivity) using 1 <;> first | rfl | ring

/-- The difference curvature is nonzero, uniformly comparable with a single positive
scale. This is the form consumed by a discrete second-derivative test. -/
theorem deriv2_reciprocalLogCorrelation_comparable (a L M N n₁ n₂ x : ℝ)
    (ha : 0 < a) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hxlo : M ≤ x) (hxhi : x ≤ 2 * M)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N)
    (hloglo : L ≤ Real.log (n₁ * x)) (hloghi : Real.log (n₂ * x) ≤ 2 * L) :
    let lam := a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3)
    0 < lam ∧ lam ≤ |deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x| ∧
      |deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x| ≤ 256 * lam := by
  dsimp only
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpos : 0 < a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3) :=
    div_pos (mul_pos ha (sub_pos.mpr hnord)) (by positivity)
  have hb := deriv2_reciprocalLogCorrelation_bounds a L M N n₁ n₂ x ha.le hL hM hN
    hxlo hxhi hnlo hnord.le hnhi hloglo hloghi
  rw [abs_of_pos (hpos.trans_le hb.1)]
  refine ⟨hpos, hb.1, hb.2.trans_eq ?_⟩
  ring

/-- Derive the logarithmic hypotheses from the original multiplicative prime band.
For the proposed route take `C = 16` and sufficiently large `P`. -/
theorem correlation_curvature_on_product_band (a C P M N n₁ n₂ x : ℝ)
    (ha : 0 < a) (hP : 1 ≤ Real.log P) (hPpos : 0 < P)
    (hC : 0 < C) (hCP : C ≤ P) (hM : 0 < M) (hN : 0 < N)
    (hxlo : M ≤ x) (hxhi : x ≤ 2 * M)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N)
    (hprodlo : P ≤ n₁ * x) (hprodhi : n₂ * x ≤ C * P) :
    let lam := a * (n₂ - n₁) / (32 * N * M ^ 2 * (Real.log P) ^ 3)
    0 < lam ∧ lam ≤ |deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x| ∧
      |deriv (deriv (reciprocalLogCorrelation a n₁ n₂)) x| ≤ 256 * lam := by
  have hxpos := hM.trans_le hxlo
  have hn₂pos := (hN.trans_le hnlo).trans hnord
  apply deriv2_reciprocalLogCorrelation_comparable a (Real.log P) M N n₁ n₂ x
    ha hP hM hN hxlo hxhi hnlo hnord hnhi
  · exact Real.log_le_log hPpos hprodlo
  · calc
      Real.log (n₂ * x) ≤ Real.log (C * P) :=
        Real.log_le_log (mul_pos hn₂pos hxpos) hprodhi
      _ = Real.log C + Real.log P := Real.log_mul hC.ne' hPpos.ne'
      _ ≤ 2 * Real.log P := by linarith [Real.log_le_log hC hCP]

end
end Erdos878.TrackB

import Erdos878.TrackBTypeIIDistance

/-!
# Track B: coefficient-independent boxes and the long-variable orientation

Both Vaughan coefficients obey the same square-moment envelope. Keeping the
coefficient functions arbitrary allows the longer variable to be placed outside
Cauchy--Schwarz, independently of which Vaughan coefficient it carries.
-/

namespace Erdos878.TrackB
open Finset
open scoped ComplexConjugate
noncomputable section

/-- Cauchy--Schwarz and distance summation for arbitrary real arithmetic
coefficients, retaining the exact product band. -/
theorem norm_sq_productBand_box_le_moments
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Ioc N (2 * N))
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (∑ m ∈ Ioc M B, A m ^ 2) * (∑ n ∈ J, D n ^ 2) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
  let I := Ioc M B
  let K := fun n₁ n₂ => typeIIDistanceBound a M P N (max n₁ n₂ - min n₁ n₂)
  have hcauchy := norm_sq_sum_mul_sum_le_sq_sum_mul_correlation I J A D
    (bandPhase a P Y)
  have hrewrite :
      (∑ m ∈ I, ∑ n ∈ J, productBandTerm A D P Y (reciprocalLogWeight a) m n) =
        ∑ m ∈ I, (A m : ℂ) * ∑ n ∈ J, (D n : ℂ) * bandPhase a P Y m n := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    unfold productBandTerm bandPhase
    split_ifs <;> simp [mul_assoc]
  have hoff : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ K n₁ n₂ := by
    intro n₁ hn₁ n₂ hn₂ hne
    have h₁ := Finset.mem_Ioc.mp (hJ hn₁)
    have h₂ := Finset.mem_Ioc.mp (hJ hn₂)
    exact (norm_sum_bandPhase_correlation_le_symmetric a C M B P Y N n₁ n₂
      ha hC hP hPlog hCP hY hM hB hN h₁.1.le h₁.2 h₂.1.le h₂.2 hne
      (typeII_lambda_le_one_of_scale a M P N n₁ n₂ ha hM hN hPlog
        h₁.1.le h₁.2 h₂.1.le h₂.2 hscale)).trans
      (typeIICorrelationBound_le_typeIIDistanceBound a M B P Y N n₁ n₂ hB)
  have hcorr := sum_abs_mul_norm_bandPhase_correlation_le_ite a P Y I J D K hoff
  rw [sum_abs_mul_ite_eq_diagonal_add_offDiagonal] at hcorr
  have hdist := sum_offDiagonal_distanceKernel_le N J D (typeIIDistanceBound a M P N)
    hJ (fun d hd => typeIIDistanceBound_nonneg a M P N d)
  have hcard : (I.card : ℝ) ≤ M := by
    simp only [I, Nat.card_Ioc]
    exact_mod_cast (show B - M ≤ M by omega)
  have hinner :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, |D n₁| * |D n₂| *
        ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖) ≤
        (∑ n ∈ J, D n ^ 2) *
          ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
    refine hcorr.trans ?_
    calc
      _ ≤ (M : ℝ) * (∑ n ∈ J, D n ^ 2) +
          2 * (∑ n ∈ J, D n ^ 2) * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d :=
        add_le_add (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun n hn => sq_nonneg _))
          hdist
      _ = _ := by ring
  change ‖∑ m ∈ I, ∑ n ∈ J, productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤ _
  rw [hrewrite]
  refine hcauchy.trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner
    (Finset.sum_nonneg fun m hm => sq_nonneg (A m))

/-- Common logarithmic envelope for either of the two Vaughan coefficients. -/
def typeIICommonLog (Y : ℕ) : ℝ := 1 + Real.log (2 * (Y : ℝ) + 1)

theorem one_le_typeIICommonLog (Y : ℕ) : 1 ≤ typeIICommonLog Y := by
  have h : 0 ≤ Real.log (2 * (Y : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  dsimp [typeIICommonLog]
  linarith

theorem sum_typeIICoeff_sq_le_common
    (U M Y : ℕ) (I : Finset ℕ) (hI : I ⊆ Ioc M (2 * M)) (hMY : M ≤ Y) :
    (∑ m ∈ I, typeIICoeff U m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3 := by
  have hlog : 1 + Real.log (2 * (M : ℝ)) ≤ typeIICommonLog Y := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simpa [typeIICommonLog] using one_le_typeIICommonLog Y
    · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hMYr : (M : ℝ) ≤ Y := by exact_mod_cast hMY
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * M)
        (show 2 * (M : ℝ) ≤ 2 * Y + 1 by linarith)
      dsimp [typeIICommonLog]
      linarith
  have hnonneg : 0 ≤ 1 + Real.log (2 * (M : ℝ)) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * M by exact_mod_cast (show 1 ≤ 2*M by omega))
      linarith
  exact (sum_typeIICoeff_sq_le_on_dyadic U M I hI).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hlog 3) (by positivity))

theorem sum_lambdaGT_sq_le_common
    (V M Y : ℕ) (I : Finset ℕ) (hI : I ⊆ Ioc M (2 * M)) (hMY : M ≤ Y) :
    (∑ m ∈ I, lambdaGT V m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3 := by
  have hMYr : (M : ℝ) ≤ Y := by exact_mod_cast hMY
  have hlog0 : 0 ≤ Real.log (2 * (M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog : Real.log (2 * (M : ℝ) + 1) ≤ typeIICommonLog Y := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * M + 1)
      (show 2 * (M : ℝ) + 1 ≤ 2 * Y + 1 by linarith)
    dsimp [typeIICommonLog]
    linarith
  have hH := one_le_typeIICommonLog Y
  have hsquare := pow_le_pow_left₀ hlog0 hlog 2
  have hcube : typeIICommonLog Y ^ 2 ≤ typeIICommonLog Y ^ 3 := by
    nlinarith [sq_nonneg (typeIICommonLog Y),
      mul_nonneg (sq_nonneg (typeIICommonLog Y)) (show 0 ≤ typeIICommonLog Y - 1 by linarith)]
  have hbound : Real.log (2 * (M : ℝ) + 1) ^ 2 ≤ 2 * typeIICommonLog Y ^ 3 := by
    nlinarith
  calc
    _ ≤ (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 := sum_lambdaGT_sq_le_on_dyadic V M I hI
    _ ≤ (M : ℝ) * (2 * typeIICommonLog Y ^ 3) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Square root of the frequency scale, independent of the box dimensions. -/
def typeIIFrequencyRoot (a : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt (a / (32 * Real.log (P : ℝ) ^ 3))

theorem typeIIFrequencyRoot_pos (a : ℝ) (P : ℕ)
    (ha : 0 < a) (hPlog : 1 ≤ Real.log (P : ℝ)) :
    0 < typeIIFrequencyRoot a P := by
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  unfold typeIIFrequencyRoot
  positivity

/-- Isolate the box dimensions in the square root of the curvature scale. -/
theorem sqrt_typeIILambdaScale_eq (a : ℝ) (M P N : ℕ)
    (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    Real.sqrt (typeIILambdaScale a M P N) =
      typeIIFrequencyRoot a P / ((M : ℝ) * Real.sqrt (N : ℝ)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have heq : typeIILambdaScale a M P N =
      (a / (32 * Real.log (P : ℝ) ^ 3)) / ((M : ℝ) ^ 2 * N) := by
    unfold typeIILambdaScale
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMr.le]
  rfl

/-- The distance sum after cancelling its box-dependent square roots. -/
theorem sum_typeIIDistanceBound_le_frequency
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) ≤
      5120 * (N : ℝ) * typeIIFrequencyRoot a P +
        20 * (M : ℝ) * N / typeIIFrequencyRoot a P := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hNr)
  have hg := typeIIFrequencyRoot_pos a P ha hPlog
  have hsquare := Real.sq_sqrt hNr.le
  refine (sum_typeIIDistanceBound_le_explicit_sqrt a M P N ha hM hN hPlog).trans_eq ?_
  rw [sqrt_typeIILambdaScale_eq a M P N ha hM hN hPlog]
  field_simp
  nlinarith

/-- Arbitrary coefficients with common dyadic moments satisfy a box estimate
with no remaining distance sum. -/
theorem norm_sq_productBand_box_le_common_moments
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Ioc N (2 * N))
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
    (hA : (∑ m ∈ Ioc M B, A m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3)
    (hD : (∑ n ∈ J, D n ^ 2) ≤ 2 * (N : ℝ) * typeIICommonLog Y ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ^ 2 ≤
      4 * (M : ℝ) * N * typeIICommonLog Y ^ 6 *
        ((M : ℝ) + 10240 * N * typeIIFrequencyRoot a P +
          40 * (M : ℝ) * N / typeIIFrequencyRoot a P) := by
  have hbase := norm_sq_productBand_box_le_moments A D a C M B P Y N J
    ha hC hP hPlog hCP hY hM hB hN hJ hscale
  have hsum := sum_typeIIDistanceBound_le_frequency a M P N ha hM hN hPlog
  have hH : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
  have hS : 0 ≤ (M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d := by
    exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun d hd => typeIIDistanceBound_nonneg a M P N d))
  calc
    _ ≤ (∑ m ∈ Ioc M B, A m ^ 2) * (∑ n ∈ J, D n ^ 2) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := hbase
    _ ≤ (2 * (M : ℝ) * typeIICommonLog Y ^ 3) *
        (2 * (N : ℝ) * typeIICommonLog Y ^ 3) *
        ((M : ℝ) + 2 * ∑ d ∈ Ioc 0 N, typeIIDistanceBound a M P N d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hA hD (Finset.sum_nonneg fun n hn => sq_nonneg _) (by positivity)) hS
    _ ≤ (2 * (M : ℝ) * typeIICommonLog Y ^ 3) *
        (2 * (N : ℝ) * typeIICommonLog Y ^ 3) *
        ((M : ℝ) + 2 * (5120 * (N : ℝ) * typeIIFrequencyRoot a P +
          20 * (M : ℝ) * N / typeIIFrequencyRoot a P)) := by
      apply mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) _)
      positivity
    _ = _ := by ring

/-- The three normalized errors: diagonal, increasing curvature, and inverse
curvature. `K` is a common lower cutoff for both coefficient supports. -/
def typeIIUniformError (a : ℝ) (P K : ℕ) : ℝ :=
  2 / (K : ℝ) + 20480 * typeIIFrequencyRoot a P / Real.sqrt (P : ℝ) +
    40 / typeIIFrequencyRoot a P

theorem typeIIUniformError_nonneg (a : ℝ) (P K : ℕ) :
    0 ≤ typeIIUniformError a P K := by
  unfold typeIIUniformError typeIIFrequencyRoot
  positivity

/-- A nonempty box with its longer dimension first has small curvature
whenever the frequency is at most the lower product endpoint. -/
theorem typeII_scale_of_long_box (a : ℝ) (M P : ℕ)
    (haP : a ≤ (P : ℝ)) (hgeom : P ≤ 4 * M ^ 2)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    a ≤ 32 * (M : ℝ) ^ 2 * Real.log (P : ℝ) ^ 3 := by
  have hPr : (P : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by exact_mod_cast hgeom
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 3 := one_le_pow₀ hPlog
  have hmul := mul_le_mul_of_nonneg_left hpow (sq_nonneg (M : ℝ))
  nlinarith [sq_nonneg (M : ℝ)]

/-- Bounding the normalized expression by the common cutoff and long-variable
geometry, without any estimate on a divisor function at an individual point. -/
theorem typeII_normalized_error_le
    (a : ℝ) (M N P K : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : 0 < P) (hK : 0 < K) (hKN : K ≤ 2 * N) (hgeom : P ≤ 4 * M ^ 2) :
    1 / (N : ℝ) + 10240 * typeIIFrequencyRoot a P / M +
        40 / typeIIFrequencyRoot a P ≤ typeIIUniformError a P K := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hsP : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hPr
  have hKNr : (K : ℝ) ≤ 2 * N := by exact_mod_cast hKN
  have hgeomr : (P : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by exact_mod_cast hgeom
  have hsPM : Real.sqrt (P : ℝ) ≤ 2 * M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hg : 0 ≤ typeIIFrequencyRoot a P := Real.sqrt_nonneg _
  have hdiag : 1 / (N : ℝ) ≤ 2 / K := by
    apply (div_le_div_iff₀ hNr hKr).2
    nlinarith
  have hcurv : 10240 * typeIIFrequencyRoot a P / M ≤
      20480 * typeIIFrequencyRoot a P / Real.sqrt (P : ℝ) := by
    apply (div_le_div_iff₀ hMr hsP).2
    nlinarith [mul_le_mul_of_nonneg_left hsPM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10240) hg)]
  exact add_le_add (add_le_add hdiag hcurv) le_rfl

/-- A single explicit envelope works for every long-oriented active box. -/
def typeIIUniformBoxBound (a : ℝ) (P Y K : ℕ) : ℝ :=
  Real.sqrt (4 * (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K)

theorem typeIIUniformBoxBound_nonneg (a : ℝ) (P Y K : ℕ) :
    0 ≤ typeIIUniformBoxBound a P Y K := Real.sqrt_nonneg _

theorem norm_productBand_box_le_uniform
    (A D : ArithmeticFunction ℝ) (a C : ℝ) (M B P Y N K : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N) (hK : 0 < K)
    (hJ : J ⊆ Ioc N (2 * N)) (hKN : K ≤ 2 * N)
    (hgeom : P ≤ 4 * M ^ 2) (hprod : M * N ≤ Y)
    (hA : (∑ m ∈ Ioc M B, A m ^ 2) ≤ 2 * (M : ℝ) * typeIICommonLog Y ^ 3)
    (hD : (∑ n ∈ J, D n ^ 2) ≤ 2 * (N : ℝ) * typeIICommonLog Y ^ 3) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ J,
        productBandTerm A D P Y (reciprocalLogWeight a) m n‖ ≤
      typeIIUniformBoxBound a P Y K := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hprodR : (M : ℝ) * N ≤ Y := by exact_mod_cast hprod
  have hg := typeIIFrequencyRoot_pos a P ha hPlog
  have hbase := norm_sq_productBand_box_le_common_moments A D a C M B P Y N J
    ha hC hP hPlog hCP hY hM hB hN hJ
    (typeII_scale_of_long_box a M P haP hgeom hPlog) hA hD
  have heq :
      4 * (M : ℝ) * N * typeIICommonLog Y ^ 6 *
        ((M : ℝ) + 10240 * N * typeIIFrequencyRoot a P +
          40 * (M : ℝ) * N / typeIIFrequencyRoot a P) =
      4 * ((M : ℝ) * N) ^ 2 * typeIICommonLog Y ^ 6 *
        (1 / (N : ℝ) + 10240 * typeIIFrequencyRoot a P / M +
          40 / typeIIFrequencyRoot a P) := by
    field_simp
  rw [heq] at hbase
  have herr := typeII_normalized_error_le a M N P K hM hN hP hK hKN hgeom
  have hsq : ((M : ℝ) * N) ^ 2 ≤ (Y : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hprodR 2
  apply (Real.le_sqrt (norm_nonneg _) (by
    exact mul_nonneg (by positivity) (typeIIUniformError_nonneg a P K))).2
  refine hbase.trans ?_
  calc
    _ ≤ 4 * ((M : ℝ) * N) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (by positivity)) (typeIIUniformError_nonneg a P K)

/-- A nonzero Vaughan summand certifies both support cutoffs as well as the
original product band. -/
theorem productBandTerm_typeII_ne_zero_properties
    (U V P Y m n : ℕ) (w : ℕ → ℂ)
    (ht : productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n ≠ 0) :
    (P < m * n ∧ m * n ≤ Y) ∧ V < m ∧ U < n := by
  have hb : P < m * n ∧ m * n ≤ Y := by
    by_contra h
    simp [productBandTerm, h] at ht
  have hm : V < m := by
    by_contra h
    simp [productBandTerm, lambdaGT_apply, h] at ht
  have hn : U < n := by
    by_contra h
    have hz := typeIICoeff_eq_zero_of_le U n (by omega)
    simp [productBandTerm, hz] at ht
  exact ⟨hb, hm, hn⟩

/-- The same uniform envelope holds for either coefficient orientation.
Empty product boxes and boxes below either Vaughan cutoff contribute zero. -/
theorem norm_typeII_productBand_box_le_uniform
    (a C : ℝ) (U V M B N D P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hN : 0 < N)
    (hB : B ≤ 2 * M) (hD : D ≤ 2 * N) :
    ‖∑ m ∈ Ioc M B, ∑ n ∈ Ioc N D,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n‖ ≤
      typeIIUniformBoxBound a P Y (min U V) := by
  by_cases hactive : ∃ m ∈ Ioc M B, ∃ n ∈ Ioc N D,
      productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n ≠ 0
  · obtain ⟨m, hm, n, hn, ht⟩ := hactive
    obtain ⟨⟨hlo, hhi⟩, hVm, hUn⟩ :=
      productBandTerm_typeII_ne_zero_properties U V P Y m n (reciprocalLogWeight a) ht
    obtain ⟨hMm, hmB⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨hNn, hnD⟩ := Finset.mem_Ioc.mp hn
    have hm2 : m ≤ 2 * M := hmB.trans hB
    have hn2 : n ≤ 2 * N := hnD.trans hD
    have hMN : M * N ≤ Y := (Nat.mul_le_mul hMm.le hNn.le).trans hhi
    have hPmn : P ≤ 4 * M * N := by
      have hh := Nat.mul_le_mul hm2 hn2
      nlinarith
    have hMY : M ≤ Y := (Nat.le_mul_of_pos_right M hN).trans hMN
    have hNY : N ≤ Y := (Nat.le_mul_of_pos_left N hM).trans hMN
    have hK : 0 < min U V := lt_min hU hV
    have hKN : min U V ≤ 2 * N := (min_le_left _ _).trans (hUn.le.trans hn2)
    have hKM : min U V ≤ 2 * M := (min_le_right _ _).trans (hVm.le.trans hm2)
    have hI : Ioc M B ⊆ Ioc M (2 * M) := Finset.Ioc_subset_Ioc le_rfl hB
    have hJ : Ioc N D ⊆ Ioc N (2 * N) := Finset.Ioc_subset_Ioc le_rfl hD
    by_cases hNM : N ≤ M
    · have hgeom : P ≤ 4 * M ^ 2 := by
        nlinarith [Nat.mul_le_mul_left M hNM]
      exact norm_productBand_box_le_uniform (lambdaGT V) (typeIICoeff U)
        a C M B P Y N (min U V) (Ioc N D) ha haP hC hP hPlog hCP hY
        hM hB hN hK hJ hKN hgeom hMN
        (sum_lambdaGT_sq_le_common V M Y (Ioc M B) hI hMY)
        (sum_typeIICoeff_sq_le_common U N Y (Ioc N D) hJ hNY)
    · have hMN' : M ≤ N := by omega
      have hgeom : P ≤ 4 * N ^ 2 := by
        nlinarith [Nat.mul_le_mul_left N hMN']
      rw [sum_productBandTerm_swap]
      exact norm_productBand_box_le_uniform (typeIICoeff U) (lambdaGT V)
        a C N D P Y M (min U V) (Ioc M B) ha haP hC hP hPlog hCP hY
        hN hD hM hK hI hKM hgeom (by simpa [Nat.mul_comm] using hMN)
        (sum_typeIICoeff_sq_le_common U N Y (Ioc N D) hJ hNY)
        (sum_lambdaGT_sq_le_common V M Y (Ioc M B) hI hMY)
  · have hz : (∑ m ∈ Ioc M B, ∑ n ∈ Ioc N D,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      by_contra ht
      exact hactive ⟨m, hm, n, hn, ht⟩
    rw [hz, norm_zero]
    exact typeIIUniformBoxBound_nonneg a P Y (min U V)

/-- The full reciprocal-log Vaughan Type-II tail, with every actual dyadic box
estimated and summed. There is no caller-supplied cancellation or box-bound
hypothesis. -/
theorem norm_weightedArithmeticSum_typeII_le_explicit
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hY2 : 2 ≤ Y) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      9 * Real.log (Y : ℝ) ^ 2 * typeIIUniformBoxBound a P Y (min U V) := by
  apply norm_weightedArithmeticSum_typeII_le_of_box_bound U V P Y hU hY2
    (reciprocalLogWeight a) (typeIIUniformBoxBound a P Y (min U V))
    (typeIIUniformBoxBound_nonneg a P Y (min U V))
  intro i hi j hj
  apply norm_typeII_productBand_box_le_uniform a C U V
    (2 ^ i) (min (2 ^ (i + 1)) Y) (2 ^ j) (min (2 ^ (j + 1)) Y) P Y
    ha haP hC hP hPlog hCP hY hU hV (by positivity) (by positivity)
  · calc
      min (2 ^ (i + 1)) Y ≤ 2 ^ (i + 1) := min_le_left _ _
      _ = 2 * 2 ^ i := by rw [pow_succ]; omega
  · calc
      min (2 ^ (j + 1)) Y ≤ 2 ^ (j + 1) := min_le_left _ _
      _ = 2 * 2 ^ j := by rw [pow_succ]; omega

/-- Expose the endpoint size and the three normalized errors in the uniform
box envelope. -/
theorem typeIIUniformBoxBound_eq (a : ℝ) (P Y K : ℕ) :
    typeIIUniformBoxBound a P Y K =
      2 * (Y : ℝ) * typeIICommonLog Y ^ 3 * Real.sqrt (typeIIUniformError a P K) := by
  have hH : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
  have hfactor : 0 ≤ 2 * (Y : ℝ) * typeIICommonLog Y ^ 3 := by positivity
  unfold typeIIUniformBoxBound
  rw [show 4 * (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 6 * typeIIUniformError a P K =
    (2 * (Y : ℝ) * typeIICommonLog Y ^ 3) ^ 2 * typeIIUniformError a P K by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hfactor]

/-- The full Type-II estimate in normalized form. -/
theorem norm_weightedArithmeticSum_typeII_le_normalized
    (a C : ℝ) (U V P Y : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hU : 0 < U) (hV : 0 < V) (hY2 : 2 ≤ Y) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      18 * (Y : ℝ) * Real.log (Y : ℝ) ^ 2 * typeIICommonLog Y ^ 3 *
        Real.sqrt (typeIIUniformError a P (min U V)) := by
  have h := norm_weightedArithmeticSum_typeII_le_explicit
    a C U V P Y ha haP hC hP hPlog hCP hY hU hV hY2
  rw [typeIIUniformBoxBound_eq] at h
  convert h using 1
  ring

/-- A common upper endpoint gives a bound uniform over all partial product
bands, including empty bands and the endpoints zero and one. -/
theorem norm_weightedArithmeticSum_typeII_le_uniform_endpoint
    (a C : ℝ) (U V P Y X : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ))
    (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hX : (X : ℝ) ≤ C * P) (hYX : Y ≤ X)
    (hU : 0 < U) (hV : 0 < V) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) (vaughanTypeII U V)‖ ≤
      18 * (X : ℝ) * Real.log (X : ℝ) ^ 2 * typeIICommonLog X ^ 3 *
        Real.sqrt (typeIIUniformError a P (min U V)) := by
  have hHX : 0 ≤ typeIICommonLog X := zero_le_one.trans (one_le_typeIICommonLog X)
  by_cases hY2 : 2 ≤ Y
  · have hYXr : (Y : ℝ) ≤ X := by exact_mod_cast hYX
    have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
    have hlogY : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    have hlogs : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) := Real.log_le_log hYr hYXr
    have hHY : 0 ≤ typeIICommonLog Y := zero_le_one.trans (one_le_typeIICommonLog Y)
    have hHs : typeIICommonLog Y ≤ typeIICommonLog X := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * Y + 1)
        (show 2 * (Y : ℝ) + 1 ≤ 2 * X + 1 by linarith)
      dsimp [typeIICommonLog]
      linarith
    refine (norm_weightedArithmeticSum_typeII_le_normalized a C U V P Y
      ha haP hC hP hPlog hCP (hYXr.trans hX) hU hV hY2).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hYXr (by norm_num))
        (pow_le_pow_left₀ hlogY hlogs 2) (sq_nonneg _) (by positivity)
    · exact pow_le_pow_left₀ hHY hHs 3
    · positivity
    · positivity
  · have hempty : Ioc P Y = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    simp only [hempty, weightedArithmeticSum, Finset.sum_empty, norm_zero]
    positivity

end
end Erdos878.TrackB

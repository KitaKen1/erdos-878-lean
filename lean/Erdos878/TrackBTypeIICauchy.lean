import Erdos878.TrackBAbel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Track B: finite Cauchy expansion for a Type-II box

The outer coefficient is treated by Cauchy--Schwarz.  The remaining square is
expanded into the exact cutoff correlations already bounded in
`TrackBBandCorrelation`.
-/

namespace Erdos878.TrackB
open Finset
open scoped ComplexConjugate
noncomputable section

theorem ofReal_sum_norm_sq_eq_sum_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (b : β → ℝ) (φ : α → β → ℂ) :
    ((∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * φ m n‖ ^ 2) : ℂ) =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, φ m n₁ * conj (φ m n₂) := by
  simp_rw [← Complex.mul_conj']
  simp_rw [map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.ofReal_mul]
  ring

/-- After exact expansion, triangle inequality leaves the norms of the cutoff
correlations.  No product condition has been discarded. -/
theorem sum_norm_sq_inner_le_sum_abs_mul_norm_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (b : β → ℝ) (φ : α → β → ℂ) :
    (∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * φ m n‖ ^ 2) ≤
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        ‖∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ := by
  let R : ℝ := ∑ m ∈ I, ‖∑ n ∈ J, (b n : ℂ) * φ m n‖ ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexpand := ofReal_sum_norm_sq_eq_sum_correlation I J b φ
  change R ≤ _
  calc
    R = ‖(R : ℂ)‖ := by simp [abs_of_nonneg hR]
    _ = ‖∑ n₁ ∈ J, ∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ :=
      congrArg norm (by simpa [R] using hexpand)
    _ ≤ ∑ n₁ ∈ J, ‖∑ n₂ ∈ J, ((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ := norm_sum_le _ _
    _ ≤ ∑ n₁ ∈ J, ∑ n₂ ∈ J, ‖((b n₁ * b n₂ : ℝ) : ℂ) *
        ∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ := by
      apply Finset.sum_le_sum
      intro n₁ hn₁
      exact norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      apply Finset.sum_congr rfl
      intro n₂ hn₂
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Cauchy--Schwarz for one Type-II box, followed by the exact correlation
expansion.  The first factor is ready for the Vaughan coefficient square-sum
bounds; the second factor is ready for the reciprocal-log correlation bound. -/
theorem norm_sq_sum_mul_sum_le_sq_sum_mul_correlation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (J : Finset β) (a : α → ℝ) (b : β → ℝ) (φ : α → β → ℂ) :
    ‖∑ m ∈ I, (a m : ℂ) * ∑ n ∈ J, (b n : ℂ) * φ m n‖ ^ 2 ≤
      (∑ m ∈ I, a m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
          ‖∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ := by
  let v : α → ℂ := fun m => ∑ n ∈ J, (b n : ℂ) * φ m n
  have htri :
      ‖∑ m ∈ I, (a m : ℂ) * v m‖ ≤ ∑ m ∈ I, |a m| * ‖v m‖ := by
    calc
      _ ≤ ∑ m ∈ I, ‖(a m : ℂ) * v m‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsquare :
      ‖∑ m ∈ I, (a m : ℂ) * v m‖ ^ 2 ≤ (∑ m ∈ I, |a m| * ‖v m‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq I (fun m => |a m|) (fun m => ‖v m‖)
  have hcorr := sum_norm_sq_inner_le_sum_abs_mul_norm_correlation I J b φ
  change ‖∑ m ∈ I, (a m : ℂ) * v m‖ ^ 2 ≤ _
  calc
    _ ≤ (∑ m ∈ I, |a m| * ‖v m‖) ^ 2 := hsquare
    _ ≤ (∑ m ∈ I, a m ^ 2) * ∑ m ∈ I, ‖v m‖ ^ 2 := by
      simpa only [sq_abs] using hcauchy
    _ ≤ (∑ m ∈ I, a m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
          ‖∑ m ∈ I, φ m n₁ * conj (φ m n₂)‖ :=
      mul_le_mul_of_nonneg_left hcorr (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The abstract phase box is definitionally the `productBandTerm` used by the
Vaughan decomposition when the weight is `reciprocalLogWeight`. -/
theorem productBandTerm_reciprocalLogWeight_eq
    (a : ℝ) (U V P Y m n : ℕ) :
    productBandTerm (lambdaGT V) (typeIICoeff U) P Y (reciprocalLogWeight a) m n =
      (lambdaGT V m : ℂ) * (typeIICoeff U n : ℂ) * bandPhase a P Y m n := by
  unfold productBandTerm bandPhase
  by_cases h : P < m * n ∧ m * n ≤ Y <;> simp [h]

/-- One actual Vaughan Type-II box after Cauchy--Schwarz.  The exact product
cutoff remains inside each correlation, so `norm_sum_bandPhase_correlation_le`
can be applied to every off-diagonal pair. -/
theorem norm_sq_sum_productBandTerm_reciprocalLogWeight_le
    (a : ℝ) (U V P Y : ℕ) (I J : Finset ℕ) :
    ‖∑ m ∈ I, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (∑ m ∈ I, lambdaGT V m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ := by
  have h := norm_sq_sum_mul_sum_le_sq_sum_mul_correlation I J
    (lambdaGT V) (typeIICoeff U) (bandPhase a P Y)
  calc
    ‖∑ m ∈ I, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 =
      ‖∑ m ∈ I, (lambdaGT V m : ℂ) *
        ∑ n ∈ J, (typeIICoeff U n : ℂ) * bandPhase a P Y m n‖ ^ 2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [productBandTerm_reciprocalLogWeight_eq]
      ring
    _ ≤ _ := h

@[simp] theorem norm_bandPhase_le_one (a : ℝ) (P Y m n : ℕ) :
    ‖bandPhase a P Y m n‖ ≤ 1 := by
  unfold bandPhase
  split_ifs <;> simp

/-- The diagonal correlation costs at most the number of outer samples. -/
theorem norm_sum_bandPhase_correlation_le_card
    (a : ℝ) (P Y n₁ n₂ : ℕ) (I : Finset ℕ) :
    ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ I.card := by
  calc
    _ ≤ ∑ m ∈ I, ‖bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, Complex.norm_conj]
      simpa using mul_le_mul (norm_bandPhase_le_one a P Y m n₁)
        (norm_bandPhase_le_one a P Y m n₂) (norm_nonneg _) zero_le_one
    _ = I.card := by simp

/-- Reversing the two inner variables conjugates the correlation and therefore
does not change its norm. -/
theorem norm_sum_bandPhase_correlation_comm
    (a : ℝ) (P Y n₁ n₂ : ℕ) (I : Finset ℕ) :
    ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ =
      ‖∑ m ∈ I, bandPhase a P Y m n₂ * conj (bandPhase a P Y m n₁)‖ := by
  have hconj :
      conj (∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)) =
        ∑ m ∈ I, bandPhase a P Y m n₂ * conj (bandPhase a P Y m n₁) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [map_mul, Complex.conj_conj]
    ring
  calc
    _ = ‖conj (∑ m ∈ I,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂))‖ :=
      (Complex.norm_conj _).symm
    _ = _ := congrArg norm hconj

/-- The explicit off-diagonal bound, made symmetric by ordering the two inner
variables with `min` and `max`. -/
noncomputable def typeIICorrelationBound
    (a : ℝ) (M B P Y N n₁ n₂ : ℕ) : ℝ :=
  let p := min n₁ n₂
  let q := max n₁ n₂
  let lo := max M (max (P / p) (P / q))
  let hi := min B (min (Y / p) (Y / q))
  let lam := a * ((q : ℝ) - p) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  10 * (256 * (hi - (lo + 1) : ℕ) * Real.sqrt lam + 1 / Real.sqrt lam)

theorem typeIICorrelationBound_nonneg
    (a : ℝ) (M B P Y N n₁ n₂ : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hne : n₁ ≠ n₂) :
    0 ≤ typeIICorrelationBound a M B P Y N n₁ n₂ := by
  have hord : min n₁ n₂ < max n₁ n₂ := min_lt_max.mpr hne
  have hordreal : ((min n₁ n₂ : ℕ) : ℝ) < max n₁ n₂ := by exact_mod_cast hord
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  dsimp [typeIICorrelationBound]
  positivity

/-- The proved reciprocal-log correlation estimate in a symmetric form suitable
for an ordered-pair Cauchy expansion. -/
theorem norm_sum_bandPhase_correlation_le_symmetric
    (a C : ℝ) (M B P Y N n₁ n₂ : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hn₁lo : N ≤ n₁) (hn₁hi : n₁ ≤ 2 * N)
    (hn₂lo : N ≤ n₂) (hn₂hi : n₂ ≤ 2 * N) (hne : n₁ ≠ n₂)
    (hlam : a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤
      typeIICorrelationBound a M B P Y N n₁ n₂ := by
  have hord : min n₁ n₂ < max n₁ n₂ := min_lt_max.mpr hne
  have hlo : N ≤ min n₁ n₂ := le_min hn₁lo hn₂lo
  have hhi : max n₁ n₂ ≤ 2 * N := max_le hn₁hi hn₂hi
  have ht := norm_sum_bandPhase_correlation_le a C M B P Y N
    (min n₁ n₂) (max n₁ n₂) ha hC hP hPlog hCP hY hM hB hN hlo hord hhi hlam
  by_cases h : n₁ ≤ n₂
  · simpa [typeIICorrelationBound, min_eq_left h, max_eq_right h] using ht
  · have hrev : n₂ ≤ n₁ := le_of_not_ge h
    rw [norm_sum_bandPhase_correlation_comm a P Y n₁ n₂]
    simpa [typeIICorrelationBound, min_eq_right hrev, max_eq_left hrev] using ht

/-- Separate the inexpensive diagonal from a supplied off-diagonal correlation
bound.  Keeping this as a full ordered-pair sum postpones the harmless symmetry
factor until the distance summation stage. -/
theorem sum_abs_mul_norm_bandPhase_correlation_le_ite
    (a : ℝ) (P Y : ℕ) (I J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (hoff : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ K n₁ n₂) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖) ≤
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        (if n₁ = n₂ then (I.card : ℝ) else K n₁ n₂) := by
  apply Finset.sum_le_sum
  intro n₁ hn₁
  apply Finset.sum_le_sum
  intro n₂ hn₂
  split_ifs with h
  · subst n₂
    exact mul_le_mul_of_nonneg_left
      (norm_sum_bandPhase_correlation_le_card a P Y n₁ n₁ I)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  ·
    exact mul_le_mul_of_nonneg_left (hoff n₁ hn₁ n₂ hn₂ h)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Actual Type-II box with the diagonal isolated and every off-diagonal term
represented by a caller-supplied correlation bound. -/
theorem norm_sq_sum_productBandTerm_le_diagonal_offDiagonal
    (a : ℝ) (U V P Y : ℕ) (I J : Finset ℕ) (K : ℕ → ℕ → ℝ)
    (hoff : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      ‖∑ m ∈ I, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤ K n₁ n₂) :
    ‖∑ m ∈ I, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (∑ m ∈ I, lambdaGT V m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          (if n₁ = n₂ then (I.card : ℝ) else K n₁ n₂) := by
  refine (norm_sq_sum_productBandTerm_reciprocalLogWeight_le a U V P Y I J).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_abs_mul_norm_bandPhase_correlation_le_ite a P Y I J (typeIICoeff U) K hoff
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- One complete dyadic Type-II box with the proved reciprocal-log correlation
bound substituted for every off-diagonal pair.  What remains is the finite
weighted distance sum displayed on the right. -/
theorem norm_sq_sum_productBandTerm_le_explicit_correlationBound
    (a C : ℝ) (U V M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hlam : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M B, lambdaGT V m ^ 2) *
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          (if n₁ = n₂ then ((Finset.Ioc M B).card : ℝ)
            else typeIICorrelationBound a M B P Y N n₁ n₂) := by
  apply norm_sq_sum_productBandTerm_le_diagonal_offDiagonal
  intro n₁ hn₁ n₂ hn₂ hne
  have h₁ := Finset.mem_Ioc.mp (hJ hn₁)
  have h₂ := Finset.mem_Ioc.mp (hJ hn₂)
  exact norm_sum_bandPhase_correlation_le_symmetric a C M B P Y N n₁ n₂
    ha hC hP hPlog hCP hY hM hB hN h₁.1.le h₁.2 h₂.1.le h₂.2 hne
    (hlam n₁ hn₁ n₂ hn₂ hne)

/-- The same explicit box estimate after inserting the proved second moment of
the outer von Mangoldt coefficient. -/
theorem norm_sq_sum_productBandTerm_le_explicit_correlationBound_with_moment
    (a C : ℝ) (U V M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hlam : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 *
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          (if n₁ = n₂ then ((Finset.Ioc M B).card : ℝ)
            else typeIICorrelationBound a M B P Y N n₁ n₂)) := by
  let Q : ℝ := ∑ n₁ ∈ J, ∑ n₂ ∈ J,
    |typeIICoeff U n₁| * |typeIICoeff U n₂| *
      (if n₁ = n₂ then ((Finset.Ioc M B).card : ℝ)
        else typeIICorrelationBound a M B P Y N n₁ n₂)
  have hbase := norm_sq_sum_productBandTerm_le_explicit_correlationBound
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ hlam
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    apply Finset.sum_nonneg
    intro n₁ hn₁
    apply Finset.sum_nonneg
    intro n₂ hn₂
    apply mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    split_ifs with h
    · positivity
    · exact typeIICorrelationBound_nonneg a M B P Y N n₁ n₂ ha hM hN hPlog h
  have houter :
      (∑ m ∈ Finset.Ioc M B, lambdaGT V m ^ 2) ≤
        (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 := by
    apply sum_lambdaGT_sq_le_on_dyadic V M
    intro m hm
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1, (Finset.mem_Ioc.mp hm).2.trans hB⟩
  change _ ≤ (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 * Q
  exact hbase.trans (mul_le_mul_of_nonneg_right houter hQ)

/-- Exact separation of the diagonal coefficient moment from the off-diagonal
ordered-pair sum. -/
theorem sum_abs_mul_ite_eq_diagonal_add_offDiagonal
    (J : Finset ℕ) (b : ℕ → ℝ) (D : ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, |b n₁| * |b n₂| *
        (if n₁ = n₂ then D else K n₁ n₂)) =
      D * (∑ n ∈ J, b n ^ 2) +
        ∑ n₁ ∈ J, ∑ n₂ ∈ J,
          if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
  calc
    _ = ∑ n₁ ∈ J, (|b n₁| ^ 2 * D +
        ∑ n₂ ∈ J, if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂) := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      calc
        _ = (∑ n₂ ∈ J, if n₁ = n₂ then |b n₁| * |b n₂| * D else 0) +
            ∑ n₂ ∈ J, if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n₂ hn₂
          split_ifs <;> ring
        _ = _ := by simp [hn₁, pow_two]
    _ = (∑ n ∈ J, |b n| ^ 2 * D) +
        ∑ n₁ ∈ J, ∑ n₂ ∈ J,
          if n₁ = n₂ then 0 else |b n₁| * |b n₂| * K n₁ n₂ := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.sum_mul]
      simp_rw [sq_abs]
      ring

/-- Final one-box interface: both coefficient moments are visibly diagonal,
and the only unsummed analytic term is the off-diagonal distance kernel. -/
theorem norm_sq_sum_productBandTerm_le_moment_mul_diagonal_add_offDiagonal
    (a C : ℝ) (U V M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hlam : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 *
        (((Finset.Ioc M B).card : ℝ) * (∑ n ∈ J, typeIICoeff U n ^ 2) +
          ∑ n₁ ∈ J, ∑ n₂ ∈ J,
            if n₁ = n₂ then 0 else
              |typeIICoeff U n₁| * |typeIICoeff U n₂| *
                typeIICorrelationBound a M B P Y N n₁ n₂) := by
  have h := norm_sq_sum_productBandTerm_le_explicit_correlationBound_with_moment
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ hlam
  calc
    _ ≤ (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 *
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          (if n₁ = n₂ then ((Finset.Ioc M B).card : ℝ)
            else typeIICorrelationBound a M B P Y N n₁ n₂)) := h
    _ = _ := by
      rw [sum_abs_mul_ite_eq_diagonal_add_offDiagonal]

/-- The diagonal part of one box is completely controlled by the inner Vaughan
coefficient second moment and the length of the outer interval. -/
theorem typeII_diagonal_le
    (U M B N : ℕ) (J : Finset ℕ) (hB : B ≤ 2 * M)
    (hJ : J ⊆ Finset.Ioc N (2 * N)) :
    ((Finset.Ioc M B).card : ℝ) * (∑ n ∈ J, typeIICoeff U n ^ 2) ≤
      2 * (M : ℝ) * N * (1 + Real.log (2 * (N : ℝ))) ^ 3 := by
  have hcard : ((Finset.Ioc M B).card : ℝ) ≤ M := by
    simp only [Nat.card_Ioc]
    exact_mod_cast (show B - M ≤ M by omega)
  have hcoeff := sum_typeIICoeff_sq_le_on_dyadic U N J hJ
  calc
    _ ≤ (M : ℝ) * (2 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3) :=
      mul_le_mul hcard hcoeff (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- One-box bound with the diagonal fully evaluated.  The only remaining inner
quantity is now the explicit off-diagonal correlation-distance sum. -/
theorem norm_sq_sum_productBandTerm_le_explicit_diagonal_add_offDiagonal
    (a C : ℝ) (U V M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hlam : ∀ n₁ ∈ J, ∀ n₂ ∈ J, n₁ ≠ n₂ →
      a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    ‖∑ m ∈ Finset.Ioc M B, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 *
        (2 * (M : ℝ) * N * (1 + Real.log (2 * (N : ℝ))) ^ 3 +
          ∑ n₁ ∈ J, ∑ n₂ ∈ J,
            if n₁ = n₂ then 0 else
              |typeIICoeff U n₁| * |typeIICoeff U n₂| *
                typeIICorrelationBound a M B P Y N n₁ n₂) := by
  have h := norm_sq_sum_productBandTerm_le_moment_mul_diagonal_add_offDiagonal
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ hlam
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact add_le_add (typeII_diagonal_le U M B N J hB hJ) le_rfl
  · positivity

end
end Erdos878.TrackB

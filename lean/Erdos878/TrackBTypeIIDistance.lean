import Erdos878.TrackBTypeIICauchy

/-!
# Track B: reindexing the Type-II off-diagonal by distance

This file isolates the finite combinatorics behind the remaining Type-II
off-diagonal sum.  An upper-triangular pair `(n₁,n₂)` is reindexed by its
positive distance `d = n₂ - n₁` and its initial point `n₁`.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- Ordered pairs from `J` lying strictly above the diagonal. -/
def typeIIUpperPairs (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  (J ×ˢ J).filter fun p => p.1 < p.2

/-- A positive distance at most `N`, together with an initial point of `J`
whose translate by that distance is still in `J`. -/
def typeIIShiftPairs (N : ℕ) (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 N ×ˢ J).filter fun p => p.2 + p.1 ∈ J

/-- The upper-triangular pair sum is exactly the positive-distance sum.
The hypothesis `J ⊆ (N,2N]` is used only to show that every distance is at
most `N`. -/
theorem sum_typeIIUpperPairs_eq_sum_typeIIShiftPairs
    {R : Type*} [AddCommMonoid R] (N : ℕ) (J : Finset ℕ)
    (F : ℕ → ℕ → R) (hJ : J ⊆ Finset.Ioc N (2 * N)) :
    ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 =
      ∑ p ∈ typeIIShiftPairs N J, F p.2 (p.2 + p.1) := by
  refine Finset.sum_nbij'
    (i := fun p : ℕ × ℕ => (p.2 - p.1, p.1))
    (j := fun p : ℕ × ℕ => (p.2, p.2 + p.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, typeIIShiftPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hn₁, hn₂⟩, hlt⟩ := hp
    have hn₁Ioc := Finset.mem_Ioc.mp (hJ hn₁)
    have hn₂Ioc := Finset.mem_Ioc.mp (hJ hn₂)
    refine ⟨⟨⟨Nat.sub_pos_iff_lt.mpr hlt, ?_⟩, hn₁⟩, ?_⟩
    · omega
    · simpa [Nat.add_sub_of_le hlt.le] using hn₂
  · rintro ⟨d, n⟩ hp
    simp only [typeIIUpperPairs, typeIIShiftPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hd, hn⟩, hnd⟩ := hp
    exact ⟨⟨hn, hnd⟩, by omega⟩
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hlt⟩ := hp
    simp [Nat.add_sub_of_le hlt.le]
  · rintro ⟨d, n⟩ hp
    simp
  · rintro ⟨n₁, n₂⟩ hp
    simp only [typeIIUpperPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hlt⟩ := hp
    simp [Nat.add_sub_of_le hlt.le]

/-- Writing the upper-triangular pair finset as nested sums. -/
theorem sum_typeIIUpperPairs_eq_sum_lt
    {R : Type*} [AddCommMonoid R] (J : Finset ℕ) (F : ℕ → ℕ → R) :
    ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0 := by
  rw [typeIIUpperPairs, Finset.sum_filter, Finset.sum_product]

/-- A symmetric ordered off-diagonal sum is twice its upper-triangular half. -/
theorem sum_offDiagonal_eq_two_mul_sum_typeIIUpperPairs
    {R : Type*} [CommSemiring R] (J : Finset ℕ) (F : ℕ → ℕ → R)
    (hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
      2 * ∑ p ∈ typeIIUpperPairs J, F p.1 p.2 := by
  have hsplit :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0) +
        (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₂ < n₁ then F n₁ n₂ else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n₁ hn₁
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n₂ hn₂
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
    · have hnot : ¬n₂ < n₁ := Nat.not_lt.mpr hlt.le
      simp [hlt, hlt.ne, hnot]
    · subst n₂
      simp
    · have hnot : ¬n₁ < n₂ := Nat.not_lt.mpr hgt.le
      simp [hgt, hgt.ne', hnot]
  have hlower :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₂ < n₁ then F n₁ n₂ else 0) =
        ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ < n₂ then F n₁ n₂ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n₁ hn₁
    apply Finset.sum_congr rfl
    intro n₂ hn₂
    by_cases hlt : n₁ < n₂
    · simp [hlt, hsymm n₂ hn₂ n₁ hn₁]
    · simp [hlt]
  rw [hsplit, hlower, ← sum_typeIIUpperPairs_eq_sum_lt J F]
  ring

/-- Writing the shift-pair finset as a distance sum followed by an initial-point
sum. -/
theorem sum_typeIIShiftPairs_eq_sum_shift
    {R : Type*} [AddCommMonoid R] (N : ℕ) (J : Finset ℕ)
    (G : ℕ → ℕ → R) :
    ∑ p ∈ typeIIShiftPairs N J, G p.1 p.2 =
      ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then G d n else 0 := by
  rw [typeIIShiftPairs, Finset.sum_filter, Finset.sum_product]

/-- Exact distance reindexing for a symmetric ordered off-diagonal sum. -/
theorem sum_offDiagonal_eq_two_mul_sum_shifts
    {R : Type*} [CommSemiring R] (N : ℕ) (J : Finset ℕ)
    (F : ℕ → ℕ → R) (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂) =
      2 * ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then F n (n + d) else 0 := by
  rw [sum_offDiagonal_eq_two_mul_sum_typeIIUpperPairs J F hsymm]
  rw [sum_typeIIUpperPairs_eq_sum_typeIIShiftPairs N J F hJ]
  rw [sum_typeIIShiftPairs_eq_sum_shift N J
    (fun d n => F n (n + d))]

/-- Translating the second square along a fixed distance does not increase the
total square mass, because translation is injective and all translated points
remain in `J`. -/
theorem sum_sq_shift_le_sum_sq (J : Finset ℕ) (b : ℕ → ℝ) (d : ℕ) :
    (∑ n ∈ J.filter (fun n => n + d ∈ J), b (n + d) ^ 2) ≤
      ∑ n ∈ J, b n ^ 2 := by
  let S := J.filter fun n => n + d ∈ J
  have hinj : Set.InjOn (fun n : ℕ => n + d) (↑S : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ h
    exact Nat.add_right_cancel h
  have himage : Finset.image (fun n : ℕ => n + d) S ⊆ J := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hn).2
  change (∑ n ∈ S, b (n + d) ^ 2) ≤ _
  calc
    _ = ∑ k ∈ Finset.image (fun n : ℕ => n + d) S, b k ^ 2 := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ n ∈ J, b n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun n hnJ hnimage => sq_nonneg (b n))

/-- The coefficient autocorrelation at one positive shift is bounded by the
coefficient second moment.  This is the finite AM--GM step used after the
distance reindexing. -/
theorem sum_abs_mul_shift_le_sum_sq (J : Finset ℕ) (b : ℕ → ℝ) (d : ℕ) :
    (∑ n ∈ J.filter (fun n => n + d ∈ J), |b n| * |b (n + d)|) ≤
      ∑ n ∈ J, b n ^ 2 := by
  let S := J.filter fun n => n + d ∈ J
  have hfirst : (∑ n ∈ S, b n ^ 2) ≤ ∑ n ∈ J, b n ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hnJ hnS
    exact sq_nonneg (b n)
  have hsecond : (∑ n ∈ S, b (n + d) ^ 2) ≤ ∑ n ∈ J, b n ^ 2 := by
    simpa [S] using sum_sq_shift_le_sum_sq J b d
  change (∑ n ∈ S, |b n| * |b (n + d)|) ≤ _
  calc
    _ ≤ ∑ n ∈ S, (b n ^ 2 + b (n + d) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have h := two_mul_le_add_sq |b n| |b (n + d)|
      rw [sq_abs, sq_abs] at h
      linarith
    _ = ((∑ n ∈ S, b n ^ 2) + ∑ n ∈ S, b (n + d) ^ 2) / 2 := by
      calc
        _ = (∑ n ∈ S, b n ^ 2 / 2) +
            ∑ n ∈ S, b (n + d) ^ 2 / 2 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by
          rw [← Finset.sum_div, ← Finset.sum_div]
          ring
    _ ≤ ((∑ n ∈ J, b n ^ 2) + ∑ n ∈ J, b n ^ 2) / 2 := by
      gcongr
    _ = ∑ n ∈ J, b n ^ 2 := by ring

/-- Summing the fixed-shift autocorrelation estimate against an arbitrary
nonnegative distance kernel. -/
theorem sum_shift_kernel_le_moment_mul_sum
    (N : ℕ) (J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℝ)
    (hK : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ K d) :
    (∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then |b n| * |b (n + d)| * K d else 0) ≤
      (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [← Finset.sum_filter]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_abs_mul_shift_le_sum_sq J b d) (hK d hd)

/-- Generic finite large-sieve-style reduction: a symmetric kernel depending
only on the distance costs at most twice the coefficient second moment times
the sum of that kernel over positive distances. -/
theorem sum_offDiagonal_distanceKernel_le
    (N : ℕ) (J : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℝ)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hK : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ K d) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
        |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)) ≤
      2 * (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by
  let F : ℕ → ℕ → ℝ := fun n₁ n₂ =>
    |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)
  have hsymm : ∀ n₁ ∈ J, ∀ n₂ ∈ J, F n₁ n₂ = F n₂ n₁ := by
    intro n₁ hn₁ n₂ hn₂
    dsimp [F]
    rw [max_comm, min_comm]
    ring
  rw [show (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
      |b n₁| * |b n₂| * K (max n₁ n₂ - min n₁ n₂)) =
      ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else F n₁ n₂ by rfl]
  rw [sum_offDiagonal_eq_two_mul_sum_shifts N J F hJ hsymm]
  have hshift := sum_shift_kernel_le_moment_mul_sum N J b K hK
  calc
    2 * (∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ J,
        if n + d ∈ J then F n (n + d) else 0) ≤
        2 * ((∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [F] using hshift
      · norm_num
    _ = 2 * (∑ n ∈ J, b n ^ 2) * ∑ d ∈ Finset.Ioc 0 N, K d := by ring

/-- A distance-only envelope for the reciprocal-log Type-II correlation.
The cutoff interval in `typeIICorrelationBound` has length at most `B ≤ 2M`,
which changes `256` into the displayed `512 M`. -/
noncomputable def typeIIDistanceBound
    (a : ℝ) (M P N d : ℕ) : ℝ :=
  let lam := a * (d : ℝ) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  10 * (512 * (M : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam)

theorem typeIIDistanceBound_nonneg
    (a : ℝ) (M P N d : ℕ) :
    0 ≤ typeIIDistanceBound a M P N d := by
  dsimp [typeIIDistanceBound]
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg M)) (Real.sqrt_nonneg _))
      (div_nonneg zero_le_one (Real.sqrt_nonneg _)))

/-- The endpoint-sensitive correlation bound is at most its distance-only
envelope on an outer dyadic interval. -/
theorem typeIICorrelationBound_le_typeIIDistanceBound
    (a : ℝ) (M B P Y N n₁ n₂ : ℕ) (hB : B ≤ 2 * M) :
    typeIICorrelationBound a M B P Y N n₁ n₂ ≤
      typeIIDistanceBound a M P N (max n₁ n₂ - min n₁ n₂) := by
  let p := min n₁ n₂
  let q := max n₁ n₂
  let lo := max M (max (P / p) (P / q))
  let hi := min B (min (Y / p) (Y / q))
  let lam := a * ((q : ℝ) - p) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  have hpq : p ≤ q := by simp [p, q]
  have hlen : hi - (lo + 1) ≤ 2 * M := by
    exact (Nat.sub_le hi (lo + 1)).trans ((min_le_left _ _).trans hB)
  have hlenReal : ((hi - (lo + 1) : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hlen
  have hlam :
      a * ((max n₁ n₂ - min n₁ n₂ : ℕ) : ℝ) /
          (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) = lam := by
    rw [Nat.cast_sub (show min n₁ n₂ ≤ max n₁ n₂ from min_le_max)]
  dsimp [typeIICorrelationBound, typeIIDistanceBound]
  rw [hlam]
  have hsqrt : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  nlinarith

/-- The actual endpoint-sensitive off-diagonal is reduced to the sum of the
distance-only envelope.  At this point the arithmetic coefficients occur only
through their second moment. -/
theorem sum_offDiagonal_typeIICorrelationBound_le_distanceMoment
    (a : ℝ) (U M B P Y N : ℕ) (J : Finset ℕ)
    (hB : B ≤ 2 * M) (hJ : J ⊆ Finset.Ioc N (2 * N)) :
    (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
        |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          typeIICorrelationBound a M B P Y N n₁ n₂) ≤
      2 * (∑ n ∈ J, typeIICoeff U n ^ 2) *
        ∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d := by
  calc
    _ ≤ ∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
        |typeIICoeff U n₁| * |typeIICoeff U n₂| *
          typeIIDistanceBound a M P N (max n₁ n₂ - min n₁ n₂) := by
      apply Finset.sum_le_sum
      intro n₁ hn₁
      apply Finset.sum_le_sum
      intro n₂ hn₂
      by_cases heq : n₁ = n₂
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left
          (typeIICorrelationBound_le_typeIIDistanceBound
            a M B P Y N n₁ n₂ hB)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := sum_offDiagonal_distanceKernel_le N J (typeIICoeff U)
      (typeIIDistanceBound a M P N) hJ
      (fun d hd => typeIIDistanceBound_nonneg a M P N d)

/-- The finite square-root sum is bounded by its largest summand times the
number of positive distances. -/
theorem sum_sqrt_Ioc_le_mul_sqrt (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, Real.sqrt (d : ℝ)) ≤
      (N : ℝ) * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.Ioc 0 N, Real.sqrt (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
    _ = (N : ℝ) * Real.sqrt (N : ℝ) := by
      simp [Nat.card_Ioc]

/-- A coarse but assumption-free bound for the reciprocal-square-root sum.
The sharper integral estimate can replace this lemma without changing the
distance-reindexing interface. -/
theorem sum_inv_sqrt_Ioc_le (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, 1 / Real.sqrt (d : ℝ)) ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.Ioc 0 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < d := by
        exact_mod_cast (Finset.mem_Ioc.mp hd).1
      have hsqrtpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
      have hsqrtOne : 1 ≤ Real.sqrt (d : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Ioc.mp hd).1)
      exact (div_le_one hsqrtpos).2 hsqrtOne
    _ = (N : ℝ) := by simp [Nat.card_Ioc]

/-- Telescoping consecutive differences on `(0,N]`. -/
theorem sum_Ioc_sub_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, (f d - f (d - 1))) = f N - f 0 := by
  calc
    _ = ∑ k ∈ Finset.range N, (f (k + 1) - f k) := by
      refine Finset.sum_nbij'
        (i := fun d : ℕ => d - 1) (j := fun k : ℕ => k + 1) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_Ioc, Finset.mem_range] at hd ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range, Finset.mem_Ioc] at hk ⊢
        omega
      · intro d hd
        simp only [Finset.mem_Ioc] at hd
        omega
      · intro k hk
        simp
      · intro d hd
        simp only [Finset.mem_Ioc] at hd
        rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    _ = _ := Finset.sum_range_sub f N

/-- The reciprocal square root is controlled by a telescoping square-root
difference. -/
theorem one_div_sqrt_le_two_mul_sqrt_sub (d : ℕ) (hd : 0 < d) :
    1 / Real.sqrt (d : ℝ) ≤
      2 * (Real.sqrt (d : ℝ) - Real.sqrt ((d - 1 : ℕ) : ℝ)) := by
  let x := Real.sqrt (d : ℝ)
  let y := Real.sqrt ((d - 1 : ℕ) : ℝ)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := hd
  have hxpos : 0 < x := Real.sqrt_pos.2 hdreal
  have hx0 : 0 ≤ x := hxpos.le
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyx : y ≤ x := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le d 1))
  have hx2 : x ^ 2 = (d : ℝ) := Real.sq_sqrt hdreal.le
  have hy2 : y ^ 2 = ((d - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd1]
    norm_num
  have hprod : (x - y) * (x + y) = 1 := by
    nlinarith
  have hsum : x + y ≤ 2 * x := by linarith
  have hmul : (x - y) * (x + y) ≤ (x - y) * (2 * x) :=
    mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hyx)
  change 1 / x ≤ 2 * (x - y)
  rw [div_le_iff₀ hxpos]
  nlinarith

/-- The standard sharp-order integral bound for the reciprocal-square-root
sum. -/
theorem sum_inv_sqrt_Ioc_le_two_mul_sqrt (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, 1 / Real.sqrt (d : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 N,
        2 * (Real.sqrt (d : ℝ) - Real.sqrt ((d - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact one_div_sqrt_le_two_mul_sqrt_sub d (Finset.mem_Ioc.mp hd).1
    _ = 2 * (Real.sqrt (N : ℝ) - Real.sqrt (0 : ℝ)) := by
      rw [← Finset.mul_sum, sum_Ioc_sub_eq (fun d => Real.sqrt (d : ℝ)) N]
      simp
    _ = 2 * Real.sqrt (N : ℝ) := by simp

/-- The distance-independent part of the Type-II curvature parameter. -/
noncomputable def typeIILambdaScale (a : ℝ) (M P N : ℕ) : ℝ :=
  a / (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)

theorem typeIILambdaScale_pos
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    0 < typeIILambdaScale a M P N := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  unfold typeIILambdaScale
  positivity

/-- On a positive distance, the envelope separates exactly into a square-root
kernel and a reciprocal-square-root kernel. -/
theorem typeIIDistanceBound_eq_scale
    (a : ℝ) (M P N d : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hd : 0 < d) :
    typeIIDistanceBound a M P N d =
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          Real.sqrt (d : ℝ) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          (1 / Real.sqrt (d : ℝ)) := by
  have hscale := typeIILambdaScale_pos a M P N ha hM hN hPlog
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtScale : Real.sqrt (typeIILambdaScale a M P N) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hscale)
  have hsqrtD : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdreal)
  have hlam :
      a * (d : ℝ) /
          (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) =
        typeIILambdaScale a M P N * (d : ℝ) := by
    unfold typeIILambdaScale
    ring
  dsimp [typeIIDistanceBound]
  rw [hlam, Real.sqrt_mul hscale.le]
  field_simp
  ring

/-- Exact separation of the full distance-envelope sum into the two elementary
finite sums. -/
theorem sum_typeIIDistanceBound_eq_scale
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) =
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          (∑ d ∈ Finset.Ioc 0 N, Real.sqrt (d : ℝ)) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          ∑ d ∈ Finset.Ioc 0 N, 1 / Real.sqrt (d : ℝ) := by
  calc
    _ = ∑ d ∈ Finset.Ioc 0 N, (
        (5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N)) *
            Real.sqrt (d : ℝ) +
          (10 / Real.sqrt (typeIILambdaScale a M P N)) *
            (1 / Real.sqrt (d : ℝ))) := by
      apply Finset.sum_congr rfl
      intro d hd
      simpa [mul_assoc] using typeIIDistanceBound_eq_scale
        a M P N d ha hM hN hPlog (Finset.mem_Ioc.mp hd).1
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Explicit finite estimate for the distance-envelope sum.  The inverse-root
part currently uses the coarse bound `Σ d⁻¹ᐟ² ≤ N`; improving it to the usual
`2√N` is localized to `sum_inv_sqrt_Ioc_le`. -/
theorem sum_typeIIDistanceBound_le_explicit
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) ≤
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          ((N : ℝ) * Real.sqrt (N : ℝ)) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) * (N : ℝ) := by
  rw [sum_typeIIDistanceBound_eq_scale a M P N ha hM hN hPlog]
  have hscale := typeIILambdaScale_pos a M P N ha hM hN hPlog
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sum_sqrt_Ioc_le_mul_sqrt N)
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg M))
        (Real.sqrt_nonneg _))
  · exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_Ioc_le N)
      (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- Sharp-order version of the explicit distance-envelope estimate, using the
telescoping bound `Σ d⁻¹ᐟ² ≤ 2√N`. -/
theorem sum_typeIIDistanceBound_le_explicit_sqrt
    (a : ℝ) (M P N : ℕ) (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) ≤
      5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
          ((N : ℝ) * Real.sqrt (N : ℝ)) +
        (10 / Real.sqrt (typeIILambdaScale a M P N)) *
          (2 * Real.sqrt (N : ℝ)) := by
  rw [sum_typeIIDistanceBound_eq_scale a M P N ha hM hN hPlog]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sum_sqrt_Ioc_le_mul_sqrt N)
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg M))
        (Real.sqrt_nonneg _))
  · exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_Ioc_le_two_mul_sqrt N)
      (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- One actual Type-II box after both Cauchy--Schwarz variables have been
discharged.  The remaining analytic object is the explicit one-dimensional
sum of `typeIIDistanceBound`. -/
theorem norm_sq_sum_productBandTerm_le_distanceSum
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
          4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 *
            ∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d) := by
  have hbase := norm_sq_sum_productBandTerm_le_explicit_diagonal_add_offDiagonal
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ hlam
  let S : ℝ := ∑ d ∈ Finset.Ioc 0 N, typeIIDistanceBound a M P N d
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun d hd => typeIIDistanceBound_nonneg a M P N d
  have hoff := sum_offDiagonal_typeIICorrelationBound_le_distanceMoment
    a U M B P Y N J hB hJ
  have hcoeff := sum_typeIICoeff_sq_le_on_dyadic U N J hJ
  have hoff' :
      (∑ n₁ ∈ J, ∑ n₂ ∈ J, if n₁ = n₂ then 0 else
          |typeIICoeff U n₁| * |typeIICoeff U n₂| *
            typeIICorrelationBound a M B P Y N n₁ n₂) ≤
        4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 * S := by
    calc
      _ ≤ 2 * (∑ n ∈ J, typeIICoeff U n ^ 2) * S := by
        simpa [S] using hoff
      _ ≤ 2 * (2 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff (by norm_num)) hS
      _ = _ := by ring
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact add_le_add le_rfl hoff'
  · positivity

/-- Fully explicit version of the one-box estimate: the two-dimensional
off-diagonal sum and the remaining one-dimensional distance sum have both been
eliminated. -/
theorem norm_sq_sum_productBandTerm_le_explicitDistance
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
          4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 *
            (5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
                ((N : ℝ) * Real.sqrt (N : ℝ)) +
              (10 / Real.sqrt (typeIILambdaScale a M P N)) *
                (2 * Real.sqrt (N : ℝ)))) := by
  have hbase := norm_sq_sum_productBandTerm_le_distanceSum
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ hlam
  have hdist := sum_typeIIDistanceBound_le_explicit_sqrt a M P N ha hM hN hPlog
  have harg : (1 : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * N by omega)
  have hlogN : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg harg
  have hfactor :
      0 ≤ 4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 := by positivity
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left hdist hfactor
  · positivity

/-- The pairwise small-curvature condition follows from one box-scale
inequality.  The factor `N` cancels because two points of `(N,2N]` are at
distance at most `N`. -/
theorem typeII_lambda_le_one_of_scale
    (a : ℝ) (M P N n₁ n₂ : ℕ)
    (ha : 0 < a) (hM : 0 < M) (hN : 0 < N)
    (hPlog : 1 ≤ Real.log (P : ℝ))
    (hn₁lo : N ≤ n₁) (hn₁hi : n₁ ≤ 2 * N)
    (hn₂lo : N ≤ n₂) (hn₂hi : n₂ ≤ 2 * N)
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) :
    a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) /
        (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1 := by
  have hminmax : min n₁ n₂ ≤ max n₁ n₂ := min_le_max
  have hdiffNat : max n₁ n₂ - min n₁ n₂ ≤ N := by
    have hlo : N ≤ min n₁ n₂ := le_min hn₁lo hn₂lo
    have hhi : max n₁ n₂ ≤ 2 * N := max_le hn₁hi hn₂hi
    omega
  have hdiffReal :
      (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) ≤ (N : ℝ) := by
    rw [← Nat.cast_sub hminmax]
    exact_mod_cast hdiffNat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have hden :
      0 < 32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3 := by
    positivity
  apply (div_le_one hden).2
  calc
    a * (((max n₁ n₂ : ℕ) : ℝ) - min n₁ n₂) ≤ a * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hdiffReal ha.le
    _ ≤ (32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hscale hNreal.le
    _ = 32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3 := by ring

/-- User-facing one-box theorem with the universally quantified `λ≤1`
hypothesis replaced by the single scale inequality on `a`, `M`, and `P`. -/
theorem norm_sq_sum_productBandTerm_le_explicitDistance_of_scale
    (a C : ℝ) (U V M B P Y N : ℕ) (J : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hJ : J ⊆ Finset.Ioc N (2 * N))
    (hscale : a ≤ 32 * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) :
    ‖∑ m ∈ Finset.Ioc M B, ∑ n ∈ J,
        productBandTerm (lambdaGT V) (typeIICoeff U) P Y
          (reciprocalLogWeight a) m n‖ ^ 2 ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 *
        (2 * (M : ℝ) * N * (1 + Real.log (2 * (N : ℝ))) ^ 3 +
          4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 *
            (5120 * (M : ℝ) * Real.sqrt (typeIILambdaScale a M P N) *
                ((N : ℝ) * Real.sqrt (N : ℝ)) +
              (10 / Real.sqrt (typeIILambdaScale a M P N)) *
                (2 * Real.sqrt (N : ℝ)))) := by
  apply norm_sq_sum_productBandTerm_le_explicitDistance
    a C U V M B P Y N J ha hC hP hPlog hCP hY hM hB hN hJ
  intro n₁ hn₁ n₂ hn₂ hne
  have h₁ := Finset.mem_Ioc.mp (hJ hn₁)
  have h₂ := Finset.mem_Ioc.mp (hJ hn₂)
  exact typeII_lambda_le_one_of_scale a M P N n₁ n₂ ha hM hN hPlog
    h₁.1.le h₁.2 h₂.1.le h₂.2 hscale

end
end Erdos878.TrackB

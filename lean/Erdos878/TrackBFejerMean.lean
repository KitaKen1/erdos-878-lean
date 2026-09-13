import Erdos878.TrackBFejerKernel

/-!
# Track B: finite weighted Fejér averaging

We keep the Fourier expansion as a double sum over sample indices. The
diagonal gives the constant coefficient; every off-diagonal difference is a
nonzero integer frequency. This avoids regrouping triangular coefficients.
-/

namespace Erdos878.TrackB
open Finset
open scoped ComplexConjugate
noncomputable section

def weightedPhaseSum {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) : ℂ :=
  ∑ r ∈ I, (w r : ℂ)*phaseCharacter ((k : ℝ)*u r)

theorem weightedPhaseSum_shift {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) (c : ℝ) :
    weightedPhaseSum I w (fun r => u r-c) k =
      phaseCharacter (-(k : ℝ)*c)*weightedPhaseSum I w u k := by
  unfold weightedPhaseSum
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  rw [show (k : ℝ)*(u r-c) = -(k : ℝ)*c+(k : ℝ)*u r by ring, phaseCharacter_add]
  ring

theorem norm_weightedPhaseSum_shift {α : Type*} (I : Finset α) (w u : α → ℝ) (k : ℤ) (c : ℝ) :
    ‖weightedPhaseSum I w (fun r => u r-c) k‖ = ‖weightedPhaseSum I w u k‖ := by
  rw [weightedPhaseSum_shift, norm_mul, norm_phaseCharacter, one_mul]

/-- Exact finite expansion of the unnormalized squared kernel. -/
theorem fejerPhaseSum_sq_expand (K : ℕ) (u : ℝ) :
    ((‖fejerPhaseSum K u‖^2 : ℝ) : ℂ) =
      ∑ i ∈ range K, ∑ j ∈ range K, phaseCharacter (((i : ℝ)-(j : ℝ))*u) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [fejerPhaseSum, map_sum]
  rw [sum_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [phaseCharacter_mul_conj]
  congr 1
  ring

theorem weighted_fejerPhaseSum_sq_expand {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c : ℝ) :
    ((∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2 : ℝ) : ℂ) =
      ∑ i ∈ range K, ∑ j ∈ range K,
        ∑ r ∈ I, (w r : ℂ)*phaseCharacter (((i : ℝ)-(j : ℝ))*(u r-c)) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, fejerPhaseSum_sq_expand, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

theorem fejer_pair_frequency (K i j : ℕ) (hi : i ∈ range K) (hj : j ∈ range K) (hne : i ≠ j) :
    (i : ℤ)-(j : ℤ) ≠ 0 ∧ |(((i : ℤ)-(j : ℤ) : ℤ) : ℝ)| < (K : ℝ) := by
  refine ⟨?_, ?_⟩
  · intro he
    exact hne (by exact_mod_cast sub_eq_zero.mp he)
  · have hiK : (i : ℝ) < K := by exact_mod_cast mem_range.mp hi
    have hjK : (j : ℝ) < K := by exact_mod_cast mem_range.mp hj
    have hi0 := Nat.cast_nonneg (α := ℝ) i
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    push_cast
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Bounding every nonconstant frequency by E bounds the whole normalized
kernel's mean error by E, with no factor depending on the number of frequencies. -/
theorem abs_weighted_finiteFejerKernel_sub_mean_le {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c E : ℝ) (hK : 0 < K) (hE : 0 ≤ E)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    |(∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - (∑ r ∈ I, w r)/(K : ℝ)| ≤ E := by
  classical
  let M : ℝ := ∑ r ∈ I, w r
  let Q := fun i j : ℕ => ∑ r ∈ I, (w r : ℂ)*phaseCharacter (((i : ℝ)-(j : ℝ))*(u r-c))
  have hdiag (i : ℕ) : Q i i = (M : ℂ) := by simp [Q, M, phaseCharacter]
  have hdiagSum : (∑ i ∈ range K, ∑ j ∈ range K, if i=j then (M : ℂ) else 0) = (K : ℂ)*M := by
    calc
      _ = ∑ _i ∈ range K, (M : ℂ) := by
        apply sum_congr rfl
        intro i hi
        simp [hi]
      _ = _ := by simp
  have hcenter : (∑ i ∈ range K, ∑ j ∈ range K, Q i j) - (K : ℂ)*M =
      ∑ i ∈ range K, ∑ j ∈ range K, (Q i j - if i=j then (M : ℂ) else 0) := by
    simp only [sum_sub_distrib]
    rw [hdiagSum]
  have hterm (i : ℕ) (hi : i ∈ range K) (j : ℕ) (hj : j ∈ range K) :
      ‖Q i j - if i=j then (M : ℂ) else 0‖ ≤ E := by
    by_cases hij : i=j
    · subst j
      simpa [hdiag] using hE
    · rw [ite_eq_right hij, sub_zero]
      have hk := fejer_pair_frequency K i j hi hj hij
      have ht := (norm_weightedPhaseSum_shift I w u ((i : ℤ)-(j : ℤ)) c).trans_le
        (hfreq _ hk.1 hk.2)
      simpa only [weightedPhaseSum, Int.cast_sub, Int.cast_natCast] using ht
  have hc : ‖(∑ i ∈ range K, ∑ j ∈ range K, Q i j) - (K : ℂ)*M‖ ≤ (K : ℝ)^2*E := by
    rw [hcenter]
    calc
      _ ≤ ∑ i ∈ range K, ∑ j ∈ range K, ‖Q i j - if i=j then (M : ℂ) else 0‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ _i ∈ range K, ∑ _j ∈ range K, E :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
      _ = _ := by simp; ring
  have hr : |(∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2) - (K : ℝ)*M| ≤ (K : ℝ)^2*E := by
    rw [← weighted_fejerPhaseSum_sq_expand I w u K c] at hc
    rw [show (K : ℂ) = ((K : ℝ) : ℂ) by norm_cast] at hc
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hc
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmean : (∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - M/(K : ℝ) =
      ((∑ r ∈ I, w r*‖fejerPhaseSum K (u r-c)‖^2) - (K : ℝ)*M)/(K : ℝ)^2 := by
    simp only [finiteFejerKernel, ← mul_div_assoc, ← sum_div]
    field_simp
  change |(∑ r ∈ I, w r*finiteFejerKernel K (u r-c)) - M/(K : ℝ)| ≤ E
  rw [hmean, abs_div, abs_of_nonneg (sq_nonneg (K : ℝ))]
  exact (div_le_iff₀ (pow_pos hKr 2)).2 (by simpa only [mul_comm] using hr)

/-- The minorant turns cancellation into a lower bound for mass inside the window. -/
theorem weighted_phaseWindow_mass_lower {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c b E : ℝ)
    (hK : 0 < K) (hb : 0 < b) (hE : 0 ≤ E) (hw : ∀ r ∈ I, 0 ≤ w r)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    (1/(K : ℝ)-fejerLeakage K b)*(∑ r ∈ I, w r)-E ≤
      ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
  classical
  have he := abs_weighted_finiteFejerKernel_sub_mean_le I w u K c E hK hE hfreq
  have hm : (∑ r ∈ I, w r)/(K : ℝ)-E ≤ ∑ r ∈ I, w r*finiteFejerKernel K (u r-c) := by
    linarith [(abs_le.mp he).1]
  have hsum : (∑ r ∈ I, w r*finiteFejerMinorant K c b (u r)) =
      (∑ r ∈ I, w r*finiteFejerKernel K (u r-c))-fejerLeakage K b*(∑ r ∈ I, w r) := by
    simp only [finiteFejerMinorant, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  have hcount : (∑ r ∈ I, w r*finiteFejerMinorant K c b (u r)) ≤
      ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
    rw [sum_filter]
    apply sum_le_sum
    intro r hr
    have ht := mul_le_mul_of_nonneg_left
      (finiteFejerMinorant_le_indicator K c b (u r) hK hb) (hw r hr)
    split_ifs at ht ⊢ <;> simpa only [mul_one, mul_zero] using ht
  calc
    _ = (∑ r ∈ I, w r)/(K : ℝ)-E-fejerLeakage K b*(∑ r ∈ I, w r) := by ring
    _ ≤ (∑ r ∈ I, w r*finiteFejerKernel K (u r-c))-fejerLeakage K b*(∑ r ∈ I, w r) :=
      sub_le_sub_right hm _
    _ = _ := hsum.symm
    _ ≤ _ := hcount

theorem weighted_phaseWindow_mass_lower_half {α : Type*}
    (I : Finset α) (w u : α → ℝ) (K : ℕ) (c b E : ℝ)
    (hK : 0 < K) (hb : 0 < b) (hwidth : 1 ≤ 2*(K : ℝ)*b^2)
    (hE : 0 ≤ E) (hw : ∀ r ∈ I, 0 ≤ w r)
    (hfreq : ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| < (K : ℝ) → ‖weightedPhaseSum I w u k‖ ≤ E) :
    (∑ r ∈ I, w r)/(2*(K : ℝ))-E ≤ ∑ r ∈ I with inPhaseWindow c b (u r), w r := by
  have hm : 0 ≤ ∑ r ∈ I, w r := sum_nonneg hw
  calc
    _ = (1/(2*(K : ℝ)))*(∑ r ∈ I, w r)-E := by ring
    _ ≤ (1/(K : ℝ)-fejerLeakage K b)*(∑ r ∈ I, w r)-E :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right (fejer_constant_coefficient_lower K b hK hb hwidth) hm) E
    _ ≤ _ := weighted_phaseWindow_mass_lower I w u K c b E hK hb hE hw hfreq

end
end Erdos878.TrackB

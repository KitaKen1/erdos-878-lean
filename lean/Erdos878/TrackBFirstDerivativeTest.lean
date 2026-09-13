import Erdos878.TrackBKusminLandau

/-!
# Track B: from monotone derivatives to finite exponential sums

The mean value theorem puts successive phase increments in the same nonresonant
strip as the derivative. No derivative outside the closed sampling interval is used.
-/

namespace Erdos878.TrackB
open Finset Set
noncomputable section

@[simp] theorem phaseCharacter_int (z : ℤ) : phaseCharacter (z : ℝ) = 1 := by
  unfold phaseCharacter
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  congr 1
  push_cast
  ring

theorem phaseCharacter_sub_int (s : ℝ) (z : ℤ) :
    phaseCharacter (s - z) = phaseCharacter s := by
  have h := (phaseCharacter_add (s - z) z).symm
  simpa only [sub_add_cancel, phaseCharacter_int, mul_one] using h

theorem norm_sum_phaseCharacter_le_of_monotone_deriv
    (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (f' x) x)
    (hm : MonotoneOn f' (Set.Ioo a (a + N)))
    (hlo : ∀ x ∈ Set.Ioo a (a + N), δ ≤ f' x)
    (hhi : ∀ x ∈ Set.Ioo a (a + N), f' x ≤ 1 - δ) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤ 1 + 1 / δ := by
  have hw (k : ℕ) (hk : k < N) : ∃ x ∈ Set.Ioo (a + k) (a + (k + 1 : ℕ)),
      f' x = f (a + (k + 1 : ℕ)) - f (a + k) := by
    have hkn : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
    have hsub : Set.Icc (a + k) (a + (k + 1 : ℕ)) ⊆ Set.Icc a (a + N) := by
      intro x hx
      simp only [Nat.cast_add, Nat.cast_one, Set.mem_Icc] at hx ⊢
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f'
      (show a + (k : ℝ) < a + ((k + 1 : ℕ) : ℝ) by push_cast; linarith)
      (hc.mono hsub) (fun x hx => hd x (by
        simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx ⊢
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]))
    refine ⟨x, hx, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub,
      add_sub_cancel_left, div_one] using he
  have hmem (k : ℕ) (hk : k < N) {x : ℝ}
      (hx : x ∈ Set.Ioo (a + k) (a + (k + 1 : ℕ))) : x ∈ Set.Ioo a (a + N) := by
    have hkn : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
    simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx ⊢
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  apply norm_sum_phaseCharacter_le_of_monotone_increments_closed
    (fun k => f (a + k)) N δ hδ
  · intro k hk
    obtain ⟨x, hx, he⟩ := hw k hk
    exact he ▸ hlo x (hmem k hk hx)
  · intro k hk
    obtain ⟨x, hx, he⟩ := hw k hk
    exact he ▸ hhi x (hmem k hk hx)
  · intro i hi j hj hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    obtain ⟨x, hx, he⟩ := hw i hi.2
    obtain ⟨y, hy, he'⟩ := hw j hj.2
    have hijR : (i + 1 : ℝ) ≤ j := by exact_mod_cast hij
    have hxy : x ≤ y := by
      simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioo] at hx hy
      linarith
    dsimp only
    rw [← he, ← he']
    exact hm (hmem i hi.2 hx) (hmem j hj.2 hy) hxy

/-- The same test on any integer strip. Subtracting the integer linear phase
does not alter the sampled exponential values. -/
theorem norm_sum_phaseCharacter_le_of_monotone_deriv_strip
    (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (f' x) x)
    (hm : MonotoneOn f' (Set.Ioo a (a + N)))
    (hlo : ∀ x ∈ Set.Ioo a (a + N), (z : ℝ) + δ ≤ f' x)
    (hhi : ∀ x ∈ Set.Ioo a (a + N), f' x ≤ (z : ℝ) + 1 - δ) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤ 1 + 1 / δ := by
  have h := norm_sum_phaseCharacter_le_of_monotone_deriv
    (fun x => f x - (z : ℝ) * (x - a)) (fun x => f' x - z) a N δ hδ
    (hc.sub (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
    (fun x hx => by
      convert (hd x hx).sub (((hasDerivAt_id x).sub_const a).const_mul (z : ℝ)) using 1 <;>
        first | rfl | simp only [mul_one])
    (fun x hx y hy hxy => sub_le_sub_right (hm hx hy hxy) _)
    (fun x hx => by linarith [hlo x hx]) (fun x hx => by linarith [hhi x hx])
  have he (k : ℕ) : phaseCharacter (f (a + k) - (z : ℝ) * (a + k - a)) =
      phaseCharacter (f (a + k)) := by
    rw [add_sub_cancel_left]
    simpa only [Int.cast_mul, Int.cast_natCast] using
      phaseCharacter_sub_int (f (a + k)) (z * (k : ℤ))
  simpa only [he] using h

end
end Erdos878.TrackB

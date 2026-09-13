import Erdos878.TrackBFejerApplication
import Mathlib.NumberTheory.Chebyshev

/-!
# Track B: remove prime powers and count primes in the phase window

Only Mathlib's explicit Chebyshev bounds are used. No prime number theorem or
short-interval prime theorem is an input.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

def logSquaredGoodSet (P : ℕ) (t : ℝ) : Finset ℕ :=
  (Ioc P (16*P)).filter (fun r : ℕ =>
    1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (r : ℝ)) ∧
      Int.fract (t/Real.log (r : ℝ)) ≤ 2/Real.log (P : ℝ)^2)

def logSquaredGoodPrimes (P : ℕ) (t : ℝ) : Finset ℕ :=
  (logSquaredGoodSet P t).filter Nat.Prime

theorem sum_vonMangoldt_Ioc_eq_psi_sub (P Q : ℕ) (hPQ : P ≤ Q) :
    (∑ n ∈ Ioc P Q, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi Q - Chebyshev.psi P := by
  have hd : Disjoint (Ioc 0 P) (Ioc P Q) := Ioc_disjoint_Ioc_of_le le_rfl
  have hu := Ioc_union_Ioc_eq_Ioc (show 0 ≤ P by omega) hPQ
  have hs : (∑ n ∈ Ioc 0 Q, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ Ioc 0 P, ArithmeticFunction.vonMangoldt n) +
        ∑ n ∈ Ioc P Q, ArithmeticFunction.vonMangoldt n := by
    rw [← hu, sum_union hd]
  simp only [Chebyshev.psi, Nat.floor_natCast] at hs ⊢
  linarith

theorem sum_prime_vonMangoldt_Ioc_eq_theta_sub (P Q : ℕ) (hPQ : P ≤ Q) :
    (∑ n ∈ (Ioc P Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.theta Q - Chebyshev.theta P := by
  have hd : Disjoint ((Ioc 0 P).filter Nat.Prime) ((Ioc P Q).filter Nat.Prime) :=
    Disjoint.mono (filter_subset _ _) (filter_subset _ _) (Ioc_disjoint_Ioc_of_le le_rfl)
  have hu : (Ioc 0 P).filter Nat.Prime ∪ (Ioc P Q).filter Nat.Prime =
      (Ioc 0 Q).filter Nat.Prime := by
    rw [← filter_union, Ioc_union_Ioc_eq_Ioc (show 0 ≤ P by omega) hPQ]
  have he (R : ℕ) : (∑ n ∈ (Ioc 0 R).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ (Ioc 0 R).filter Nat.Prime, Real.log n := by
    apply sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2
  have hs : (∑ n ∈ (Ioc 0 Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ (Ioc 0 P).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) +
        ∑ n ∈ (Ioc P Q).filter Nat.Prime, ArithmeticFunction.vonMangoldt n := by
    rw [← hu, sum_union hd]
  rw [he P, he Q] at hs
  simp only [Chebyshev.theta, Nat.floor_natCast] at hs ⊢
  linarith

/-- The wide band has a fixed positive von Mangoldt mass using only Chebyshev bounds. -/
theorem sum_vonMangoldt_wide_band_lower (P : ℕ) (h : trackBScaleCondition P) :
    5*(P : ℝ) ≤ ∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have hP16 := trackBScaleCondition_sixteen_le P h
  have hP : 0 < P := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := zero_lt_one.trans_le h.1
  have hlog16 : Real.log ((16*P+1 : ℕ) : ℝ) ≤ 3*L := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h (by exact_mod_cast hP16) (by omega) (by norm_num)).2.1
  have hlog16P : Real.log ((16*P : ℕ) : ℝ) ≤ 2*L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h (by exact_mod_cast hP16) (by omega) (by norm_num)).1
  have hsqrt16 : Real.sqrt ((16*P : ℕ) : ℝ) = 4*S := by
    have hsqrt_four : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    calc
      _ = Real.sqrt ((16 : ℝ)*(P : ℝ)) := by norm_cast
      _ = Real.sqrt (16 : ℝ)*Real.sqrt (P : ℝ) := Real.sqrt_mul (by norm_num) _
      _ = _ := by rw [hsqrt_four]
  have hlogerr : Real.log ((16*P+1 : ℕ) : ℝ) ≤ (P : ℝ)/4 := by
    have hLP : 16*L ≤ (P : ℝ) := by
      calc
        _ = 16*L^1 := by ring
        _ ≤ 16*L^400 := mul_le_mul_of_nonneg_left
          (show L^1 ≤ L^400 by exact (pow_le_pow_right₀ h.1 (by decide))) (by norm_num)
        _ ≤ _ := h.2
    linarith
  have hsqrt : 4*L ≤ S := by
    calc
      _ = 4*L^1 := by ring
      _ ≤ 4*L^200 := mul_le_mul_of_nonneg_left
        (show L^1 ≤ L^200 by exact pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  have hsqrterr : 2*Real.sqrt ((16*P : ℕ) : ℝ)*Real.log ((16*P : ℕ) : ℝ) ≤ 4*(P : ℝ) := by
    rw [hsqrt16]
    have hSS := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
    have hlog0 : 0 ≤ Real.log ((16*P : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 16*P by omega))
    have hprod := mul_le_mul_of_nonneg_left hlog16P (Real.sqrt_nonneg (P : ℝ))
    have hprod2 := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4*S by positivity)
    nlinarith
  have htheta16 := Chebyshev.theta_ge (16*P)
  have hthetaP := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) hPr.le
  have hprimeBand : 5*(P : ℝ) ≤
      Chebyshev.theta (16*P) - Chebyshev.theta P := by
    rw [Real.log_four_eq] at hthetaP
    have hlog2 := Real.log_two_gt_d9
    have hlog2P := mul_le_mul_of_nonneg_right hlog2.le hPr.le
    have hmain : (19/2 : ℝ)*(P : ℝ) ≤ 14*Real.log 2*(P : ℝ) := by nlinarith
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at htheta16
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hlogerr hsqrterr
    nlinarith
  have hprime : 5*(P : ℝ) ≤
      ∑ n ∈ (Ioc P (16*P)).filter Nat.Prime, ArithmeticFunction.vonMangoldt n := by
    rw [sum_prime_vonMangoldt_Ioc_eq_theta_sub P (16*P) (by omega)]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact hprimeBand
  exact hprime.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg))

/-- All nonprime von Mangoldt mass below `16P` is negligible at the Fejér scale. -/
theorem sum_nonprime_vonMangoldt_wide_upper (P : ℕ) (h : trackBScaleCondition P)
    (hL2 : 2 ≤ Real.log (P : ℝ)) :
    (∑ n ∈ (Ioc 0 (16*P)).filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n) ≤
      (P : ℝ)/(2*Real.log (P : ℝ)^6) := by
  let L := Real.log (P : ℝ)
  let S := Real.sqrt (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P h; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by linarith
  have hlog16P : Real.log ((16*P : ℕ) : ℝ) ≤ 2*L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) h
        (by exact_mod_cast trackBScaleCondition_sixteen_le P h) (by omega) (by norm_num)).1
  have hsqrt16 : Real.sqrt ((16*P : ℕ) : ℝ) = 4*S := by
    have hsqrt_four : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    calc
      _ = Real.sqrt ((16 : ℝ)*(P : ℝ)) := by norm_cast
      _ = Real.sqrt (16 : ℝ)*Real.sqrt (P : ℝ) := Real.sqrt_mul (by norm_num) _
      _ = _ := by rw [hsqrt_four]
  have hL193 : 8 ≤ L^193 := by
    calc
      8 = (2 : ℝ)^3 := by norm_num
      _ ≤ L^3 := pow_le_pow_left₀ (by norm_num) hL2 3
      _ ≤ L^193 := pow_le_pow_right₀ (by linarith) (by decide)
  have hscale : 32*L^7 ≤ S := by
    have ht : 8*L^7 ≤ L^193*L^7 := mul_le_mul_of_nonneg_right hL193 (pow_nonneg hL.le 7)
    calc
      _ = 4*(8*L^7) := by ring
      _ ≤ 4*(L^193*L^7) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = 4*L^200 := by ring
      _ ≤ _ := trackBScaleCondition_sqrt_lower P h
  have he := Chebyshev.psi_sub_theta_eq_sum_not_prime ((16*P : ℕ) : ℝ)
  simp only [Nat.floor_natCast] at he
  rw [← he]
  have ht := Chebyshev.psi_sub_theta_le (x := ((16*P : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ 16*P by omega))
  rw [hsqrt16] at ht
  refine ht.trans ?_
  have hSS := Real.sq_sqrt (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hlog0 : 0 ≤ Real.log ((16*P : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 16*P by omega))
  apply (le_div_iff₀ (by positivity)).2
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have ha : 16*S*Real.log ((16*P : ℕ) : ℝ)*L^6 ≤ 32*S*L^7 := by
    calc
      _ = (16*S*L^6)*Real.log ((16*P : ℕ) : ℝ) := by ring
      _ ≤ (16*S*L^6)*(2*L) := mul_le_mul_of_nonneg_left hlog16P
        (mul_nonneg (mul_nonneg (by norm_num) hS0) (pow_nonneg hL.le 6))
      _ = _ := by ring
  have hb : 32*S*L^7 ≤ S*S := by
    have hm := mul_le_mul_of_nonneg_left hscale hS0
    nlinarith
  rw [show S*S = (P : ℝ) by nlinarith [hSS]] at hb
  nlinarith

theorem logSquaredGoodSet_sum_split (P : ℕ) (t : ℝ) :
    (∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n) =
      (∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p) +
        ∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
          ArithmeticFunction.vonMangoldt n := by
  rw [logSquaredGoodPrimes]
  exact (sum_filter_add_sum_filter_not (logSquaredGoodSet P t) Nat.Prime
    ArithmeticFunction.vonMangoldt).symm

theorem logSquaredGoodSet_nonprime_subset (P : ℕ) (t : ℝ) :
    (logSquaredGoodSet P t).filter (fun n => ¬n.Prime) ⊆
      (Ioc 0 (16*P)).filter (fun n => ¬n.Prime) := by
  intro n hn
  rw [mem_filter] at hn ⊢
  have hband := (mem_filter.mp hn.1).1
  refine ⟨?_, hn.2⟩
  rw [mem_Ioc]
  exact ⟨lt_of_le_of_lt (Nat.zero_le P) (mem_Ioc.mp hband).1,
    (mem_Ioc.mp hband).2⟩

/-- The analytic phase-window estimate contains actual primes, after higher prime
powers are removed with Mathlib's explicit Chebyshev estimate. -/
theorem eventually_goodPrime_vonMangoldt_mass_lower :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      (P : ℝ)/Real.log (P : ℝ)^6 ≤
        ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by
  have hlog : ∀ᶠ P : ℕ in atTop, 3 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 3)
  filter_upwards [eventually_vonMangoldt_logSquaredWindow_mass_lower 16 (by norm_num),
    eventually_trackBScaleCondition, hlog] with P hwindow hscale hL3
  intro t htlo hthi
  let L := Real.log (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P hscale; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by dsimp [L]; linarith
  have hwide := sum_vonMangoldt_wide_band_lower P hscale
  have hwindow' :
      (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) -
          256000000*(P : ℝ)/L^25 ≤
        ∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n := by
    have hw := hwindow t htlo hthi (16*P) (16*P) (by omega) (by norm_num) (by omega)
    have hc : (1000000 : ℝ)*16^2 = 256000000 := by norm_num
    rw [hc] at hw
    simpa only [logSquaredGoodSet, L] using hw
  have hpow19 : (512000000 : ℝ) ≤ L^19 := by
    calc
      _ ≤ (3 : ℝ)^19 := by norm_num
      _ ≤ L^19 := pow_le_pow_left₀ (by norm_num) (by simpa only [L] using hL3) 19
  have hpow : (512000000 : ℝ)*L^6 ≤ L^25 := by
    have hp := mul_le_mul_of_nonneg_right hpow19 (pow_nonneg hL.le 6)
    calc
      _ ≤ L^19*L^6 := hp
      _ = _ := by ring
  have herr : 256000000*(P : ℝ)/L^25 ≤ (P : ℝ)/(2*L^6) := by
    apply (div_le_div_iff₀ (pow_pos hL 25) (mul_pos (by norm_num) (pow_pos hL 6))).2
    calc
      (256000000*(P : ℝ))*(2*L^6) = (P : ℝ)*((512000000 : ℝ)*L^6) := by ring
      _ ≤ (P : ℝ)*L^25 := mul_le_mul_of_nonneg_left hpow hPr.le
  have hmain : 5*(P : ℝ)/(2*L^6) ≤
      (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) :=
    div_le_div_of_nonneg_right hwide (by positivity)
  have hgood : 2*(P : ℝ)/L^6 ≤
      ∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n := by
    calc
      2*(P : ℝ)/L^6 = 5*(P : ℝ)/(2*L^6) - (P : ℝ)/(2*L^6) := by field_simp; ring
      _ ≤ (∑ n ∈ Ioc P (16*P), ArithmeticFunction.vonMangoldt n)/(2*L^6) -
          256000000*(P : ℝ)/L^25 := sub_le_sub hmain herr
      _ ≤ _ := hwindow'
  have hnonprime :
      (∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n) ≤ (P : ℝ)/(2*L^6) := by
    exact (sum_le_sum_of_subset_of_nonneg (logSquaredGoodSet_nonprime_subset P t)
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans
        (by
          simpa only [L] using
            (sum_nonprime_vonMangoldt_wide_upper P hscale
              (by linarith : 2 ≤ Real.log (P : ℝ))))
  have hsplit := logSquaredGoodSet_sum_split P t
  have hsafe : (P : ℝ)/L^6 ≤ 2*(P : ℝ)/L^6 - (P : ℝ)/(2*L^6) := by
    apply (div_le_iff₀ (pow_pos hL 6)).2
    field_simp
    nlinarith
  calc
    (P : ℝ)/Real.log (P : ℝ)^6 = (P : ℝ)/L^6 := by rfl
    _ ≤ 2*(P : ℝ)/L^6 - (P : ℝ)/(2*L^6) := hsafe
    _ ≤ (∑ n ∈ logSquaredGoodSet P t, ArithmeticFunction.vonMangoldt n) -
        ∑ n ∈ (logSquaredGoodSet P t).filter (fun n => ¬n.Prime),
          ArithmeticFunction.vonMangoldt n := sub_le_sub hgood hnonprime
    _ = ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by linarith

theorem goodPrime_vonMangoldt_le_two_log (P : ℕ) (t : ℝ)
    (hscale : trackBScaleCondition P) (p : ℕ) (hp : p ∈ logSquaredGoodPrimes P t) :
    ArithmeticFunction.vonMangoldt p ≤ 2*Real.log (P : ℝ) := by
  have hpfilter := mem_filter.mp hp
  have hpprime : p.Prime := hpfilter.2
  have hpband := (mem_filter.mp hpfilter.1).1
  have hp_le : p ≤ 16*P := (mem_Ioc.mp hpband).2
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hP_pos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by have := trackBScaleCondition_sixteen_le P hscale; omega)
  have hlogmono : Real.log (p : ℝ) ≤ Real.log ((16*P : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hp_pos)
      (show ((16*P : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ((16*P : ℕ) : ℝ)
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        positivity)
      (by exact_mod_cast hp_le)
  have hlogendpoint : Real.log ((16*P : ℕ) : ℝ) ≤ 2*Real.log (P : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (trackBEndpoint_log_bounds 16 P (16*P) hscale
        (by exact_mod_cast trackBScaleCondition_sixteen_le P hscale) (by omega) (by norm_num)).1
  rw [ArithmeticFunction.vonMangoldt_apply_prime hpprime]
  exact hlogmono.trans hlogendpoint

/-- Quantitative prime selection in the logarithmic phase window. This is an actual
cardinality lower bound, rather than a von Mangoldt weighted statement. -/
theorem eventually_logSquaredGoodPrimes_card_lower :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      (P : ℝ)/(2*Real.log (P : ℝ)^7) ≤ (logSquaredGoodPrimes P t).card := by
  have hlog : ∀ᶠ P : ℕ in atTop, 3 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 3)
  filter_upwards [eventually_goodPrime_vonMangoldt_mass_lower,
    eventually_trackBScaleCondition, hlog] with P hmass hscale hL3
  intro t htlo hthi
  let L := Real.log (P : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hmass' : (P : ℝ)/L^6 ≤
      ∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p := by
    simpa only [L] using hmass t htlo hthi
  have hsum : (∑ p ∈ logSquaredGoodPrimes P t, ArithmeticFunction.vonMangoldt p) ≤
      (logSquaredGoodPrimes P t).card*(2*L) := by
    calc
      _ ≤ ∑ _p ∈ logSquaredGoodPrimes P t, 2*L := by
        apply sum_le_sum
        intro p hp
        simpa only [L] using goodPrime_vonMangoldt_le_two_log P t hscale p hp
      _ = _ := by simp [mul_comm]
  have hmassCard : (P : ℝ)/L^6 ≤ (logSquaredGoodPrimes P t).card*(2*L) :=
    hmass'.trans hsum
  have hmul : (P : ℝ) ≤ (logSquaredGoodPrimes P t).card*(2*L)*L^6 :=
    (div_le_iff₀ (pow_pos hL 6)).mp hmassCard
  apply (div_le_iff₀ (mul_pos (by norm_num) (pow_pos hL 7))).2
  calc
    (P : ℝ) ≤ (logSquaredGoodPrimes P t).card*(2*L)*L^6 := hmul
    _ = ((logSquaredGoodPrimes P t).card : ℝ)*(2*L^7) := by ring

theorem exists_logSquaredGoodPrime_family_of_card_le (P N : ℕ) (t : ℝ)
    (hN : N ≤ (logSquaredGoodPrimes P t).card) :
    ∃ S : Finset ℕ, S ⊆ logSquaredGoodPrimes P t ∧ S.card = N ∧
      ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 16*P ∧
        1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (p : ℝ)) ∧
        Int.fract (t/Real.log (p : ℝ)) ≤ 2/Real.log (P : ℝ)^2 := by
  obtain ⟨S, hsub, hcard⟩ := exists_subset_card_eq hN
  refine ⟨S, hsub, hcard, ?_⟩
  intro p hp
  have hpg := mem_filter.mp (hsub hp)
  have hbase := mem_filter.mp hpg.1
  exact ⟨hpg.2, (mem_Ioc.mp hbase.1).1, (mem_Ioc.mp hbase.1).2,
    hbase.2.1, hbase.2.2⟩

/-- Extract any required finite number of primes from the quantitative window,
provided the requested cardinality is below the proved real-valued lower bound. -/
theorem eventually_exists_logSquaredGoodPrime_family :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t →
      t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ N : ℕ, (N : ℝ) ≤ (P : ℝ)/(2*Real.log (P : ℝ)^7) →
      ∃ S : Finset ℕ, S ⊆ logSquaredGoodPrimes P t ∧ S.card = N ∧
        ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 16*P ∧
          1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (p : ℝ)) ∧
          Int.fract (t/Real.log (p : ℝ)) ≤ 2/Real.log (P : ℝ)^2 := by
  filter_upwards [eventually_logSquaredGoodPrimes_card_lower] with P hcard
  intro t htlo hthi N hN
  apply exists_logSquaredGoodPrime_family_of_card_le P N t
  exact_mod_cast hN.trans (hcard t htlo hthi)

end
end Erdos878.TrackB

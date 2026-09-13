import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic
import FormalConjecturesForMathlib.Data.Set.Density
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos878.OmegaBound
import Erdos878.RelaxedBound
import Erdos878.BadPair
import Erdos878.PrimeMass
import Erdos878.UnionBound
import Erdos878.Rotation
import CheckScalar
import CheckNatScalar
import CheckEndpoint

/-!
# Erdős Problem 878: Formal Conjectures target development

This file targets the three independent prospective FC-style asymptotic propositions declared in
`../FClikelean/Erdos878.lean`: the density-one result for `F`, the maximal-order result for `f`,
and the proposed strengthening of formula (17) in Erdős's original paper.

The finite and conditional interfaces below are proved.  The final asymptotic claims remain named
propositions (rather than unproved theorem declarations); this keeps the source honest while the
missing analytic selection and normal-order estimates are supplied by future work.

Feasibility audit (2026-09-12): the prefix-weighted Track-A scale-moment assumptions and the
Track-B reciprocal-mass selection assumptions are inconsistent. `Erdos878.CertificateAudit`
proves their negations; their conditional wrappers below are historical, unusable routes.
`Erdos878.MatchingAsymptotic` supplies a corrected matching-deficit interface for Track A.
-/

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/- The source paper writes `H(x) = Σ_{1 ≤ n < x} f(n)/n`, whereas the finite decomposition in
   this file is most convenient on the closed interval `Icc 1 X`.  These endpoint bridges keep the
   two conventions exact. -/
noncomputable def sourceH (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / (n : ℝ)

/-- FC-facing name for the source sum. The older proof development uses `sourceH`; keeping this
as an abbreviation makes the official-remarks declarations match the FClike catalog exactly. -/
noncomputable abbrev H (x : ℕ) : ℝ := sourceH x

theorem sourceH_eq_Icc_pred (x : ℕ) :
    sourceH x = ∑ n ∈ Finset.Icc 1 (x - 1), (f n : ℝ) / (n : ℝ) := by
  unfold sourceH
  rw [show Finset.Ico 1 x = Finset.Icc 1 (x - 1) by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega]

theorem sourceH_succ_eq_Icc (X : ℕ) :
    sourceH (X + 1) = ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ) := by
  unfold sourceH
  rw [show Finset.Ico 1 (X + 1) = Finset.Icc 1 X by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega]

/- A reusable dyadic-recursion lemma.  It turns a bound on every doubled block into a global
   summatory bound, provided the comparison function is positive and monotone beyond a threshold.
   The finite initial range is deliberately an explicit hypothesis: this keeps endpoint/log-domain
   bookkeeping visible rather than hiding it in an asymptotic axiom. -/
theorem sum_Icc_le_of_dyadic_block_bound
    (g φ : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hg : ∀ n : ℕ, 0 ≤ g n)
    (hφpos : ∀ n : ℕ, N ≤ n → 0 < φ n)
    (hφmono : ∀ {a b : ℕ}, N ≤ a → a ≤ b → φ a ≤ φ b)
    (hbase : ∀ X : ℕ, X < 2 * N + 1 →
      (∑ n ∈ Finset.Icc 1 X, g n) ≤ C * (X : ℝ) * φ X)
    (hblock : ∀ X : ℕ, N ≤ X →
      (∑ n ∈ Finset.Icc X (2 * X), g n) ≤ C * (X : ℝ) * φ X) :
    ∀ X : ℕ, (∑ n ∈ Finset.Icc 1 X, g n) ≤ C * (X : ℝ) * φ X := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hsmall : X < 2 * N + 1
      · exact hbase X hsmall
      · let m : ℕ := (X + 1) / 2
        have hXlarge : 2 * N + 1 ≤ X := by omega
        have hmN : N ≤ m := by
          dsimp [m]
          omega
        have hmpos : 0 < m := by omega
        have hmle : m ≤ X := by
          dsimp [m]
          omega
        have hmminus_lt : m - 1 < X := by omega
        have hmminusN : N ≤ m - 1 := by
          dsimp [m]
          omega
        have hXle : X ≤ 2 * m := by
          dsimp [m]
          omega
        have hsplit : Finset.Icc 1 X =
            Finset.Icc 1 (m - 1) ∪ Finset.Icc m X := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_union]
          omega
        have hdisj : Disjoint (Finset.Icc 1 (m - 1)) (Finset.Icc m X) := by
          rw [Finset.disjoint_left]
          intro n hn₁ hn₂
          have h₁ := Finset.mem_Icc.mp hn₁
          have h₂ := Finset.mem_Icc.mp hn₂
          omega
        have htail :
            (∑ n ∈ Finset.Icc m X, g n) ≤
              ∑ n ∈ Finset.Icc m (2 * m), g n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have hnI := Finset.mem_Icc.mp hn
            exact Finset.mem_Icc.mpr ⟨hnI.1, hnI.2.trans hXle⟩
          · intro n hn hnot
            exact hg n
        have hsmall' := ih (m - 1) hmminus_lt
        have hblock' := hblock m hmN
        have hφX : 0 < φ X := hφpos X (by omega)
        have hφm : 0 < φ m := hφpos m hmN
        have hφmminus : 0 < φ (m - 1) := hφpos (m - 1) hmminusN
        have hmonom : φ m ≤ φ X := hφmono hmN hmle
        have hmonomminus : φ (m - 1) ≤ φ X :=
          hφmono hmminusN (by omega)
        have hsmall'' :
            C * ((m - 1 : ℕ) : ℝ) * φ (m - 1) ≤
              C * ((m - 1 : ℕ) : ℝ) * φ X := by
          exact mul_le_mul_of_nonneg_left hmonomminus
            (mul_nonneg hC (by positivity))
        have hblock'' :
            C * (m : ℝ) * φ m ≤ C * (m : ℝ) * φ X := by
          exact mul_le_mul_of_nonneg_left hmonom (mul_nonneg hC (by positivity))
        have hsum :
            (∑ n ∈ Finset.Icc 1 X, g n) ≤
              C * ((m - 1 : ℕ) : ℝ) * φ (m - 1) +
                C * (m : ℝ) * φ m := by
          rw [hsplit, Finset.sum_union hdisj]
          exact add_le_add hsmall' (htail.trans hblock')
        have hsum' :
            (∑ n ∈ Finset.Icc 1 X, g n) ≤
              C * ((m - 1 : ℕ) : ℝ) * φ X + C * (m : ℝ) * φ X :=
          hsum.trans (add_le_add hsmall'' hblock'')
        have hindex :
            (((m - 1 : ℕ) : ℝ) + (m : ℝ)) ≤ (X : ℝ) := by
          exact_mod_cast (by omega : (m - 1) + m ≤ X)
        have hcoef : 0 ≤ C * φ X := mul_nonneg hC hφX.le
        have hgeom :
            C * (((m - 1 : ℕ) : ℝ) + (m : ℝ)) * φ X ≤
              C * (X : ℝ) * φ X := by
          nlinarith [mul_le_mul_of_nonneg_right hindex hcoef]
        calc
          (∑ n ∈ Finset.Icc 1 X, g n) ≤
              C * ((m - 1 : ℕ) : ℝ) * φ X + C * (m : ℝ) * φ X := hsum'
          _ = C * (((m - 1 : ℕ) : ℝ) + (m : ℝ)) * φ X := by ring
          _ ≤ C * (X : ℝ) * φ X := hgeom

/- Track C's normalized prime-power sum is exactly the cast of the source function `f` divided
by `n`.  This keeps the endpoint-band analysis in `RelaxedBound` independent of the FC target
file while exposing the exact interface needed by the final maximum estimate. -/
theorem f_div_eq_normalizedPrimePowerSum
    {n : ℕ} :
    (f n : ℝ) / (n : ℝ) = normalizedPrimePowerSum n := by
  unfold f normalizedPrimePowerSum normalizedPrimePowerWeight
  rw [Nat.cast_sum, Finset.sum_div]
  simp only [Nat.cast_pow]

/- Direct source-notation form of the report-scale reduction.  The only non-elementary datum is
the explicit tail certificate passed to `normalizedPrimePowerSum_le_report_bound`; once supplied,
the casted `f(n)/n` inequality is immediate. -/
theorem f_div_le_report_bound
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 0 < T) (hv : 0 < v) (hv1 : 1 ≤ v)
    (hlogT : Real.log T = v)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hTail :
      ∑ p ∈ Finset.Icc
          (⌊Real.exp (v - 3 * Real.log v)⌋₊ + 1)
          (⌊Real.exp (v + Real.log v)⌋₊),
          normalizedPositiveSurplus n (v + Real.log v) p ≤ 24 * T / v ^ 2)
    (hlogn : Real.log (n : ℝ) = T) :
    (f n : ℝ) / (n : ℝ) ≤
      T / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2 := by
  rw [f_div_eq_normalizedPrimePowerSum]
  have hbound := normalizedPrimePowerSum_le_report_bound hn hT hv hv1 hlogT hA hTail
  simpa [hlogn] using hbound

/- Direct source-level closure from the sharp natural-window certificate.  All floor arithmetic,
positive-fiber support, and the boundary fiber are handled by
`normalized_surplus_tail_sum_le_of_report_sharp_width_certificate`; this wrapper exposes exactly
the resulting bound on `f(n)/n` in the notation of the report. -/
theorem f_div_le_report_bound_of_sharp_width_certificate
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 4 ≤ T) (hv : 0 < v) (hv1 : 1 ≤ v)
    (hlogT : Real.log T = v) (hlogn : Real.log (n : ℝ) = T)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hAhalf : (v + Real.log v) / 2 ≤ v - 3 * Real.log v)
    (hAL : v - 3 * Real.log v ≤ v + Real.log v)
    (hL : 0 < v + Real.log v) (hL2 : 2 ≤ v + Real.log v)
    (hExp : Real.exp (v + Real.log v) ≤ (n : ℝ))
    (hwindow :
      (∑ k ∈ (Finset.range (n + 1)).filter (fun j : ℕ ↦
        0 < j ∧ T ≤ (j : ℝ) * (v + Real.log v) ∧
          (j : ℝ) * (v - 3 * Real.log v) < T),
        ((v + Real.log v) -
            (T / (k : ℝ) -
              4 * ((v + Real.log v) - T / (k : ℝ)) / T)) /
          (v + Real.log v) *
          (Real.exp (T / (k : ℝ)) -
            Real.exp (T / (k : ℝ) -
              4 * ((v + Real.log v) - T / (k : ℝ)) / T) + 1)) ≤
        24 * T / v ^ 2) :
    (f n : ℝ) / (n : ℝ) ≤
      T / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2 := by
  have htail := normalized_surplus_tail_sum_le_of_report_sharp_width_certificate
    hn hT hlogn hA hAhalf hAL hL hL2 hExp hwindow
  exact f_div_le_report_bound hn (lt_of_lt_of_le (by norm_num) hT)
    hv hv1 hlogT hA htail hlogn

/- The weighted-geometric finite certificate exposes the remaining Track-C task as one scalar
inequality.  All floor/support bookkeeping is supplied by the report adapter; the caller only
has to prove that the explicit weighted bound is at most `24*T/v^2`. -/
theorem f_div_le_report_bound_of_weighted_window_certificate
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 4 ≤ T) (hv : 0 < v) (hv1 : 1 ≤ v)
    (hlogT : Real.log T = v) (hlogn : Real.log (n : ℝ) = T)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hAhalf : (v + Real.log v) / 2 ≤ v - 3 * Real.log v)
    (hAL : v - 3 * Real.log v ≤ v + Real.log v)
    (hL : 0 < v + Real.log v) (hL2 : 2 ≤ v + Real.log v)
    (hExp : Real.exp (v + Real.log v) ≤ (n : ℝ))
    (hscalar :
      16 * Real.exp (v + Real.log v) *
          ((v + Real.log v) /
            (Nat.ceil (T / (v + Real.log v)) : ℝ)) ^ 2 /
            ((v + Real.log v) * T) *
              (1 + T / ((v - 3 * Real.log v) * (v + Real.log v))) ^ 3 +
        2 * ((T / (v - 3 * Real.log v) - T / (v + Real.log v) + 2) *
          (((v + Real.log v) - (v - 3 * Real.log v)) /
            (v + Real.log v))) ≤ 24 * T / v ^ 2) :
    (f n : ℝ) / (n : ℝ) ≤
      T / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2 := by
  let A : ℝ := v - 3 * Real.log v
  let L : ℝ := v + Real.log v
  let K : Finset ℕ := (Finset.range (n + 1)).filter (fun j : ℕ ↦
    0 < j ∧ T ≤ (j : ℝ) * L ∧ (j : ℝ) * A < T)
  have hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hwindowWeighted :
      (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 +
          2 * ((T / A - T / L + 2) * ((L - A) / L)) := by
    dsimp [A, L, K]
    exact report_sharp_width_sum_le_weighted_explicit_window
      hT (lt_of_lt_of_le (by norm_num) hT) (by linarith [hAhalf, hAL])
      hAL hL ((Finset.range (n + 1)).filter (fun j : ℕ ↦
        0 < j ∧ T ≤ (j : ℝ) * (v + Real.log v) ∧
          (j : ℝ) * (v - 3 * Real.log v) < T)) (by
            intro k hk
            exact (Finset.mem_filter.mp hk).2)
  have hwindow :
      (∑ k ∈ K, reportSharpWidthTerm T L k) ≤ 24 * T / v ^ 2 := by
    exact hwindowWeighted.trans (by simpa [A, L] using hscalar)
  apply f_div_le_report_bound_of_sharp_width_certificate hn hT hv hv1 hlogT hlogn
    hA hAhalf hAL hL hL2 hExp
  simpa [A, L, K, reportSharpWidthTerm] using hwindow

/- Endpoint-sharp variant of the weighted certificate.  Its scalar hypothesis keeps the actual
   natural window width `floor (T/A) - ceil (T/L)` in the linear contribution. -/
theorem f_div_le_report_bound_of_tight_weighted_window_certificate
    {n : ℕ} (hn : n ≠ 0) {T v : ℝ}
    (hT : 4 ≤ T) (hv : 0 < v) (hv1 : 1 ≤ v)
    (hlogT : Real.log T = v) (hlogn : Real.log (n : ℝ) = T)
    (hA : Real.log 2 ≤ v - 3 * Real.log v)
    (hAhalf : (v + Real.log v) / 2 ≤ v - 3 * Real.log v)
    (hAL : v - 3 * Real.log v ≤ v + Real.log v)
    (hL : 0 < v + Real.log v) (hL2 : 2 ≤ v + Real.log v)
    (hExp : Real.exp (v + Real.log v) ≤ (n : ℝ))
    (hscalar : tightReportScalar T v ≤ 24 * T / v ^ 2) :
    (f n : ℝ) / (n : ℝ) ≤
      T / (v + Real.log v) + T / v ^ 3 + 24 * T / v ^ 2 := by
  let A : ℝ := v - 3 * Real.log v
  let L : ℝ := v + Real.log v
  let K : Finset ℕ := (Finset.range (n + 1)).filter (fun j : ℕ ↦
    0 < j ∧ T ≤ (j : ℝ) * L ∧ (j : ℝ) * A < T)
  have hK : ∀ k ∈ K, 0 < k ∧ T ≤ (k : ℝ) * L ∧ (k : ℝ) * A < T := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hwindowWeighted :
      (∑ k ∈ K, reportSharpWidthTerm T L k) ≤
        16 * Real.exp L * (L / (Nat.ceil (T / L) : ℝ)) ^ 2 /
            (L * T) * (1 + T / (A * L)) ^ 3 +
          2 * ((((Nat.floor (T / A) - Nat.ceil (T / L) : ℕ) : ℝ) + 1) ^ 2 /
            (Nat.ceil (T / L) : ℝ)) := by
    dsimp [A, L, K]
    exact report_sharp_width_sum_le_weighted_explicit_window_tight
      hT (lt_of_lt_of_le (by norm_num) hT) (by linarith [hAhalf, hAL])
      hAL hL ((Finset.range (n + 1)).filter (fun j : ℕ ↦
        0 < j ∧ T ≤ (j : ℝ) * (v + Real.log v) ∧
          (j : ℝ) * (v - 3 * Real.log v) < T)) (by
            intro k hk
            exact (Finset.mem_filter.mp hk).2)
  have hwindow :
      (∑ k ∈ K, reportSharpWidthTerm T L k) ≤ 24 * T / v ^ 2 := by
    exact hwindowWeighted.trans (by simpa [A, L, tightReportScalar] using hscalar)
  apply f_div_le_report_bound_of_sharp_width_certificate hn hT hv hv1 hlogT hlogn
    hA hAhalf hAL hL hL2 hExp
  simpa [A, L, K, reportSharpWidthTerm] using hwindow

/- The report's side conditions on `A = v - 3 log v` and `L = v + log v` are eventually
elementary.  This lemma discharges those parameter inequalities, so a future tail certificate
need only be supplied on the eventual region; it does not hide any prime-distribution input. -/
theorem eventually_report_parameter_side_conditions :
    ∀ᶠ v : ℝ in atTop,
      1 ≤ v ∧ 0 < v ∧ Real.log 2 ≤ v - 3 * Real.log v ∧
        (v + Real.log v) / 2 ≤ v - 3 * Real.log v ∧
        0 < v + Real.log v := by
  have hratio : Tendsto (fun v : ℝ ↦ Real.log v / v) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall : ∀ᶠ v : ℝ in atTop, Real.log v / v < (1 / 14 : ℝ) :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  filter_upwards [eventually_ge_atTop (14 : ℝ), hsmall] with v hv hratio
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hvlog : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hlogbound : Real.log v < v / 14 := by
    have h := (div_lt_iff₀ hvpos).mp hratio
    nlinarith
  have hA : Real.log 2 ≤ v - 3 * Real.log v := by
    nlinarith
  have hhalf : (v + Real.log v) / 2 ≤ v - 3 * Real.log v := by
    nlinarith
  exact ⟨by linarith, hvpos, hA, hhalf, by linarith⟩

/- Natural-endpoint packaging of the preceding side conditions.  With
`T = log n` and `v = log T`, all positivity and endpoint inequalities hold eventually along the
integer endpoints used by the source problem. -/
theorem eventually_report_parameter_data_on_nat :
    ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) ∧
        0 < Real.log (Real.log (n : ℝ)) ∧
        1 ≤ Real.log (Real.log (n : ℝ)) ∧
        Real.log 2 ≤ Real.log (Real.log (n : ℝ)) -
          3 * Real.log (Real.log (Real.log (n : ℝ))) ∧
        (Real.log (Real.log (n : ℝ)) +
          Real.log (Real.log (Real.log (n : ℝ)))) / 2 ≤
          Real.log (Real.log (n : ℝ)) -
            3 * Real.log (Real.log (Real.log (n : ℝ))) ∧
        0 < Real.log (Real.log (n : ℝ)) +
          Real.log (Real.log (Real.log (n : ℝ))) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hside := hv.eventually eventually_report_parameter_side_conditions
  have hT : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
    hlog.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hside, hT] with n hside hT
  rcases hside with ⟨hv1, hvpos, hA, hhalf, hL⟩
  exact ⟨hT, hvpos, hv1, hA, hhalf, hL⟩

/- The endpoint-sharp scalar certificate now closes the full report-scale upper bound
   eventually on natural endpoints.  No prime-distribution hypothesis is hidden here: the
   preceding finite-window adapter has already isolated that input in the source tail estimate. -/
theorem eventually_f_div_le_report_bound_of_tight_scalar :
    ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) / (n : ℝ) ≤
        Real.log (n : ℝ) /
            (Real.log (Real.log (n : ℝ)) +
              Real.log (Real.log (Real.log (n : ℝ)))) +
          Real.log (n : ℝ) / (Real.log (Real.log (n : ℝ))) ^ 3 +
          24 * Real.log (n : ℝ) /
            (Real.log (Real.log (n : ℝ))) ^ 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hTlarge : ∀ᶠ n : ℕ in atTop,
      4 ≤ Real.log (n : ℝ) :=
    hlog.eventually (eventually_ge_atTop (4 : ℝ))
  have hv2 : ∀ᶠ n : ℕ in atTop,
      2 ≤ Real.log (Real.log (n : ℝ)) :=
    hv.eventually (eventually_ge_atTop (2 : ℝ))
  have hdata := eventually_report_parameter_data_on_nat
  have hscalar := eventually_tight_report_scalar_bound_on_nat
  have hexp := eventually_report_endpoint_exp_le_nat
  filter_upwards [hTlarge, hv2, hdata, hscalar, hexp] with n hT hV2 hside hscalar hexp
  rcases hside with ⟨hTpos, hvpos, hv1, hA, hhalf, hL⟩
  have hn1 : 1 < n := by
    have hlogpos : 0 < Real.log (n : ℝ) := hTpos
    have hreal : (1 : ℝ) < (n : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp hlogpos
    exact_mod_cast hreal
  have hn0 : n ≠ 0 := by omega
  have hlogloglognonneg : 0 ≤ Real.log (Real.log (Real.log (n : ℝ))) :=
    Real.log_nonneg hv1
  have hAL : Real.log (Real.log (n : ℝ)) -
      3 * Real.log (Real.log (Real.log (n : ℝ))) ≤
      Real.log (Real.log (n : ℝ)) +
        Real.log (Real.log (Real.log (n : ℝ))) := by
    nlinarith [hlogloglognonneg]
  have hL2 : 2 ≤ Real.log (Real.log (n : ℝ)) +
      Real.log (Real.log (Real.log (n : ℝ))) := by
    nlinarith [hlogloglognonneg]
  exact f_div_le_report_bound_of_tight_weighted_window_certificate
    hn0 hT hvpos hv1 rfl rfl hA hhalf hAL hL hL2 hexp hscalar

/- A finite denominator estimate for one source summand.  If `k = floor(log_p n)` and
   `q = n / p^k`, then `q p^k ≤ n`; hence the normalized prime-power contribution is at most
   `1/q`.  Unlike the tempting exact-cofactor shortcut, this remains valid even when `p^k` does
   not divide `n` (for example `n = 6, p = 2`).  This is the elementary kernel for a future
   summatory H(X) estimate. -/
theorem normalizedPrimePowerWeight_le_reciprocal_floor_quotient
    {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    ((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ) ≤
      (((n / p ^ Nat.log p n : ℕ) : ℝ)⁻¹) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    (Nat.dvd_of_mem_primeFactors hp)
  have hlogpos : 0 < Nat.log p n := Nat.log_pos hpp.one_lt hple
  have hpowle : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hn
  have hpowpos : 0 < p ^ Nat.log p n := pow_pos hpp.pos _
  have hqpos : 0 < n / p ^ Nat.log p n := Nat.div_pos hpowle hpowpos
  have hqmul : (n / p ^ Nat.log p n) * p ^ Nat.log p n ≤ n :=
    Nat.div_mul_le_self n (p ^ Nat.log p n)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hqreal : 0 < ((n / p ^ Nat.log p n : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hqmulR :
      ((n / p ^ Nat.log p n : ℕ) : ℝ) *
          ((p ^ Nat.log p n : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hqmul
  have hprod :
      (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) *
          ((n / p ^ Nat.log p n : ℕ) : ℝ) ≤ 1 := by
    calc
      (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) *
          ((n / p ^ Nat.log p n : ℕ) : ℝ) =
          (((n / p ^ Nat.log p n : ℕ) : ℝ) *
            ((p ^ Nat.log p n : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ 1 := (div_le_iff₀ hnreal).2 (by simpa using hqmulR)
  have hquot :
      ((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ) ≤
        1 / ((n / p ^ Nat.log p n : ℕ) : ℝ) := by
    apply (le_div_iff₀ hqreal).2
    simpa [mul_comm] using hprod
  simpa [one_div] using hquot

/- Summing the preceding pointwise estimate gives a denominator-side majorant for `f(n)/n`.
   The quotient is a floor quotient, not an asserted divisor, so this lemma is safe for every
   prime divisor and is suitable for later finite reindexing by `(p, floor(log_p n), q)`. -/
theorem f_div_le_sum_reciprocal_floor_quotient
    {n : ℕ} (hn : n ≠ 0) :
    (f n : ℝ) / (n : ℝ) ≤
      ∑ p ∈ n.primeFactors,
        (((n / p ^ Nat.log p n : ℕ) : ℝ)⁻¹) := by
  unfold f
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  exact normalizedPrimePowerWeight_le_reciprocal_floor_quotient hn hp

/- Summatory packaging of the floor-quotient majorant.  This is the exact finite reduction of
   the H(X) problem: the remaining analytic task is to reindex or estimate the displayed double
   sum, while no divisibility of `p ^ floor(log_p n)` is being assumed. -/
theorem summatory_f_div_le_sum_reciprocal_floor_quotient (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 X,
        ∑ p ∈ n.primeFactors,
          (((n / p ^ Nat.log p n : ℕ) : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro n hn
  exact f_div_le_sum_reciprocal_floor_quotient (by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)

/- A finite harmonic estimate for the basic block which appears after fixing a prime and a
   logarithmic exponent.  It is deliberately stated without any reindexing assumptions: each
   denominator is the actual product `p*m`, and the comparison is termwise with the harmonic sum.
   Later floor-quotient arguments can therefore use this as a stable quantitative primitive. -/
theorem sum_inv_mul_le_harmonic (p B : ℕ) (hp : 0 < p) :
    (∑ m ∈ Finset.Icc 1 B, (((p * m : ℕ) : ℝ)⁻¹)) ≤ (harmonic B : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  rw [Nat.cast_mul]
  apply (inv_le_inv₀ (mul_pos hpR hmR) hmR).2
  nlinarith [show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))]

/- The logarithmic form is the version used in asymptotic bookkeeping.  It is just the standard
   harmonic-number upper bound, but exposing it here avoids repeatedly transporting the rational
   harmonic number through casts in later H(X) estimates. -/
theorem sum_inv_mul_le_one_add_log (p B : ℕ) (hp : 0 < p) :
    (∑ m ∈ Finset.Icc 1 B, (((p * m : ℕ) : ℝ)⁻¹)) ≤
      1 + Real.log (B : ℝ) := by
  exact (sum_inv_mul_le_harmonic p B hp).trans (by
    simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (harmonic_le_one_add_log B))

/- A quotient fibre has at most `d` elements.  The remainder map is injective on a fixed
   quotient fibre, by the Euclidean division identity.  This avoids trying to choose a canonical
   inverse for the floor quotient and is robust at the endpoint `X`. -/
theorem card_filter_div_eq_le (X d q : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun n ↦ n / d = q)).card ≤ d := by
  let S : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ n / d = q)
  have hmap : Set.MapsTo (fun n : ℕ ↦ n % d) (S : Set ℕ) (Finset.range d : Set ℕ) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.mod_lt n hd)
  have hinj : (S : Set ℕ).InjOn (fun n : ℕ ↦ n % d) := by
    intro n₁ hn₁ n₂ hn₂ hmod
    have hq₁ : n₁ / d = q := (Finset.mem_filter.mp hn₁).2
    have hq₂ : n₂ / d = q := (Finset.mem_filter.mp hn₂).2
    change n₁ % d = n₂ % d at hmod
    calc
      n₁ = n₁ / d * d + n₁ % d := (Nat.div_add_mod' n₁ d).symm
      _ = n₂ / d * d + n₂ % d := by rw [hq₁, hq₂, hmod]
      _ = n₂ := Nat.div_add_mod' n₂ d
  have hcard := Finset.card_le_card_of_injOn (fun n : ℕ ↦ n % d) hmap hinj
  simpa [S] using hcard

/- Weighted form of the preceding fibre estimate.  On the fibre the quotient is constant, so the
   sum collapses to `card * q⁻¹`; the nonnegativity of the reciprocal then allows multiplication by
   the cardinality bound. -/
theorem sum_inv_div_filter_le (X d q : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ n / d = q),
      (((n / d : ℕ) : ℝ)⁻¹)) ≤
      (d : ℝ) * ((q : ℕ) : ℝ)⁻¹ := by
  let S : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ n / d = q)
  have hsum :
      (∑ n ∈ S, (((n / d : ℕ) : ℝ)⁻¹)) =
        (S.card : ℝ) * ((q : ℕ) : ℝ)⁻¹ := by
    calc
      (∑ n ∈ S, (((n / d : ℕ) : ℝ)⁻¹)) =
          ∑ _n ∈ S, ((q : ℕ) : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [(Finset.mem_filter.mp hn).2]
      _ = (S.card : ℝ) * ((q : ℕ) : ℝ)⁻¹ := by simp [mul_comm]
  rw [show (Finset.Icc 1 X).filter (fun n ↦ n / d = q) = S from rfl, hsum]
  have hcard : S.card ≤ d := by
    exact card_filter_div_eq_le X d q hd
  have hqnonneg : 0 ≤ ((q : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hqnonneg

/- Summing the fibres recovers a global quotient estimate.  The zero quotient fibre contributes
   exactly zero, while all positive quotients lie in `Icc 1 (X / d)`; the standard fiberwise sum
   lemma then reduces the whole expression to a harmonic block. -/
theorem sum_inv_div_le_mul_harmonic (X d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 X, (((n / d : ℕ) : ℝ)⁻¹)) ≤
      (d : ℝ) * (harmonic (X / d) : ℝ) := by
  let S : Finset ℕ := Finset.Icc 1 X
  let T : Finset ℕ := Finset.Icc 1 (X / d)
  have hoff : ∀ y ∉ T,
      (∑ n ∈ S with n / d = y, (((n / d : ℕ) : ℝ)⁻¹)) ≤ 0 := by
    intro y hy
    by_cases hy0 : y = 0
    · apply le_of_eq
      apply Finset.sum_eq_zero
      intro n hn
      have hq : n / d = y := (Finset.mem_filter.mp hn).2
      simp [hy0, hq]
    · have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
      have hygt : X / d < y := by
        apply Nat.lt_of_not_ge
        intro hle
        exact hy (Finset.mem_Icc.mpr ⟨hy1, hle⟩)
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n hn
      have hS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hq : n / d = y := (Finset.mem_filter.mp hn).2
      have hnX : n ≤ X := (Finset.mem_Icc.mp (show n ∈ Finset.Icc 1 X by simpa [S] using hS)).2
      have hdiv : n / d ≤ X / d := Nat.div_le_div_right hnX
      exfalso
      exact (Nat.not_lt_of_ge hdiv) (hq ▸ hygt)
  have hfiber := Finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos
    (s := S) (t := T) (g := fun n : ℕ ↦ n / d)
    (f := fun n : ℕ ↦ (((n / d : ℕ) : ℝ)⁻¹)) hoff
  have hblock :
      (∑ y ∈ T, ∑ n ∈ S with n / d = y, (((n / d : ℕ) : ℝ)⁻¹)) ≤
        ∑ y ∈ T, (d : ℝ) * ((y : ℕ) : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro y hy
    simpa [S] using (sum_inv_div_filter_le X d y hd)
  calc
    (∑ n ∈ Finset.Icc 1 X, (((n / d : ℕ) : ℝ)⁻¹)) =
        ∑ n ∈ S, (((n / d : ℕ) : ℝ)⁻¹) := by rfl
    _ ≤ ∑ y ∈ T, ∑ n ∈ S with n / d = y, (((n / d : ℕ) : ℝ)⁻¹) := hfiber
    _ ≤ ∑ y ∈ T, (d : ℝ) * ((y : ℕ) : ℝ)⁻¹ := hblock
    _ = (d : ℝ) * (harmonic (X / d) : ℝ) := by
      rw [← Finset.mul_sum]
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rfl

theorem sum_inv_div_le_mul_one_add_log (X d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 X, (((n / d : ℕ) : ℝ)⁻¹)) ≤
      (d : ℝ) * (1 + Real.log (X / d : ℕ)) := by
  exact (sum_inv_div_le_mul_harmonic X d hd).trans (by
    have hdR : 0 ≤ (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by
      simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
        (harmonic_le_one_add_log (X / d))) hdR)

/- A single `Nat.log` block is contained in the interval ending just before the next power.
   Combining this elementary block containment with the global fibre estimate gives a clean finite
   bound for the contribution of one exponent `k`. -/
theorem sum_inv_div_on_natLog_block_le (X p k : ℕ) (hp : 1 < p) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
      ((p ^ k : ℕ) : ℝ) *
        (harmonic ((p ^ (k + 1) - 1) / p ^ k) : ℝ) := by
  let S : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k)
  let U : Finset ℕ := Finset.Icc 1 (p ^ (k + 1) - 1)
  have hsub : S ⊆ U := by
    intro n hn
    have hS : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hn).1
    have hlog : Nat.log p n = k := (Finset.mem_filter.mp hn).2
    have hupper : n < p ^ (k + 1) := by
      have h := Nat.lt_pow_succ_log_self hp n
      simpa [hlog, Nat.succ_eq_add_one] using h
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hS).1, Nat.le_sub_one_of_lt hupper⟩
  have hsumle :
      (∑ n ∈ S, (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
        ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    positivity
  have hglobal := sum_inv_div_le_mul_harmonic
    (p ^ (k + 1) - 1) (p ^ k) (Nat.pow_pos (Nat.zero_lt_of_lt hp))
  calc
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k),
        (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
        ∑ n ∈ S, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by rfl
    _ ≤ ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := hsumle
    _ ≤ ((p ^ k : ℕ) : ℝ) *
        (harmonic ((p ^ (k + 1) - 1) / p ^ k) : ℝ) := by
      simpa [U] using hglobal

/- Cutoff-sensitive version of the preceding block estimate. The upper endpoint is the actual
   cutoff `X` intersected with the logarithmic block, so a final partial block is not charged as
   if it extended all the way to `p^(k+1)`. -/
theorem sum_inv_div_on_natLog_block_le_cutoff (X p k : ℕ) (hp : 1 < p) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
      ((p ^ k : ℕ) : ℝ) *
        (harmonic ((min X (p ^ (k + 1) - 1)) / p ^ k) : ℝ) := by
  let S : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k)
  let Y : ℕ := min X (p ^ (k + 1) - 1)
  let U : Finset ℕ := Finset.Icc 1 Y
  have hsub : S ⊆ U := by
    intro n hn
    have hS : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hn).1
    have hlog : Nat.log p n = k := (Finset.mem_filter.mp hn).2
    have hupper : n < p ^ (k + 1) := by
      have h := Nat.lt_pow_succ_log_self hp n
      simpa [hlog, Nat.succ_eq_add_one] using h
    apply Finset.mem_Icc.mpr
    refine ⟨(Finset.mem_Icc.mp hS).1, ?_⟩
    exact (Nat.le_min).2 ⟨(Finset.mem_Icc.mp hS).2, Nat.le_sub_one_of_lt hupper⟩
  have hsumle :
      (∑ n ∈ S, (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
        ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    positivity
  have hglobal := sum_inv_div_le_mul_harmonic Y (p ^ k)
    (Nat.pow_pos (Nat.zero_lt_of_lt hp))
  calc
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k),
        (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
        ∑ n ∈ S, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by rfl
    _ ≤ ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := hsumle
    _ ≤ ((p ^ k : ℕ) : ℝ) *
        (harmonic ((min X (p ^ (k + 1) - 1)) / p ^ k) : ℝ) := by
      simpa [U, Y] using hglobal

/- The endpoint of a power block has the expected quotient exactly.  Keeping this arithmetic fact
   separate makes the later block sum read `p^k · H_(p-1)` rather than carrying a floor quotient. -/
theorem pow_succ_sub_one_div_pow_eq_sub_one (p k : ℕ) (hp : 1 < p) :
    (p ^ (k + 1) - 1) / p ^ k = p - 1 := by
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hpowpos : 0 < p ^ k := Nat.pow_pos hp0
  have hpowone : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpowpos)
  have hpone : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp0)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.pow_succ]
    calc
      (p - 1) * p ^ k = p * p ^ k - p ^ k := by
        rw [Nat.sub_mul]
        simp
      _ ≤ p * p ^ k - 1 := Nat.sub_le_sub_left hpowone _
      _ = p ^ k * p - 1 := by simp [Nat.mul_comm]
  · rw [Nat.pow_succ]
    have hprod : 0 < p ^ k * p := Nat.mul_pos hpowpos hp0
    have hlt : p ^ k * p - 1 < p ^ k * p := Nat.sub_lt hprod Nat.zero_lt_one
    simpa [Nat.sub_add_cancel hpone, Nat.mul_comm] using hlt

theorem sum_inv_div_on_natLog_block_le_harmonic_sub_one (X p k : ℕ) (hp : 1 < p) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
      ((p ^ k : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
  simpa [pow_succ_sub_one_div_pow_eq_sub_one p k hp] using
    (sum_inv_div_on_natLog_block_le X p k hp)

/- Exact reindexing of a finite sum over positive multiples.  This is the bridge needed to exploit
   the extra condition `p ∣ n` in the definition of `f`: after writing `n = p*m`, the relevant
   floor quotient becomes a quotient in the smaller variable `m`. -/
theorem sum_filter_dvd_eq_sum_mul (X p : ℕ) (hp : 0 < p) (g : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ p ∣ n), g n) =
      ∑ m ∈ Finset.Icc 1 (X / p), g (p * m) := by
  let S : Finset ℕ := Finset.Icc 1 (X / p)
  let T : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ p ∣ n)
  symm
  apply Finset.sum_bij (fun m _ ↦ p * m)
  · intro m hm
    have hmI : m ∈ Finset.Icc 1 (X / p) := by simpa [S] using hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, dvd_mul_right p m⟩
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_Icc.mp hmI).1.trans (Nat.le_mul_of_pos_left m hp)
    · calc
        p * m = m * p := Nat.mul_comm _ _
        _ ≤ X := Nat.mul_le_of_le_div p m X (Finset.mem_Icc.mp hmI).2
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    have hnI : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hn).1
    have hdiv : p ∣ n := (Finset.mem_filter.mp hn).2
    obtain ⟨m, hm⟩ := hdiv
    refine ⟨m, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
        by_contra hm0
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos (by simpa using hm0)
        subst m
        exact (Nat.ne_of_gt hnpos) (by simpa using hm)
      · apply (Nat.le_div_iff_mul_le hp).2
        simpa [hm, Nat.mul_comm] using (Finset.mem_Icc.mp hnI).2
    · simp [hm]
  · intro m hm
    rfl

/- The multiples of `p` in `[1,Y]` inject into `[1,⌊Y/p⌋]` by Euclidean division.
   This cardinality form is the finite counting input behind the factor `2X/p` in Erdős's
   dyadic estimate (21). -/
theorem card_filter_dvd_Icc_le_div (Y p : ℕ) (hp : 0 < p) :
    ((Finset.Icc 1 Y).filter (fun n ↦ p ∣ n)).card ≤ Y / p := by
  let S : Finset ℕ := (Finset.Icc 1 Y).filter (fun n ↦ p ∣ n)
  let T : Finset ℕ := Finset.Icc 1 (Y / p)
  have hmap : Set.MapsTo (fun n : ℕ ↦ n / p) (S : Set ℕ) (T : Set ℕ) := by
    intro n hn
    have hnS : n ∈ S := by simpa [S] using hn
    have hnI := (Finset.mem_filter.mp hnS).1
    have hdvd := (Finset.mem_filter.mp hnS).2
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hn0 : n ≠ 0 := by omega
    have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hqpos : 0 < n / p := Nat.div_pos hp_le hp
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos),
      Nat.div_le_div_right (Finset.mem_Icc.mp hnI).2⟩
  have hinj : (S : Set ℕ).InjOn (fun n : ℕ ↦ n / p) := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hn₁S : n₁ ∈ S := hn₁
    have hn₂S : n₂ ∈ S := hn₂
    have hd₁ : p ∣ n₁ := (Finset.mem_filter.mp hn₁S).2
    have hd₂ : p ∣ n₂ := (Finset.mem_filter.mp hn₂S).2
    change n₁ / p = n₂ / p at heq
    calc
      n₁ = p * (n₁ / p) := (Nat.mul_div_cancel' hd₁).symm
      _ = p * (n₂ / p) := by rw [heq]
      _ = n₂ := Nat.mul_div_cancel' hd₂
  have hcard := Finset.card_le_card_of_injOn (fun n : ℕ ↦ n / p) hmap hinj
  simpa [S, T] using hcard

/- The pointwise endpoint comparison used in the dyadic summation: on `X ≤ n ≤ 2X`, the
   prime-power exponent is monotone in `n`, while the denominator is bounded below by `X`. -/
theorem primePowerWeight_le_dyadic_endpoint
    {X n p : ℕ} (hX : 0 < X)
    (hn : n ∈ Finset.Icc X (2 * X)) (hp : p ∈ n.primeFactors) :
    ((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ) ≤
      ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hlog : Nat.log p n ≤ Nat.log p (2 * X) :=
    Nat.log_mono_right (Finset.mem_Icc.mp hn).2
  have hpow : p ^ Nat.log p n ≤ p ^ Nat.log p (2 * X) :=
    Nat.pow_le_pow_right hpp.pos hlog
  have hpowR : ((p ^ Nat.log p n : ℕ) : ℝ) ≤
      ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) := by exact_mod_cast hpow
  have hnR : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hnumR : 0 ≤ ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) := by positivity
  exact div_le_div₀ hnumR hpowR hXR hnR

/- Predicate-preserving version of the multiple reindexing lemma.  It is used for the
   `Nat.log` blocks, where the block condition must travel through the substitution `n=p*m`. -/
theorem sum_filter_dvd_and_pred_eq_sum_mul
    (X p : ℕ) (hp : 0 < p) (P : ℕ → Prop) [DecidablePred P] (g : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ P n), g n) =
      ∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)), g (p * m) := by
  let S : Finset ℕ := (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m))
  let T : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦ p ∣ n ∧ P n)
  symm
  apply Finset.sum_bij (fun m _ ↦ p * m)
  · intro m hm
    have hmS : m ∈ S := by simpa [S] using hm
    have hmI : m ∈ Finset.Icc 1 (X / p) := (Finset.mem_filter.mp hmS).1
    have hmP : P (p * m) := (Finset.mem_filter.mp hmS).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, ?_⟩
    · refine ⟨(Finset.mem_Icc.mp hmI).1.trans (Nat.le_mul_of_pos_left m hp), ?_⟩
      calc
        p * m = m * p := Nat.mul_comm _ _
        _ ≤ X := Nat.mul_le_of_le_div p m X (Finset.mem_Icc.mp hmI).2
    exact ⟨dvd_mul_right p m, hmP⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    have hnI : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hn).1
    have hnP : P n := (Finset.mem_filter.mp hn).2.2
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hn).2.1
    refine ⟨m, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        constructor
        · have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
          have hmpos : 0 < m := by
            by_contra hm0
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos (by simpa using hm0)
            subst m
            exact (Nat.ne_of_gt hnpos) (by simpa using hm)
          exact hmpos
        · apply (Nat.le_div_iff_mul_le hp).2
          simpa [hm, Nat.mul_comm] using (Finset.mem_Icc.mp hnI).2
      · simpa [hm] using hnP
    · simp [hm]
  · intro m hm
    rfl

/- Applying the predicate-preserving reindexing to a `Nat.log` block removes the leading prime
   factor exactly: `log_p (p*m) = log_p m + 1`.  Together with cancellation in natural division,
   this transfers the prime-divisible block at exponent `k` to the preceding block at exponent
   `k-1`. -/
theorem sum_inv_div_on_prime_natLog_block_le
    (X p k : ℕ) (hp : 1 < p) (hk : 1 ≤ k) :
    (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n ↦ p ∣ n ∧ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
      ((p ^ (k - 1) : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
  classical
  let P : ℕ → Prop := fun n ↦ Nat.log p n = k
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hreindex := sum_filter_dvd_and_pred_eq_sum_mul X p hp0 P
    (fun n ↦ (((n / p ^ k : ℕ) : ℝ)⁻¹))
  have hfilter :
      (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)) =
        (Finset.Icc 1 (X / p)).filter (fun m ↦ Nat.log p m = k - 1) := by
    ext m
    by_cases hmI : m ∈ Finset.Icc 1 (X / p)
    · have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hlog : Nat.log p (p * m) = Nat.log p m + 1 := by
        simpa [Nat.mul_comm] using (Nat.log_mul_base hp (Nat.ne_of_gt hmpos))
      simp only [Finset.mem_filter, hmI, true_and, P]
      rw [hlog]
      constructor <;> intro h <;> omega
    · simp only [Finset.mem_filter, hmI, false_and]
  have hpow : p ^ k = p * p ^ (k - 1) := by
    calc
      p ^ k = p ^ (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
      _ = p ^ (k - 1) * p := Nat.pow_succ _ _
      _ = p * p ^ (k - 1) := by ac_rfl
  have hden : ∀ m ∈ Finset.Icc 1 (X / p),
      (p * m) / p ^ k = m / p ^ (k - 1) := by
    intro m hm
    rw [hpow]
    exact Nat.mul_div_mul_left m (p ^ (k - 1)) hp0
  have hsum :
      (∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)),
        (((p * m) / p ^ k : ℕ) : ℝ)⁻¹) =
        ∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ Nat.log p m = k - 1),
          (((m / p ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    exact_mod_cast hden m (Finset.mem_filter.mp hm).1
  calc
    (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n ↦ p ∣ n ∧ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
        ∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)),
          (((p * m) / p ^ k : ℕ) : ℝ)⁻¹ := by
      simpa [P] using hreindex
    _ = ∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ Nat.log p m = k - 1),
          (((m / p ^ (k - 1) : ℕ) : ℝ)⁻¹) := hsum
    _ ≤ ((p ^ (k - 1) : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) :=
      sum_inv_div_on_natLog_block_le_harmonic_sub_one (X / p) p (k - 1) hp

/- Divisor-aware cutoff version. After the exact substitution `n=p*m`, the exponent drops to
   `k-1` and the smaller cutoff `X/p` is retained in the endpoint. -/
theorem sum_inv_div_on_prime_natLog_block_le_cutoff
    (X p k : ℕ) (hp : 1 < p) (hk : 1 ≤ k) :
    (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n ↦ p ∣ n ∧ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) ≤
      ((p ^ (k - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / p) (p ^ k - 1)) / p ^ (k - 1) : ℕ) : ℝ) := by
  classical
  let P : ℕ → Prop := fun n ↦ Nat.log p n = k
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hreindex := sum_filter_dvd_and_pred_eq_sum_mul X p hp0 P
    (fun n ↦ (((n / p ^ k : ℕ) : ℝ)⁻¹))
  have hfilter :
      (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)) =
        (Finset.Icc 1 (X / p)).filter (fun m ↦ Nat.log p m = k - 1) := by
    ext m
    by_cases hmI : m ∈ Finset.Icc 1 (X / p)
    · have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hlog : Nat.log p (p * m) = Nat.log p m + 1 := by
        simpa [Nat.mul_comm] using Nat.log_mul_base hp (Nat.ne_of_gt hmpos)
      simp only [Finset.mem_filter, hmI, true_and, P]
      rw [hlog]
      constructor <;> intro h <;> omega
    · simp only [Finset.mem_filter, hmI, false_and]
  have hpow : p ^ k = p * p ^ (k - 1) := by
    calc
      p ^ k = p ^ (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
      _ = p ^ (k - 1) * p := Nat.pow_succ _ _
      _ = p * p ^ (k - 1) := by ac_rfl
  have hden : ∀ m ∈ Finset.Icc 1 (X / p),
      (p * m) / p ^ k = m / p ^ (k - 1) := by
    intro m hm
    rw [hpow]
    exact Nat.mul_div_mul_left m (p ^ (k - 1)) hp0
  have hsum :
      (∑ n ∈ (Finset.Icc 1 X).filter
          (fun n ↦ p ∣ n ∧ Nat.log p n = k),
        (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
        ∑ m ∈ (Finset.Icc 1 (X / p)).filter
          (fun m ↦ Nat.log p m = k - 1),
          (((m / p ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
    calc
      (∑ n ∈ (Finset.Icc 1 X).filter
          (fun n ↦ p ∣ n ∧ Nat.log p n = k),
        (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
          ∑ m ∈ (Finset.Icc 1 (X / p)).filter (fun m ↦ P (p * m)),
            (((p * m) / p ^ k : ℕ) : ℝ)⁻¹ := by
        simpa [P] using hreindex
      _ = ∑ m ∈ (Finset.Icc 1 (X / p)).filter
            (fun m ↦ Nat.log p m = k - 1),
            (((m / p ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
        rw [hfilter]
        apply Finset.sum_congr rfl
        intro m hm
        congr 1
        exact_mod_cast hden m (Finset.mem_filter.mp hm).1
  calc
    (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n ↦ p ∣ n ∧ Nat.log p n = k),
      (((n / p ^ k : ℕ) : ℝ)⁻¹)) =
        ∑ m ∈ (Finset.Icc 1 (X / p)).filter
          (fun m ↦ Nat.log p m = k - 1),
          (((m / p ^ (k - 1) : ℕ) : ℝ)⁻¹) := hsum
    _ ≤ ((p ^ (k - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / p) (p ^ k - 1)) / p ^ (k - 1) : ℕ) : ℝ) := by
      simpa [Nat.sub_add_cancel hk] using
        (sum_inv_div_on_natLog_block_le_cutoff (X / p) p (k - 1) hp)

/- Pair-indexed form of the summatory function.  The sigma finset records exactly one pair
   `(n,p)` for each `p ∈ n.primeFactors`; this is the finite combinatorial starting point for a
   subsequent `(p,k)` fibre decomposition. -/
theorem summatory_f_div_eq_sum_primeFactor_pairs (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) =
      ∑ z ∈ (Finset.Icc 1 X).sigma (fun n ↦ n.primeFactors),
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 X, normalizedPrimePowerSum n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact f_div_eq_normalizedPrimePowerSum
    _ = ∑ n ∈ Finset.Icc 1 X,
        ∑ p ∈ n.primeFactors,
          (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
      simp [normalizedPrimePowerSum, normalizedPrimePowerWeight]
    _ = ∑ z ∈ (Finset.Icc 1 X).sigma (fun n ↦ n.primeFactors),
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
      rw [Finset.sum_sigma']

/- Finite source-aligned form of equation (21) in the 1984 paper.  It is unconditional and only
   uses the elementary fact that the multiples of `p` in `[1,2X]` inject into `[1,⌊2X/p⌋]`.
   The later estimates (22) and (27) are the genuinely analytic inputs needed to turn this
   endpoint sum into the stated `H(X) ≪ X log log log X` bound. -/
theorem summatory_f_div_Icc_le_two_mul_prime_power_weight
    (X : ℕ) (hX : 0 < X) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
      ∑ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime,
        (2 : ℝ) * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) := by
  let S : Finset ((_ : ℕ) × ℕ) :=
    (Finset.Icc X (2 * X)).sigma (fun n : ℕ ↦ n.primeFactors)
  let P : Finset ℕ := (Finset.Icc 2 (2 * X)).filter Nat.Prime
  have hpair :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) =
        ∑ z ∈ S, (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
    calc
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) =
          ∑ n ∈ Finset.Icc X (2 * X), normalizedPrimePowerSum n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact f_div_eq_normalizedPrimePowerSum
      _ = ∑ n ∈ Finset.Icc X (2 * X),
          ∑ p ∈ n.primeFactors,
            (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
        simp [normalizedPrimePowerSum, normalizedPrimePowerWeight]
      _ = ∑ z ∈ S,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
        rw [Finset.sum_sigma']
  have hmaps : ∀ z ∈ S, z.2 ∈ P := by
    intro z hz
    have hz' := Finset.mem_sigma.mp (show z ∈
      (Finset.Icc X (2 * X)).sigma (fun n : ℕ ↦ n.primeFactors) by simpa [S] using hz)
    have hp : z.2.Prime := Nat.prime_of_mem_primeFactors hz'.2
    have hnupper : z.1 ≤ 2 * X := (Finset.mem_Icc.mp hz'.1).2
    have hzpos : 0 < z.1 := lt_of_lt_of_le hX (Finset.mem_Icc.mp hz'.1).1
    have hple : z.2 ≤ z.1 := Nat.le_of_dvd hzpos
      (Nat.dvd_of_mem_primeFactors hz'.2)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple.trans hnupper⟩, hp⟩
  have hdecomp :
      (∑ z ∈ S,
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
      ∑ p ∈ P, ∑ z ∈ S with z.2 = p,
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun z ↦
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)))
  have hfiber : ∀ p ∈ P,
      (∑ z ∈ S with z.2 = p,
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) ≤
      (2 : ℝ) * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) := by
    intro p hpP
    let U : Finset ((_ : ℕ) × ℕ) := S.filter (fun z ↦ z.2 = p)
    let V : Finset ℕ := (Finset.Icc X (2 * X)).filter (fun n ↦ p ∣ n)
    let W : Finset ℕ := (Finset.Icc 1 (2 * X)).filter (fun n ↦ p ∣ n)
    have hUeq :
        (∑ z ∈ S with z.2 = p,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
        ∑ n ∈ V, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
      change (∑ z ∈ U,
        (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
          ∑ n ∈ V, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ))
      apply Finset.sum_bij (fun z _ ↦ z.1)
      · intro z hz
        have hzU : z ∈ U := hz
        have hzS := (Finset.mem_filter.mp hzU).1
        have hzsig := Finset.mem_sigma.mp (show z ∈
          (Finset.Icc X (2 * X)).sigma (fun n : ℕ ↦ n.primeFactors) by
            simpa [S] using hzS)
        have hzp : z.2 = p := (Finset.mem_filter.mp hzU).2
        apply Finset.mem_filter.mpr
        exact ⟨hzsig.1, by simpa [hzp] using Nat.dvd_of_mem_primeFactors hzsig.2⟩
      · intro z₁ hz₁ z₂ hz₂ heq
        have hz₁U : z₁ ∈ U := hz₁
        have hz₂U : z₂ ∈ U := hz₂
        have h1 : z₁.2 = p := (Finset.mem_filter.mp hz₁U).2
        have h2 : z₂.2 = p := (Finset.mem_filter.mp hz₂U).2
        cases z₁ with
        | mk n₁ q₁ =>
          cases z₂ with
          | mk n₂ q₂ =>
            simp only at heq h1 h2 ⊢
            subst n₂
            subst q₁
            subst q₂
            rfl
      · intro n hn
        have hnV : n ∈ V := by simpa [V] using hn
        have hnI := (Finset.mem_filter.mp hnV).1
        have hdiv := (Finset.mem_filter.mp hnV).2
        refine ⟨⟨n, p⟩, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        apply Finset.mem_sigma.mpr
        refine ⟨hnI, ?_⟩
        exact Nat.mem_primeFactors.mpr ⟨by
          have hpPrime : p.Prime := (Finset.mem_filter.mp hpP).2
          exact hpPrime, hdiv, by
            exact Nat.ne_of_gt (lt_of_lt_of_le hX (Finset.mem_Icc.mp hnI).1)⟩
      · intro z hz
        have hzU : z ∈ U := hz
        have hzp : z.2 = p := (Finset.mem_filter.mp hzU).2
        simp [hzp]
    have hVsub : V ⊆ W := by
      intro n hn
      have hnV : n ∈ V := by simpa [V] using hn
      have hnI := (Finset.mem_filter.mp hnV).1
      have hdiv := (Finset.mem_filter.mp hnV).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hX.trans_le (Finset.mem_Icc.mp hnI).1, (Finset.mem_Icc.mp hnI).2⟩, hdiv⟩
    have hpoint : ∀ n ∈ V,
        (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) ≤
          ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ) := by
      intro n hn
      have hnV : n ∈ V := hn
      have hnI := (Finset.mem_filter.mp hnV).1
      have hdiv := (Finset.mem_filter.mp hnV).2
      have hpPrime : p.Prime := (Finset.mem_filter.mp hpP).2
      have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpPrime, hdiv, by
        exact Nat.ne_of_gt (lt_of_lt_of_le hX (Finset.mem_Icc.mp hnI).1)⟩
      exact primePowerWeight_le_dyadic_endpoint hX hnI hpmem
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hpPos : 0 < p := hpPrime.pos
    have hcardVW : V.card ≤ W.card := Finset.card_le_card hVsub
    have hcardW : W.card ≤ (2 * X) / p := by
      simpa [W] using card_filter_dvd_Icc_le_div (2 * X) p hpPos
    have hcard : V.card ≤ (2 * X) / p := hcardVW.trans hcardW
    have hcardR : (V.card : ℝ) ≤ (((2 * X) / p : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpPos
    have hE_nonneg : 0 ≤ ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ) := by positivity
    have hsumV :
        (∑ n ∈ V, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ))) ≤
          (V.card : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul V
          (fun n : ℕ ↦ (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)))
          (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) hpoint)
    have hmul₁ :
        (V.card : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) ≤
          (((2 * X) / p : ℕ) : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardR hE_nonneg
    have hdivR : (((2 * X) / p : ℕ) : ℝ) ≤ (2 * X : ℝ) / (p : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_div_le (α := ℝ) (m := 2 * X) (n := p))
    have hmul₂ :
        (((2 * X) / p : ℕ) : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) ≤
          ((2 * X : ℝ) / (p : ℝ)) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hdivR hE_nonneg
    rw [hUeq]
    calc
      (∑ n ∈ V, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ))) ≤
          (V.card : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) := hsumV
      _ ≤ (((2 * X) / p : ℕ) : ℝ) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) := hmul₁
      _ ≤ ((2 * X : ℝ) / (p : ℝ)) *
            (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (X : ℝ)) := hmul₂
      _ = (2 : ℝ) * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) := by
        field_simp
  rw [hpair, hdecomp]
  apply Finset.sum_le_sum
  intro p hpP
  exact hfiber p hpP

/- The endpoint weight used in the source's equation (21).  Naming it explicitly makes the
   subsequent small/large-prime split readable and prevents repeated coercion noise.  For a prime
   `p`, `Nat.log p (2 * X)` is exactly the exponent `α_p(2X)` characterized by the usual floor-log
   inequalities, so this is the source quantity `p^{α_p(2X)}/p`. -/
noncomputable def endpointPrimePowerWeight (X p : ℕ) : ℝ :=
  (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ))

theorem endpointPrimePowerWeight_eq_source_term (X p : ℕ) :
    endpointPrimePowerWeight X p =
      (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) := by
  rfl

/- Public source-aligned wrapper for equation (21).  The factor `2` is the interval-length/counting
   factor coming from multiples of `p` in `[X,2X]`; all genuinely analytic work starts only when
   this finite prime sum is split and estimated. -/
theorem source_eq21_dyadic_endpoint_bound
    (X : ℕ) (hX : 0 < X) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
      ∑ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime,
        (2 : ℝ) * endpointPrimePowerWeight X p := by
  simpa [endpointPrimePowerWeight] using
    (summatory_f_div_Icc_le_two_mul_prime_power_weight X hX)

/- Definitions for the source's subsequent split (23): a prime is called small/large according to
   whether its endpoint prime power is below a chosen integer threshold `Y`.  Using an integer
   threshold keeps this interface entirely finite; the analytic application may instantiate `Y`
   with a floor of `2X / log log X`. -/
noncomputable def dyadicPrimeSet (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 * X)).filter Nat.Prime

noncomputable def dyadicEndpointWeight (X p : ℕ) : ℝ :=
  (2 : ℝ) * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ))

/- The paper's first split is by the prime base itself (`p < (log X)^10`), rather than by the
   endpoint power.  This separate finite set keeps those two notions distinct. -/
noncomputable def dyadicPrimeSmallPrimeSet (X P : ℕ) : Finset ℕ :=
  (dyadicPrimeSet X).filter (fun p ↦ p ≤ P)

noncomputable def dyadicPrimeLargePrimeSet (X P : ℕ) : Finset ℕ :=
  (dyadicPrimeSet X).filter (fun p ↦ P < p)

noncomputable def dyadicPrimeLargeHighPowerSet (X P Y : ℕ) : Finset ℕ :=
  (dyadicPrimeLargePrimeSet X P).filter
    (fun p ↦ Y < p ^ Nat.log p (2 * X))

noncomputable def dyadicPrimeLargeLowPowerSet (X P Y : ℕ) : Finset ℕ :=
  (dyadicPrimeLargePrimeSet X P).filter
    (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y)

noncomputable def dyadicPrimeExponentFiber (X r : ℕ) : Finset ℕ :=
  (dyadicPrimeSet X).filter (fun p ↦ Nat.log p (2 * X) = r)

noncomputable def dyadicPrimeLargeHighPowerExponentFiber
    (X P Y r : ℕ) : Finset ℕ :=
  (dyadicPrimeLargeHighPowerSet X P Y).filter
    (fun p ↦ Nat.log p (2 * X) = r)

noncomputable def sourceExponentInterval (X Y r : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 * X)).filter
    (fun p ↦ p.Prime ∧ Y < p ^ r ∧ p ^ r ≤ 2 * X)

/- Cutoff-preserving version of the source interval.  Keeping `P < p` in the finite set is
   important: dropping it before applying Brun loses the factor `1 / log P` and cannot recover
   equation (27)'s `log log X / log X` scale. -/
noncomputable def sourceExponentLargeInterval (X P Y r : ℕ) : Finset ℕ :=
  (Finset.Icc (P + 1) (2 * X)).filter
    (fun p ↦ p.Prime ∧ Y < p ^ r ∧ p ^ r ≤ 2 * X)

/- A general logarithmic bound for the exponent of a prime power.  This is the elementary core of
   the source's short `r`-range argument: a base above `P` whose `r`-th power is at most `N` has
   `r < log N / log P`. -/
theorem exponent_lt_log_ratio_of_prime_power_le
    (P p N r : ℕ) (hP : 1 < P) (hp : P < p) (hN : 1 < N)
    (hpow : p ^ r ≤ N) :
    (r : ℝ) < Real.log (N : ℝ) / Real.log (P : ℝ) := by
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  by_cases hr0 : r = 0
  · subst r
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    apply (lt_div_iff₀ hlogP).2
    simpa using hlogN
  · have hrpos : 0 < (r : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hr0)
    have hPpos : 0 < (P : ℝ) := by positivity
    have hloglt : Real.log (P : ℝ) < Real.log (p : ℝ) :=
      Real.log_lt_log hPpos (by exact_mod_cast hp)
    have hmul : (r : ℝ) * Real.log (P : ℝ) <
        (r : ℝ) * Real.log (p : ℝ) :=
      mul_lt_mul_of_pos_left hloglt hrpos
    have hpowR : (p : ℝ) ^ r ≤ (N : ℝ) := by
      exact_mod_cast hpow
    have hlogpow : (r : ℝ) * Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
      have hpPos : 0 < (p : ℝ) := by
        exact_mod_cast (show 0 < p by omega)
      have h := Real.log_le_log (pow_pos hpPos _) hpowR
      simpa [Nat.cast_pow, Real.log_pow] using h
    apply (lt_div_iff₀ hlogP).2
    exact hmul.trans_le hlogpow

/- Converse root form of the same logarithmic comparison.  It turns an integer exponent bound
   `r < log N/log P` into the endpoint inequality `P < N^(1/r)`, which is the missing ordering
   hypothesis when the cutoff-preserving Brun interval is used. -/
theorem prime_cutoff_lt_reciprocal_root_of_exponent_lt_log_ratio
    (P N r : ℕ) (hP : 1 < P) (hN : 1 < N) (hr : 0 < r)
    (hratio : (r : ℝ) < Real.log (N : ℝ) / Real.log (P : ℝ)) :
    (P : ℝ) < (N : ℝ) ^ ((r : ℝ)⁻¹) := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP)
  have hlogpow : (r : ℝ) * Real.log (P : ℝ) < Real.log (N : ℝ) :=
    (lt_div_iff₀ hlogP).mp hratio
  have hPpow : (P : ℝ) ^ (r : ℝ) < (N : ℝ) :=
    (Real.rpow_lt_iff_lt_log hPpos hNpos).2 hlogpow
  exact (Real.lt_rpow_inv_iff_of_pos hPpos.le hNpos.le hrR).2 hPpow

theorem prime_cutoff_lt_reciprocal_root_of_nat_range
    (P N Rmax : ℕ) (hP : 1 < P) (hN : 1 < N)
    (hRange : ∀ r ∈ Finset.range Rmax,
      (r : ℝ) < Real.log (N : ℝ) / Real.log (P : ℝ)) :
    ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < (N : ℝ) ^ ((r : ℝ)⁻¹) := by
  intro r hrange hr
  exact prime_cutoff_lt_reciprocal_root_of_exponent_lt_log_ratio
    P N r hP hN hr (hRange r hrange)

/- A source-shaped range corollary.  The paper uses the deliberately loose bound
   `10 log X / log log X`; isolating the real-variable comparison here leaves only the
   eventual lower bound on the base cutoff (`log P ≥ 10 log log X`) to be supplied later. -/
theorem dyadicPrimeLargeHighPower_natLog_lt_ceil_ten_log_div_loglog
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X)
    (hlogX : 0 ≤ Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hPlog : 10 * Real.log (Real.log (X : ℝ)) ≤ Real.log (P : ℝ))
    (hlog2X : Real.log ((2 * X : ℕ) : ℝ) ≤ 10 * Real.log (X : ℝ)) :
    ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) <
        Nat.ceil (10 * Real.log (X : ℝ) /
          Real.log (Real.log (X : ℝ))) := by
  intro p hp
  have hlogP : 0 < Real.log (P : ℝ) := by
    have hten : 0 < 10 * Real.log (Real.log (X : ℝ)) := by positivity
    exact lt_of_lt_of_le hten hPlog
  have hratio0 : Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) ≤
      (10 * Real.log (X : ℝ)) / Real.log (P : ℝ) :=
    div_le_div_of_nonneg_right hlog2X (le_of_lt hlogP)
  have hnum : 0 ≤ 10 * Real.log (X : ℝ) :=
    mul_nonneg (by norm_num) hlogX
  have hden10 : 0 < 10 * Real.log (Real.log (X : ℝ)) := by positivity
  have hratio1 : (10 * Real.log (X : ℝ)) / Real.log (P : ℝ) ≤
      (10 * Real.log (X : ℝ)) /
        (10 * Real.log (Real.log (X : ℝ))) :=
    div_le_div_of_nonneg_left hnum hden10 hPlog
  have hratio2 : (10 * Real.log (X : ℝ)) /
        (10 * Real.log (Real.log (X : ℝ))) ≤
      (10 * Real.log (X : ℝ)) / Real.log (Real.log (X : ℝ)) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    nlinarith [hloglog]
  have hratio : Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) :=
    hratio0.trans (hratio1.trans hratio2)
  have hp' := Finset.mem_filter.mp hp
  have hpLarge := Finset.mem_filter.mp hp'.1
  have hpP : P < p := hpLarge.2
  have hlt := exponent_lt_log_ratio_of_prime_power_le
    P p (2 * X) (Nat.log p (2 * X)) hP
      hpP hX
      (Nat.pow_log_le_self p (by omega))
  exact Nat.lt_ceil.mpr (hlt.trans_le hratio)

/- The weaker cutoff inequality actually needed for the source range.  Requiring only
   `log log X ≤ log P` is robust under the floor in `P = floor ((log X)^10)`, while still
   yielding the paper's deliberately loose `10 log X/log log X` exponent bound. -/
theorem dyadicPrimeLargeHighPower_natLog_lt_ceil_ten_log_div_loglog_of_loglog_le
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X)
    (hlogX : 0 ≤ Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hPlog : Real.log (Real.log (X : ℝ)) ≤ Real.log (P : ℝ))
    (hlog2X : Real.log ((2 * X : ℕ) : ℝ) ≤ 10 * Real.log (X : ℝ)) :
    ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) <
        Nat.ceil (10 * Real.log (X : ℝ) /
          Real.log (Real.log (X : ℝ))) := by
  intro p hp
  have hlogP : 0 < Real.log (P : ℝ) :=
    lt_of_lt_of_le hloglog hPlog
  have hratio0 : Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) ≤
      (10 * Real.log (X : ℝ)) / Real.log (P : ℝ) :=
    div_le_div_of_nonneg_right hlog2X (le_of_lt hlogP)
  have hnum : 0 ≤ 10 * Real.log (X : ℝ) :=
    mul_nonneg (by norm_num) hlogX
  have hratio1 : (10 * Real.log (X : ℝ)) / Real.log (P : ℝ) ≤
      (10 * Real.log (X : ℝ)) / Real.log (Real.log (X : ℝ)) :=
    div_le_div_of_nonneg_left hnum (by positivity) hPlog
  have hratio := hratio0.trans hratio1
  have hp' := Finset.mem_filter.mp hp
  have hpLarge := Finset.mem_filter.mp hp'.1
  have hpP : P < p := hpLarge.2
  have hlt := exponent_lt_log_ratio_of_prime_power_le
    P p (2 * X) (Nat.log p (2 * X)) hP hpP hX
      (Nat.pow_log_le_self p (by omega))
  exact Nat.lt_ceil.mpr (hlt.trans_le hratio)

theorem dyadicPrimeLargeHighPower_natLog_lt_ceil_log_ratio
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X) :
    ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) <
        Nat.ceil (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ)) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpLarge := Finset.mem_filter.mp hp'.1
  have hpP : P < p := hpLarge.2
  have hpow : p ^ Nat.log p (2 * X) ≤ 2 * X :=
    Nat.pow_log_le_self p (by omega)
  have hratio := exponent_lt_log_ratio_of_prime_power_le
    P p (2 * X) (Nat.log p (2 * X)) hP hpP hX hpow
  exact Nat.lt_ceil.mpr hratio

/- Weighted AM--GM gives the elementary concavity estimate needed to control the relative width
   of reciprocal roots uniformly in the exponent.  Keeping this as a standalone real lemma avoids
   hiding the only non-linear step in the later Brun-budget instantiation. -/
theorem rpow_le_one_add_mul_sub
    {D α : ℝ} (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    D ^ α ≤ 1 + α * (D - 1) := by
  have hAM := Real.geom_mean_le_arith_mean2_weighted
    hα0 (sub_nonneg.mpr hα1) hD (by norm_num : (0 : ℝ) ≤ 1)
    (by ring : α + (1 - α) = 1)
  have hAM' : D ^ α ≤ α * D + (1 - α) := by
    simpa using hAM
  calc
    D ^ α ≤ α * D + (1 - α) := hAM'
    _ = 1 + α * (D - 1) := by ring

theorem rpow_sub_one_le_div_sub
    {D r : ℝ} (hD : 1 ≤ D) (hr : 1 ≤ r) :
    D ^ r⁻¹ - 1 ≤ (D - 1) / r := by
  have hD0 : 0 ≤ D := hD.trans' (by norm_num)
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hα0 : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr0)
  have hα1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have h := rpow_le_one_add_mul_sub hD0 hα0 hα1
  have hrewrite : r⁻¹ * (D - 1) = (D - 1) / r := by
    rw [div_eq_mul_inv]
    ring
  linarith

/- Relative-width form for two positive endpoints.  This is the exact elementary estimate used
   after taking reciprocal roots: the exponent-dependent root ratio costs at most `1/r` times
   the original endpoint ratio. -/
theorem rpow_ratio_sub_one_le_div_sub
    {U V r : ℝ} (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ U) (hr : 1 ≤ r) :
    U ^ r⁻¹ / V ^ r⁻¹ - 1 ≤ (U / V - 1) / r := by
  have hD : 1 ≤ U / V := by
    apply (le_div_iff₀ hV).2
    simpa [one_mul] using hVU
  have h := rpow_sub_one_le_div_sub hD hr
  have hdiv : (U / V) ^ r⁻¹ = U ^ r⁻¹ / V ^ r⁻¹ := by
    exact Real.div_rpow hU.le hV.le _
  simpa [hdiv] using h

/- The same estimate remains valid when the lower root endpoint is enlarged to a cutoff `A`.
   This avoids throwing away the `P < p` saving when the source interval is aggregated. -/
theorem rpow_sub_max_div_max_le
    {U V A r : ℝ} (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ U)
    (hr : 1 ≤ r) (hVA : V ^ r⁻¹ ≤ A) :
    (U ^ r⁻¹ - A) / A ≤ (U / V - 1) / r := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hVpow : 0 < V ^ r⁻¹ := Real.rpow_pos_of_pos hV _
  have hApos : 0 < A := lt_of_lt_of_le hVpow hVA
  have hD : 1 ≤ U / V := by
    apply (le_div_iff₀ hV).2
    simpa [one_mul] using hVU
  have hq : 0 ≤ (U / V - 1) / r := by
    exact div_nonneg (sub_nonneg.mpr hD) hrpos.le
  have hratio := rpow_ratio_sub_one_le_div_sub hU hV hVU hr
  have hratio' : U ^ r⁻¹ / V ^ r⁻¹ ≤ 1 + (U / V - 1) / r := by
    linarith
  have hmul : U ^ r⁻¹ ≤ (1 + (U / V - 1) / r) * V ^ r⁻¹ := by
    exact (div_le_iff₀ hVpow).mp hratio'
  have hcoef : 0 ≤ 1 + (U / V - 1) / r := by linarith
  have hmul' : (1 + (U / V - 1) / r) * V ^ r⁻¹ ≤
      (1 + (U / V - 1) / r) * A :=
    mul_le_mul_of_nonneg_left hVA hcoef
  apply (div_le_iff₀ hApos).2
  have hmain : U ^ r⁻¹ - A ≤ A * ((U / V - 1) / r) := by
    linarith [hmul, hmul']
  simpa [mul_comm] using hmain

/- If the lower endpoint is at least `V^(1/r)`, the square-root Brun parameter turns the
   exponent-dependent main term into a single logarithmic ratio.  This is the cancellation that
   makes the source's `r`-sum potentially uniform; the cubic sieve error is handled separately. -/
theorem rpow_main_coefficient_le_log_ratio
    {U V A r : ℝ} (hV : 1 < V) (hVU : V ≤ U) (hr : 1 ≤ r)
    (hVA : V ^ r⁻¹ ≤ A) (hA : 1 < A) :
    (2 / Real.log (Real.sqrt A)) * ((U / V - 1) / r) ≤
      4 * (U / V - 1) / Real.log V := by
  have hVpos : 0 < V := lt_trans (by norm_num) hV
  have hUpos : 0 < U := lt_of_lt_of_le hVpos hVU
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hApos : 0 < A := lt_trans (by norm_num) hA
  have hlogV : 0 < Real.log V := Real.log_pos hV
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hlogsqrt : Real.log (Real.sqrt A) = Real.log A / 2 :=
    Real.log_sqrt hApos.le
  have hlogVA : Real.log V / r ≤ Real.log A := by
    have hlogpow : Real.log (V ^ r⁻¹) ≤ Real.log A :=
      Real.log_le_log (Real.rpow_pos_of_pos hVpos _) hVA
    rw [Real.log_rpow hVpos] at hlogpow
    simpa [div_eq_mul_inv, mul_comm] using hlogpow
  have hdenorder : Real.log V ≤ r * Real.log A := by
    have := (div_le_iff₀ hrpos).mp hlogVA
    simpa [mul_comm] using this
  have hD : 1 ≤ U / V := by
    apply (le_div_iff₀ hVpos).2
    simpa [one_mul] using hVU
  have hnum : 0 ≤ U / V - 1 := sub_nonneg.mpr hD
  have hquot : (U / V - 1) / (r * Real.log A) ≤
      (U / V - 1) / Real.log V := by
    exact div_le_div_of_nonneg_left hnum hlogV hdenorder
  rw [hlogsqrt]
  have hmain : (2 / (Real.log A / 2)) * ((U / V - 1) / r) =
      4 * ((U / V - 1) / (r * Real.log A)) := by
    field_simp [hlogA.ne', hrpos.ne']
    ring
  rw [hmain]
  have h4 := mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 4)
  simpa [div_eq_mul_inv, mul_assoc] using h4

/- A coarse but fully explicit bound for the cubic Brun remainder.  It is deliberately stated with
   scalar endpoint hypotheses: later the source cutoff supplies `A ≥ (log X)^8` and the doubled
   endpoint supplies `log A ≤ 2 log X`.  Constants are intentionally generous to keep the Lean
   arithmetic elementary. -/
theorem sqrt_cubic_error_le_of_log_bounds
    {A L : ℝ} (hL : 4 ≤ L) (hA : L ^ (8 : ℕ) ≤ A)
    (hlogA : Real.log A ≤ 2 * L) :
    (6 * Real.sqrt A * (1 + Real.log (Real.sqrt A)) ^ 3) / A ≤ 48 / L := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 < L := by linarith
  have hLpowpos : 0 < L ^ (8 : ℕ) := by positivity
  have hApos : 0 < A := lt_of_lt_of_le hLpowpos hA
  have hAone : 1 < A := by
    have hpowone : 1 < L ^ (8 : ℕ) := one_lt_pow₀ hLone (by norm_num)
    exact lt_of_lt_of_le hpowone hA
  have hAsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hL4pos : 0 < L ^ (4 : ℕ) := by positivity
  have hL4sqrt : L ^ (4 : ℕ) ≤ Real.sqrt A := by
    apply (Real.le_sqrt' hL4pos).2
    calc
      (L ^ (4 : ℕ)) ^ 2 = L ^ (8 : ℕ) := by ring
      _ ≤ A := hA
  have hlogsqrt : Real.log (Real.sqrt A) = Real.log A / 2 :=
    Real.log_sqrt hApos.le
  have hlogApos : 0 < Real.log A := Real.log_pos hAone
  have hlogsqrtpos : 0 < Real.log (Real.sqrt A) := by
    rw [hlogsqrt]
    exact div_pos hlogApos (by norm_num)
  have hlogsqrt_upper : Real.log (Real.sqrt A) ≤ L := by
    rw [hlogsqrt]
    linarith
  have hpoly : (1 + Real.log (Real.sqrt A)) ^ 3 ≤ (2 * L) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity) ?_ 3
    linarith
  have hnum : 0 ≤ 6 * (1 + Real.log (Real.sqrt A)) ^ 3 := by positivity
  have hnum_le : 6 * (1 + Real.log (Real.sqrt A)) ^ 3 ≤ 6 * (2 * L) ^ 3 :=
    mul_le_mul_of_nonneg_left hpoly (by norm_num)
  have hstep1 : (6 * (1 + Real.log (Real.sqrt A)) ^ 3) / Real.sqrt A ≤
      (6 * (2 * L) ^ 3) / Real.sqrt A :=
    div_le_div_of_nonneg_right hnum_le hAsqrtpos.le
  have hstep2 : (6 * (2 * L) ^ 3) / Real.sqrt A ≤
      (6 * (2 * L) ^ 3) / (L ^ (4 : ℕ)) :=
    div_le_div_of_nonneg_left (by positivity) hL4pos hL4sqrt
  have hrewrite : (6 * Real.sqrt A * (1 + Real.log (Real.sqrt A)) ^ 3) / A =
      (6 * (1 + Real.log (Real.sqrt A)) ^ 3) / Real.sqrt A := by
    have hsq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hApos.le
    field_simp [hApos.ne', hAsqrtpos.ne']
    nlinarith [hsq]
  rw [hrewrite]
  calc
    (6 * (1 + Real.log (Real.sqrt A)) ^ 3) / Real.sqrt A ≤
        (6 * (2 * L) ^ 3) / Real.sqrt A := hstep1
    _ ≤ (6 * (2 * L) ^ 3) / (L ^ (4 : ℕ)) := hstep2
    _ = 48 / L := by
      field_simp [hLpos.ne']
      ring

/- Eventual form of the preceding remainder estimate.  Once a moving lower endpoint `A X` is at
   least `(log X)^8` and its logarithm is at most `2 log X`, the cubic sieve error is already below
   the target `log log X / log X`; this isolates exactly the cutoff bookkeeping needed later. -/
theorem eventually_sqrt_cubic_error_le_loglog_div_log
    (A : ℕ → ℝ)
    (hA : ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ (8 : ℕ) ≤ A X)
    (hlogA : ∀ᶠ X : ℕ in atTop,
      Real.log (A X) ≤ 2 * Real.log (X : ℝ)) :
    ∀ᶠ X : ℕ in atTop,
      (6 * Real.sqrt (A X) * (1 + Real.log (Real.sqrt (A X))) ^ 3) / A X ≤
        Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
  have hL : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
    exact h
  have hLL : ∀ᶠ X : ℕ in atTop,
      48 ≤ Real.log (Real.log (X : ℝ)) := by
    have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (48 : ℝ))
    exact h
  have hlogXpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    exact h
  filter_upwards [hL, hLL, hlogXpos, hA, hlogA] with X hLX hLLX hLpos hAX hlogAX
  have herr := sqrt_cubic_error_le_of_log_bounds hLX hAX hlogAX
  have hquot : (48 : ℝ) / Real.log (X : ℝ) ≤
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) :=
    div_le_div_of_nonneg_right hLLX (le_of_lt hLpos)
  exact herr.trans hquot

/- The integer exponent interval is contained in the real interval obtained by taking the
   reciprocal `r`-th powers of its endpoints.  This is the floor/ceiling bridge needed to feed
   the source interval into `reciprocalPrimesBetween` and hence into Brun--Titchmarsh. -/
theorem sourceExponentInterval_subset_reciprocalPrimeInterval
    (X Y r : ℕ) (hr : 0 < r) (hY : 0 < Y) :
    sourceExponentInterval X Y r ⊆
      (Finset.Icc
        (Nat.ceil ((Y : ℝ) ^ ((r : ℝ)⁻¹)))
        (Nat.floor (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)))).filter Nat.Prime := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hpPred := hp'.2
  have hpPrime : p.Prime := hpPred.1
  have hp0 : 0 < p := hpPrime.pos
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hpR0 : 0 ≤ (p : ℝ) := by positivity
  have hupper0 : 0 ≤ ((2 * X : ℕ) : ℝ) := by positivity
  have hpPow : (Y : ℝ) < (p : ℝ) ^ (r : ℕ) := by
    exact_mod_cast hpPred.2.1
  have hpPowUpper : (p : ℝ) ^ (r : ℕ) ≤ ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast hpPred.2.2
  have hrootLower : (Y : ℝ) ^ ((r : ℝ)⁻¹) < (p : ℝ) := by
    have h := Real.rpow_lt_rpow hY0 hpPow (inv_pos.mpr hrR)
    have hpow : ((p : ℝ) ^ (r : ℕ)) ^ ((r : ℝ)⁻¹) = (p : ℝ) := by
      rw [← Real.rpow_natCast, ← (Real.rpow_mul hpR0)]
      rw [mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hr))]
      simp
    exact h.trans_eq hpow
  have hrootUpper : (p : ℝ) ≤ ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) := by
    have hpPowUpper' : (p : ℝ) ^ (r : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      simpa only [Real.rpow_natCast] using hpPowUpper
    have h := Real.rpow_le_rpow
      (x := (p : ℝ) ^ (r : ℝ)) (y := ((2 * X : ℕ) : ℝ))
      (z := (r : ℝ)⁻¹) (by positivity) hpPowUpper' (inv_pos.mpr hrR).le
    have h' : ((p : ℝ) ^ (r : ℕ)) ^ ((r : ℝ)⁻¹) ≤
        ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) := by
      simpa only [Real.rpow_natCast] using h
    have hpow : ((p : ℝ) ^ (r : ℕ)) ^ ((r : ℝ)⁻¹) = (p : ℝ) := by
      rw [← Real.rpow_natCast, ← (Real.rpow_mul hpR0)]
      rw [mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hr))]
      simp
    exact hpow ▸ h'
  have hpCeil : Nat.ceil ((Y : ℝ) ^ ((r : ℝ)⁻¹)) ≤ p := by
    apply Nat.ceil_le.mpr
    exact hrootLower.le
  have hpFloor : p ≤ Nat.floor (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) := by
    exact Nat.le_floor hrootUpper
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hpCeil, hpFloor⟩, hpPrime⟩

/- The cutoff-preserving interval bridge.  The lower endpoint is the maximum of the base-prime
   cutoff and the reciprocal `r`-th root of `Y`; this retains the `1 / log P` saving in Brun's
   estimate instead of enlarging back to the interval starting at `Y^(1/r)`. -/
theorem sourceExponentLargeInterval_subset_reciprocalPrimeInterval
    (X P Y r : ℕ) (hP : 1 < P) (hr : 0 < r) (hY : 0 < Y) :
    sourceExponentLargeInterval X P Y r ⊆
      (Finset.Icc
        (Nat.ceil (max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))))
        (Nat.floor (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)))).filter Nat.Prime := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hpPred := hp'.2
  have hpPrime : p.Prime := hpPred.1
  have hpSrc : p ∈ sourceExponentInterval X Y r := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpPred⟩
    apply Finset.mem_Icc.mpr
    refine ⟨?_, hpI.2⟩
    omega
  have hpRoot := Finset.mem_filter.mp
    (sourceExponentInterval_subset_reciprocalPrimeInterval X Y r hr hY hpSrc)
  have hpRootI := Finset.mem_Icc.mp hpRoot.1
  have hpP : P < p := by omega
  have hPp : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.le
  have hrootp : (Y : ℝ) ^ ((r : ℝ)⁻¹) ≤ (p : ℝ) :=
    Nat.ceil_le.mp hpRootI.1
  have hmax : max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) ≤ (p : ℝ) :=
    max_le hPp hrootp
  have hpCeil : Nat.ceil (max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) ≤ p := by
    apply Nat.ceil_le.mpr
    exact hmax
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hpCeil, hpRootI.2⟩, hpPrime⟩

theorem sourceExponentLargeInterval_reciprocal_mass_le_between
    (X P Y r : ℕ) (hP : 1 < P) (hr : 0 < r) (hY : 0 < Y) :
    (∑ p ∈ sourceExponentLargeInterval X P Y r, ((p : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween
        (max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)))
        (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (sourceExponentLargeInterval_subset_reciprocalPrimeInterval X P Y r hP hr hY)
  intro p hp hnot
  positivity

theorem sourceExponentInterval_reciprocal_mass_le_between
    (X Y r : ℕ) (hr : 0 < r) (hY : 0 < Y) :
    (∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween ((Y : ℝ) ^ ((r : ℝ)⁻¹))
        (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (sourceExponentInterval_subset_reciprocalPrimeInterval X Y r hr hY)
  intro p hp hnot
  positivity

/- A source-shaped Brun--Titchmarsh certificate for one exponent layer.  The interval ordering is
   explicit because the finite source split may be instantiated with any integer cutoff `Y`; the
   asymptotic choice `Y ≈ X / log log X` is intentionally left to the caller. -/
theorem sourceExponentInterval_reciprocal_mass_le_brun
    (X Y r : ℕ) (hr : 0 < r) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) ≤
      (2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
          ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z +
        6 * z * (1 + Real.log z) ^ 3) /
        ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hX0 : 0 ≤ ((2 * X : ℕ) : ℝ) := by positivity
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hYltR : (Y : ℝ) < ((2 * X : ℕ) : ℝ) := by exact_mod_cast hYlt
  have hab : (Y : ℝ) ^ ((r : ℝ)⁻¹) <
      ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
    Real.rpow_lt_rpow hY0 hYltR (inv_pos.mpr hrR)
  have ha : 0 < (Y : ℝ) ^ ((r : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hYpos _
  exact (sourceExponentInterval_reciprocal_mass_le_between X Y r hr hY).trans
      (reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
      ((Y : ℝ) ^ ((r : ℝ)⁻¹)) (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) z ha hab hz)

theorem sourceExponentLargeInterval_reciprocal_mass_le_brun
    (X P Y r : ℕ) (hP : 1 < P) (hr : 0 < r) (hY : 0 < Y)
    (hYlt : Y < 2 * X)
    (hPupper : (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ sourceExponentLargeInterval X P Y r, ((p : ℝ)⁻¹)) ≤
      (2 * (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) -
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z +
        6 * z * (1 + Real.log z) ^ 3) /
        max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hX0 : 0 ≤ ((2 * X : ℕ) : ℝ) := by positivity
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hYltR : (Y : ℝ) < ((2 * X : ℕ) : ℝ) := by exact_mod_cast hYlt
  have hrootlt : (Y : ℝ) ^ ((r : ℝ)⁻¹) <
      ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
    Real.rpow_lt_rpow hY0 hYltR (inv_pos.mpr hrR)
  have hab : max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) <
      ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
    max_lt hPupper hrootlt
  have ha : 0 < max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
    exact lt_of_lt_of_le hPpos (le_max_left _ _)
  exact (sourceExponentLargeInterval_reciprocal_mass_le_between
    X P Y r hP hr hY).trans
      (reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
        (max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)))
        (((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) z ha hab hz)

theorem sourceExponentLargeInterval_zero_empty (X P Y : ℕ) (hY : 0 < Y) :
    sourceExponentLargeInterval X P Y 0 = ∅ := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hylt : Y < 1 := by simpa using hp'.2.2.1
    omega
  · simp

noncomputable def sourceExponentLargeBrunBudget
    (X P Y : ℕ) (z : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else
    (2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
        max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z +
      6 * z * (1 + Real.log z) ^ 3) /
      max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))

theorem sourceExponentLargeBrunBudget_nonneg
    (X P Y r : ℕ) (hP : 1 < P) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hPupper : 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℝ) (hz : 1 < z) :
    0 ≤ sourceExponentLargeBrunBudget X P Y z r := by
  by_cases hr0 : r = 0
  · simp [sourceExponentLargeBrunBudget, hr0]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have hY0 : 0 ≤ (Y : ℝ) := by positivity
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
    have hYltR : (Y : ℝ) < ((2 * X : ℕ) : ℝ) := by exact_mod_cast hYlt
    have hrootlt : (Y : ℝ) ^ ((r : ℝ)⁻¹) <
        ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
      Real.rpow_lt_rpow hY0 hYltR (inv_pos.mpr hrR)
    have hmaxlt : max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) <
        ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
      max_lt (hPupper hrpos) hrootlt
    have hdiff : 0 ≤ ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) -
        max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
      linarith [hmaxlt.le]
    have hlog : 0 < Real.log z := Real.log_pos hz
    have hmain : 0 ≤ 2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
        max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z := by
      positivity
    have herror : 0 ≤ 6 * z * (1 + Real.log z) ^ 3 := by positivity
    have hden : 0 < max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
      have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
      exact lt_of_lt_of_le hPpos (le_max_left _ _)
    rw [sourceExponentLargeBrunBudget, ite_eq_right hr0]
    exact div_nonneg (add_nonneg hmain herror) hden.le

/- The weighted-AM--GM width estimate specialized to the cutoff-preserving source interval.
   It bounds the main Brun numerator divided by its lower endpoint without losing the `P` cutoff. -/
theorem sourceExponentLarge_relative_width_le
    (X P Y r : ℕ) (hr : 0 < r) (hY : 0 < Y)
    (hYlt : Y < 2 * X) :
    ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) -
        max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) /
      max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) ≤
      ((((2 * X : ℕ) : ℝ) / (Y : ℝ) - 1) / (r : ℝ)) := by
  have hU : 0 < ((2 * X : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * X by omega)
  have hV : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hVU : (Y : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hYlt)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))
  exact rpow_sub_max_div_max_le hU hV hVU hr1 (le_max_right _ _)

/- After the root-width reduction, the main term in the Brun budget has no hidden dependence on
   the exponent except through the explicit factor `1/r`.  The remaining cubic sieve error is kept
   visible as a separate summand for the eventual analytic estimate. -/
theorem sourceExponentLargeBrunBudget_le_width_plus_error
    (X P Y r : ℕ) (hr : 0 < r) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℝ) (hz : 1 < z) :
    sourceExponentLargeBrunBudget X P Y z r ≤
      (2 / Real.log z) *
          ((((2 * X : ℕ) : ℝ) / (Y : ℝ) - 1) / (r : ℝ)) +
        (6 * z * (1 + Real.log z) ^ 3) /
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) := by
  have hwidth := sourceExponentLarge_relative_width_le X P Y r hr hY hYlt
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hcoef : 0 ≤ 2 / Real.log z := by positivity
  have hmain :
      (2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z) /
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) ≤
        (2 / Real.log z) *
          ((((2 * X : ℕ) : ℝ) / (Y : ℝ) - 1) / (r : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hwidth hcoef
    calc
      (2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z) /
          max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹)) =
          (2 / Real.log z) *
            (((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
              max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) /
                max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))) := by
            field_simp [hlogz.ne']
      _ ≤ (2 / Real.log z) *
          ((((2 * X : ℕ) : ℝ) / (Y : ℝ) - 1) / (r : ℝ)) := hmul
  rw [sourceExponentLargeBrunBudget, ite_eq_right (Nat.ne_of_gt hr), add_div]
  exact add_le_add hmain (le_refl _)

/- Choosing `z = √A` with `A = max(P,Y^(1/r))` removes the exponent from the main term.  The
   remaining error is explicit and is the only part that still needs a lower bound on the cutoff. -/
theorem sourceExponentLargeBrunBudget_le_log_ratio_plus_sqrt_error
    (X P Y r : ℕ) (hP : 1 < P) (hr : 0 < r) (hY : 1 < Y)
    (hYlt : Y < 2 * X) :
    let A : ℝ := max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))
    sourceExponentLargeBrunBudget X P Y (Real.sqrt A) r ≤
      4 * ((((2 * X : ℕ) : ℝ) / (Y : ℝ) - 1) / Real.log (Y : ℝ)) +
        (6 * Real.sqrt A * (1 + Real.log (Real.sqrt A)) ^ 3) / A := by
  dsimp
  let A : ℝ := max (P : ℝ) ((Y : ℝ) ^ ((r : ℝ)⁻¹))
  have hA : 1 < A := lt_of_lt_of_le (by exact_mod_cast hP) (le_max_left _ _)
  have hAsqrt : 1 < Real.sqrt A := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [hA]
  have hYpos : 0 < Y := by omega
  have hbase := sourceExponentLargeBrunBudget_le_width_plus_error
    X P Y r hr hYpos hYlt (Real.sqrt A) hAsqrt
  have hcoeff := rpow_main_coefficient_le_log_ratio
    (U := ((2 * X : ℕ) : ℝ)) (V := (Y : ℝ)) (A := A) (r := (r : ℝ))
    (by exact_mod_cast hY) (by exact_mod_cast (Nat.le_of_lt hYlt))
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr)))
    (le_max_right _ _) hA
  have hsum := add_le_add hcoeff
    (le_refl ((6 * Real.sqrt A * (1 + Real.log (Real.sqrt A)) ^ 3) / A))
  exact hbase.trans (by
    convert hsum using 1; ring)

theorem sourceExponentLargeInterval_reciprocal_mass_le_brun_budget
    (X P Y r : ℕ) (hP : 1 < P) (hr : 0 < r) (hY : 0 < Y)
    (hYlt : Y < 2 * X)
    (hPupper : (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ sourceExponentLargeInterval X P Y r, ((p : ℝ)⁻¹)) ≤
      sourceExponentLargeBrunBudget X P Y z r := by
  simpa [sourceExponentLargeBrunBudget, hr.ne'] using
    (sourceExponentLargeInterval_reciprocal_mass_le_brun
      X P Y r hP hr hY hYlt hPupper z hz)

theorem sourceExponentInterval_zero_empty (X Y : ℕ) (hY : 0 < Y) :
    sourceExponentInterval X Y 0 = ∅ := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hylt : Y < 1 := by simpa using hp'.2.2.1
    omega
  · simp

theorem dyadicPrimeLargeHighPower_exponent_fiber_subset_interval
    (X P Y r : ℕ) :
    (dyadicPrimeLargeHighPowerSet X P Y).filter
        (fun p ↦ Nat.log p (2 * X) = r) ⊆
      sourceExponentInterval X Y r := by
  intro p hp
  have hpHigh := Finset.mem_filter.mp hp
  have hpLarge := Finset.mem_filter.mp hpHigh.1
  have hpLargePrime := Finset.mem_filter.mp hpLarge.1
  have hpDyadic := Finset.mem_filter.mp hpLargePrime.1
  have hpI := Finset.mem_Icc.mp hpDyadic.1
  have hpPrime : p.Prime := hpDyadic.2
  have hlog : Nat.log p (2 * X) = r := hpHigh.2
  have hX0 : 2 * X ≠ 0 := by omega
  have hpowle : p ^ r ≤ 2 * X := by
    simpa [← hlog] using Nat.pow_log_le_self p hX0
  have hpowgt : Y < p ^ r := by
    simpa [← hlog] using hpLarge.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr hpI, ?_⟩
  exact ⟨hpPrime, hpowgt, hpowle⟩

theorem dyadicPrimeLargeHighPower_exponent_fiber_subset_large_interval
    (X P Y r : ℕ) :
    (dyadicPrimeLargeHighPowerSet X P Y).filter
        (fun p ↦ Nat.log p (2 * X) = r) ⊆
      sourceExponentLargeInterval X P Y r := by
  intro p hp
  have hpHigh := Finset.mem_filter.mp hp
  have hpLarge := Finset.mem_filter.mp hpHigh.1
  have hpLargePrime := Finset.mem_filter.mp hpLarge.1
  have hpDyadic := Finset.mem_filter.mp hpLargePrime.1
  have hpI := Finset.mem_Icc.mp hpDyadic.1
  have hpPrime : p.Prime := hpDyadic.2
  have hpP : P < p := hpLargePrime.2
  have hlog : Nat.log p (2 * X) = r := hpHigh.2
  have hX0 : 2 * X ≠ 0 := by omega
  have hpowle : p ^ r ≤ 2 * X := by
    simpa [← hlog] using Nat.pow_log_le_self p hX0
  have hpowgt : Y < p ^ r := by
    simpa [← hlog] using hpLarge.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hpP, hpI.2⟩, ?_⟩
  exact ⟨hpPrime, hpowgt, hpowle⟩

theorem dyadicPrimeLargeHighPower_exponent_fiber_reciprocal_le_large_interval
    (X P Y r : ℕ) :
    (∑ p ∈ (dyadicPrimeLargeHighPowerSet X P Y).filter
        (fun p ↦ Nat.log p (2 * X) = r), ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ sourceExponentLargeInterval X P Y r, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (dyadicPrimeLargeHighPower_exponent_fiber_subset_large_interval X P Y r)
  intro p hp hnot
  positivity

theorem dyadicPrimeLargeHighPower_exponent_fiber_reciprocal_le_interval
    (X P Y r : ℕ) :
    (∑ p ∈ (dyadicPrimeLargeHighPowerSet X P Y).filter
        (fun p ↦ Nat.log p (2 * X) = r), ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (dyadicPrimeLargeHighPower_exponent_fiber_subset_interval X P Y r)
  intro p hp hnot
  positivity

theorem dyadic_endpoint_weight_source_prime_split (X P : ℕ) :
    (∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p) =
      (∑ p ∈ dyadicPrimeSmallPrimeSet X P, dyadicEndpointWeight X p) +
        ∑ p ∈ dyadicPrimeLargePrimeSet X P, dyadicEndpointWeight X p := by
  have h := Finset.sum_filter_add_sum_filter_not
    (dyadicPrimeSet X) (fun p ↦ p ≤ P) (fun p ↦ dyadicEndpointWeight X p)
  rw [← h]
  have hlarge :
      (dyadicPrimeSet X).filter (fun p ↦ ¬ p ≤ P) = dyadicPrimeLargePrimeSet X P := by
    ext p
    simp [dyadicPrimeLargePrimeSet, not_le]
  have hsmall :
      (dyadicPrimeSet X).filter (fun p ↦ p ≤ P) = dyadicPrimeSmallPrimeSet X P := by
    rfl
  rw [hsmall, hlarge]

theorem dyadic_endpoint_weight_source_large_power_split (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeLargePrimeSet X P, dyadicEndpointWeight X p) =
      (∑ p ∈ dyadicPrimeLargeLowPowerSet X P Y, dyadicEndpointWeight X p) +
        ∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p := by
  have h := Finset.sum_filter_add_sum_filter_not
    (dyadicPrimeLargePrimeSet X P)
    (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y) (fun p ↦ dyadicEndpointWeight X p)
  rw [← h]
  have hhigh :
      (dyadicPrimeLargePrimeSet X P).filter
          (fun p ↦ ¬ p ^ Nat.log p (2 * X) ≤ Y) =
        dyadicPrimeLargeHighPowerSet X P Y := by
    ext p
    simp [dyadicPrimeLargeHighPowerSet, not_le]
  have hlow :
      (dyadicPrimeLargePrimeSet X P).filter
          (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y) =
        dyadicPrimeLargeLowPowerSet X P Y := by
    rfl
  rw [hlow, hhigh]

/- Exact finite form of the source's three-way split (small base primes, large primes with a low
   endpoint power, and large primes with a high endpoint power).  The names `low` and `high` are
   intentionally neutral: the analytic choice of `Y` and its relation to `X/log log X` is separate.
 -/
theorem dyadic_endpoint_weight_source_three_way_split (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p) =
      (∑ p ∈ dyadicPrimeSmallPrimeSet X P, dyadicEndpointWeight X p) +
        (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) +
          ∑ p ∈ dyadicPrimeLargeLowPowerSet X P Y, dyadicEndpointWeight X p := by
  rw [dyadic_endpoint_weight_source_prime_split,
    dyadic_endpoint_weight_source_large_power_split]
  ring

/- The low endpoint-power branch is elementary: its weight is at most `2Y/p`, and all its prime
   bases lie below `2X`.  This is the finite core of the source's estimate (24); the relation
   between `Y` and `X/log log X` is intentionally left to the analytic instantiation. -/
theorem dyadicEndpointLargeLowPower_mass_le_cutoff_reciprocal_mass
    (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeLargeLowPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (2 * (Y : ℝ)) * (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) := by
  have hsub : dyadicPrimeLargeLowPowerSet X P Y ⊆ Nat.primesLE (2 * X) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpdyadic := Finset.mem_filter.mp hpbase.1
    have hpI := Finset.mem_Icc.mp hpdyadic.1
    exact Nat.mem_primesLE.mpr ⟨hpI.2, hpdyadic.2⟩
  have hpoint : ∀ p ∈ dyadicPrimeLargeLowPowerSet X P Y,
      dyadicEndpointWeight X p ≤ (2 * (Y : ℝ)) * ((p : ℝ)⁻¹) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hlow := hp'.2
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpdyadic := Finset.mem_filter.mp hpbase.1
    have hpprime := hpdyadic.2
    have hp0 : 0 < p := hpprime.pos
    have hpowR : ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast hlow
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    unfold dyadicEndpointWeight
    have hdiv := div_le_div_of_nonneg_right hpowR (le_of_lt hpR)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  calc
    (∑ p ∈ dyadicPrimeLargeLowPowerSet X P Y, dyadicEndpointWeight X p) ≤
        ∑ p ∈ dyadicPrimeLargeLowPowerSet X P Y,
          (2 * (Y : ℝ)) * ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ ≤ (2 * (Y : ℝ)) * (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      positivity

/- Generic high-branch cover lemma.  It isolates exactly what an interval proof such as the
   source's (25)--(27) must provide: a finite pairwise-disjoint cover of the high-power primes.
   Once such a cover is supplied, the endpoint weights collapse to `4X` times the reciprocal
   prime mass of the covering intervals. -/
theorem dyadicEndpointLargeHighPower_mass_le_of_disjoint_cover
    (X P Y R : ℕ) (I : ℕ → Finset ℕ)
    (hcover : dyadicPrimeLargeHighPowerSet X P Y ⊆
      (Finset.range R).biUnion I)
    (hdisj : ∀ ⦃i⦄, i ∈ Finset.range R → ∀ ⦃j⦄, j ∈ Finset.range R →
      (I i ∩ I j).Nonempty → i = j) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ i ∈ Finset.range R, ∑ p ∈ I i, ((p : ℝ)⁻¹)) := by
  have hpoint : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      dyadicEndpointWeight X p ≤ (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpdyadic := Finset.mem_filter.mp hpbase.1
    have hpprime := hpdyadic.2
    have hpI := Finset.mem_Icc.mp hpdyadic.1
    have hp0 : 0 < p := hpprime.pos
    have hX0 : 2 * X ≠ 0 := by omega
    have hpow : p ^ Nat.log p (2 * X) ≤ 2 * X :=
      Nat.pow_log_le_self p hX0
    have hpowR : ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) ≤ (2 * X : ℝ) := by
      exact_mod_cast hpow
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    unfold dyadicEndpointWeight
    have hdiv := div_le_div_of_nonneg_right hpowR (le_of_lt hpR)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) ≤
          2 * ((2 * X : ℝ) / (p : ℝ)) := hmul
      _ = (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
        simp [div_eq_mul_inv]
        ring
  have hunion :
      (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
        (4 * (X : ℝ)) * ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ (Finset.range R).biUnion I,
        (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hcover
    intro p hp hnot
    positivity
  have hbi :
      (∑ p ∈ (Finset.range R).biUnion I,
        (4 * (X : ℝ)) * ((p : ℝ)⁻¹)) =
      (4 * (X : ℝ)) *
        (∑ i ∈ Finset.range R, ∑ p ∈ I i, ((p : ℝ)⁻¹)) := by
    rw [Finset.sum_biUnion (by
      rw [Finset.pairwiseDisjoint_iff]
      intro i hi j hj hij
      exact hdisj hi hj hij)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        ∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
          (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ ≤ ∑ p ∈ (Finset.range R).biUnion I,
          (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := hunion
    _ = (4 * (X : ℝ)) *
        (∑ i ∈ Finset.range R, ∑ p ∈ I i, ((p : ℝ)⁻¹)) := hbi

/- Instantiation of the generic cover with the already formalized disjoint base-16 prime blocks.
   This gives an unconditional coarse high-branch estimate; replacing these broad blocks by the
   narrower exponent-indexed intervals is precisely the remaining source (25)--(27) refinement. -/
theorem dyadicEndpointLargeHighPower_mass_le_dyadic_cover
    (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ i ∈ Finset.range (Nat.log 16 (2 * X) + 1),
          ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_disjoint_cover
    X P Y (Nat.log 16 (2 * X) + 1) dyadicDisjointPrimeBlock
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpdyadic := Finset.mem_filter.mp hpbase.1
    have hpI := Finset.mem_Icc.mp hpdyadic.1
    have hpLE : p ∈ Nat.primesLE (2 * X) :=
      Nat.mem_primesLE.mpr ⟨hpI.2, hpdyadic.2⟩
    simpa [dyadicDisjointPrimeFamily] using
      (primesLE_subset_dyadicDisjointPrimeFamily_succ_log (2 * X) hpLE)
  · intro i hi j hj hij
    by_cases heq : i = j
    · exact heq
    · exact False.elim (hij.not_disjoint
        ((dyadicDisjointPrimeBlock_pairwiseDisjoint
          (Nat.log 16 (2 * X) + 1)) hi hj heq))

/- Exponent-indexed cover of the high branch.  The fibers are disjoint by construction and the
   exponent range is finite because every base prime is at most `2X`.  This is the exact finite
   reindexing needed before applying a Brun estimate to each `r`-interval. -/
theorem dyadicEndpointLargeHighPower_mass_le_exponent_cover
    (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
          ∑ p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y r, ((p : ℝ)⁻¹)) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_disjoint_cover
    X P Y (Nat.log 2 (2 * X) + 1)
      (dyadicPrimeLargeHighPowerExponentFiber X P Y)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpdyadic := Finset.mem_filter.mp hpbase.1
    let r := Nat.log p (2 * X)
    have hrle : r ≤ Nat.log 2 (2 * X) := by
      dsimp [r]
      exact Nat.log_mono (by norm_num) hpdyadic.2.two_le (le_refl _)
    have hrmem : r ∈ Finset.range (Nat.log 2 (2 * X) + 1) := by
      dsimp [r]
      exact Finset.mem_range.mpr (by omega)
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hrmem, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hp, rfl⟩
  · intro i hi j hj hij
    obtain ⟨p, hp⟩ := hij
    have hpi : p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y i :=
      (Finset.mem_inter.mp hp).1
    have hpj : p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y j :=
      (Finset.mem_inter.mp hp).2
    have hpi' := (Finset.mem_filter.mp hpi).2
    have hpj' := (Finset.mem_filter.mp hpj).2
    exact hpi'.symm.trans hpj'

theorem dyadicEndpointLargeHighPower_mass_le_exponent_interval_cover
    (X P Y : ℕ) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
          ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) := by
  have hcover := dyadicEndpointLargeHighPower_mass_le_exponent_cover X P Y
  have hsum :
      (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
        ∑ p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y r, ((p : ℝ)⁻¹)) ≤
      ∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
        ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro r hr
    exact dyadicPrimeLargeHighPower_exponent_fiber_reciprocal_le_interval X P Y r
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) *
          (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
            ∑ p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y r, ((p : ℝ)⁻¹)) := hcover
    _ ≤ (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
          ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/- A certificate interface for the source's equation (27).  The finite reindexing above is
   unconditional; supplying a nonnegative budget `B r` for each source interval immediately
   aggregates it into a high-branch endpoint bound.  This keeps the remaining Brun analysis
   explicit rather than hiding it in an axiom or an unproved theorem. -/
theorem dyadicEndpointLargeHighPower_mass_le_of_exponent_interval_budget
    (X P Y : ℕ) (B : ℕ → ℝ)
    (hB : ∀ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
      (∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) ≤ B r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1), B r) := by
  have hcover := dyadicEndpointLargeHighPower_mass_le_exponent_interval_cover X P Y
  have hsum :
      (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
        ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) ≤
      ∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1), B r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hB r hr
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) *
          (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
            ∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) := hcover
    _ ≤ (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1), B r) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/- Range-truncated variant of the certificate interface.  This is the form that can exploit the
   source's much shorter exponent range once its elementary upper-bound lemma is supplied. -/
theorem dyadicEndpointLargeHighPower_mass_le_of_exponent_range_interval_budget
    (X P Y Rmax : ℕ) (B : ℕ → ℝ)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hB : ∀ r ∈ Finset.range Rmax,
      (∑ p ∈ sourceExponentInterval X Y r, ((p : ℝ)⁻¹)) ≤ B r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax, B r) := by
  let I : ℕ → Finset ℕ := fun r ↦
    (dyadicPrimeLargeHighPowerSet X P Y).filter
      (fun p ↦ Nat.log p (2 * X) = r)
  have hcover : dyadicPrimeLargeHighPowerSet X P Y ⊆
      (Finset.range Rmax).biUnion I := by
    intro p hp
    let r := Nat.log p (2 * X)
    have hr : r ∈ Finset.range Rmax := Finset.mem_range.mpr (hExp p hp)
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hp, rfl⟩
  have hdisj : ∀ ⦃i⦄, i ∈ Finset.range Rmax → ∀ ⦃j⦄, j ∈ Finset.range Rmax →
      (I i ∩ I j).Nonempty → i = j := by
    intro i hi j hj hij
    obtain ⟨p, hp⟩ := hij
    have hpi : p ∈ I i := (Finset.mem_inter.mp hp).1
    have hpj : p ∈ I j := (Finset.mem_inter.mp hp).2
    have hpi' := (Finset.mem_filter.mp hpi).2
    have hpj' := (Finset.mem_filter.mp hpj).2
    exact hpi'.symm.trans hpj'
  have hcoverMass := dyadicEndpointLargeHighPower_mass_le_of_disjoint_cover
    X P Y Rmax I hcover hdisj
  have hsum : (∑ r ∈ Finset.range Rmax, ∑ p ∈ I r, ((p : ℝ)⁻¹)) ≤
      ∑ r ∈ Finset.range Rmax, B r := by
    apply Finset.sum_le_sum
    intro r hr
    have hfiber : I r ⊆ sourceExponentInterval X Y r := by
      intro p hp
      exact dyadicPrimeLargeHighPower_exponent_fiber_subset_interval X P Y r hp
    exact (Finset.sum_le_sum_of_subset_of_nonneg hfiber (by
      intro p hp hnot
      positivity)).trans (hB r hr)
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax,
          ∑ p ∈ I r, ((p : ℝ)⁻¹)) := hcoverMass
    _ ≤ (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax, B r) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/- Fiber-level form of the preceding interface.  It is useful when the analytic interval bound
   retains an extra restriction (here `P < p`) that would be lost by enlarging the fiber to the
   uncut source interval. -/
theorem dyadicEndpointLargeHighPower_mass_le_of_exponent_range_fiber_budget
    (X P Y Rmax : ℕ) (B : ℕ → ℝ)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hB : ∀ r ∈ Finset.range Rmax,
      (∑ p ∈ dyadicPrimeLargeHighPowerExponentFiber X P Y r, ((p : ℝ)⁻¹)) ≤ B r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax, B r) := by
  let I : ℕ → Finset ℕ := fun r ↦
    (dyadicPrimeLargeHighPowerSet X P Y).filter
      (fun p ↦ Nat.log p (2 * X) = r)
  have hcover : dyadicPrimeLargeHighPowerSet X P Y ⊆
      (Finset.range Rmax).biUnion I := by
    intro p hp
    let r := Nat.log p (2 * X)
    have hr : r ∈ Finset.range Rmax := Finset.mem_range.mpr (hExp p hp)
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hp, rfl⟩
  have hdisj : ∀ ⦃i⦄, i ∈ Finset.range Rmax → ∀ ⦃j⦄, j ∈ Finset.range Rmax →
      (I i ∩ I j).Nonempty → i = j := by
    intro i hi j hj hij
    obtain ⟨p, hp⟩ := hij
    have hpi : p ∈ I i := (Finset.mem_inter.mp hp).1
    have hpj : p ∈ I j := (Finset.mem_inter.mp hp).2
    have hpi' := (Finset.mem_filter.mp hpi).2
    have hpj' := (Finset.mem_filter.mp hpj).2
    exact hpi'.symm.trans hpj'
  have hcoverMass := dyadicEndpointLargeHighPower_mass_le_of_disjoint_cover
    X P Y Rmax I hcover hdisj
  have hsum : (∑ r ∈ Finset.range Rmax, ∑ p ∈ I r, ((p : ℝ)⁻¹)) ≤
      ∑ r ∈ Finset.range Rmax, B r := by
    apply Finset.sum_le_sum
    intro r hr
    simpa [I, dyadicPrimeLargeHighPowerExponentFiber] using hB r hr
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax,
          ∑ p ∈ I r, ((p : ℝ)⁻¹)) := hcoverMass
    _ ≤ (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax, B r) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem dyadicEndpointLargeHighPower_mass_le_of_exponent_range_large_interval_budget
    (X P Y Rmax : ℕ) (B : ℕ → ℝ)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hB : ∀ r ∈ Finset.range Rmax,
      (∑ p ∈ sourceExponentLargeInterval X P Y r, ((p : ℝ)⁻¹)) ≤ B r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (∑ r ∈ Finset.range Rmax, B r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_fiber_budget
    X P Y Rmax B hExp
  intro r hr
  have hfiber := dyadicPrimeLargeHighPower_exponent_fiber_reciprocal_le_large_interval
    X P Y r
  exact hfiber.trans (hB r hr)

/- Direct source-shaped high-branch interface retaining the base-prime cutoff.  The only
   per-layer side condition is that the cutoff `P` lies below the upper reciprocal root; for
   positive exponents this is exactly what the short exponent-range argument is meant to ensure. -/
theorem dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_range
    (X P Y Rmax : ℕ) (hP : 1 < P) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hPupper : ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range Rmax, sourceExponentLargeBrunBudget X P Y z r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_large_interval_budget
    X P Y Rmax (sourceExponentLargeBrunBudget X P Y z) hExp
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp [sourceExponentLargeBrunBudget, sourceExponentLargeInterval_zero_empty X P Y hY]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    simpa [sourceExponentLargeBrunBudget, hr0] using
      (sourceExponentLargeInterval_reciprocal_mass_le_brun_budget
        X P Y r hP hrpos hY hYlt (hPupper r hr hrpos) z hz)

/- Variable-parameter version of the source budget.  The optimized Brun parameter may depend on
   the exponent layer (as it does for `z = √A_r`), so this adapter keeps that dependence explicit. -/
theorem dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_range_variable_z
    (X P Y Rmax : ℕ) (hP : 1 < P) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hPupper : ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℕ → ℝ) (hz : ∀ r ∈ Finset.range Rmax, 1 < z r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range Rmax,
          sourceExponentLargeBrunBudget X P Y (z r) r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_large_interval_budget
    X P Y Rmax (fun r ↦ sourceExponentLargeBrunBudget X P Y (z r) r) hExp
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp [sourceExponentLargeBrunBudget, sourceExponentLargeInterval_zero_empty X P Y hY]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    simpa [sourceExponentLargeBrunBudget, hr0] using
      (sourceExponentLargeInterval_reciprocal_mass_le_brun_budget
        X P Y r hP hrpos hY hYlt (hPupper r hr hrpos) (z r) (hz r hr))

theorem dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_log_range
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X)
    (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range
          (Nat.ceil (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))),
          sourceExponentLargeBrunBudget X P Y z r) := by
  let Rmax : ℕ := Nat.ceil
    (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))
  have hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax := by
    intro p hp
    simpa [Rmax] using
      (dyadicPrimeLargeHighPower_natLog_lt_ceil_log_ratio X P Y hP hX p hp)
  have hRange : ∀ r ∈ Finset.range Rmax,
      (r : ℝ) < Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) := by
    intro r hr
    exact Nat.lt_ceil.mp (by simpa [Rmax] using hr)
  have hPupper : ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
    prime_cutoff_lt_reciprocal_root_of_nat_range P (2 * X) Rmax hP hX hRange
  have hmass := dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_range
    X P Y Rmax hP hY hYlt hExp hPupper z hz
  simpa [Rmax] using hmass

theorem dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_log_range_variable_z
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X)
    (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℕ → ℝ) (hz : ∀ r, 1 < z r) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range
          (Nat.ceil (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))),
          sourceExponentLargeBrunBudget X P Y (z r) r) := by
  let Rmax : ℕ := Nat.ceil
    (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))
  have hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax := by
    intro p hp
    simpa [Rmax] using
      (dyadicPrimeLargeHighPower_natLog_lt_ceil_log_ratio X P Y hP hX p hp)
  have hRange : ∀ r ∈ Finset.range Rmax,
      (r : ℝ) < Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) := by
    intro r hr
    exact Nat.lt_ceil.mp (by simpa [Rmax] using hr)
  have hPupper : ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
    prime_cutoff_lt_reciprocal_root_of_nat_range P (2 * X) Rmax hP hX hRange
  have hmass := dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_range_variable_z
    X P Y Rmax hP hY hYlt hExp hPupper z (fun r hr ↦ hz r)
  simpa [Rmax] using hmass

theorem sourceExponentLargeBrunBudget_sum_le_of_uniform
    (X P Y Rmax : ℕ) (z : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)))
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y z r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y z r) ≤ 10 * C := by
  have hsum : (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y z r) ≤
      ∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hB r hr
  have hq : 0 ≤ C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    positivity
  have hsumConst :
      (∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) =
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := by
    simp [Finset.sum_const]
  have hmul := mul_le_mul_of_nonneg_right hR hq
  rw [hsumConst] at hsum
  calc
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y z r) ≤
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hsum
    _ ≤ (10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hmul
    _ = 10 * C := by
      field_simp [hlogX.ne', hloglog.ne']

theorem sourceExponentLargeBrunBudget_sum_le_of_uniform_variable_z
    (X P Y Rmax : ℕ) (z : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)))
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤ 10 * C := by
  have hsum : (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤
      ∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hB r hr
  have hq : 0 ≤ C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    positivity
  have hsumConst :
      (∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) =
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := by
    simp [Finset.sum_const]
  have hmul := mul_le_mul_of_nonneg_right hR hq
  rw [hsumConst] at hsum
  calc
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hsum
    _ ≤ (10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hmul
    _ = 10 * C := by
      field_simp [hlogX.ne', hloglog.ne']

/- A ceiling-tolerant variant for the exact `Nat.ceil` exponent range.  The extra `+1` is the
   unavoidable rounding cost and is retained explicitly instead of silently assuming integrality. -/
theorem sourceExponentLargeBrunBudget_sum_le_of_uniform_variable_z_le_add_one
    (X P Y Rmax : ℕ) (z : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) + 1)
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤
        (10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * C := by
  have hsum : (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤
      ∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hB r hr
  have hq : 0 ≤ C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    positivity
  have hsumConst :
      (∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) =
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := by
    simp [Finset.sum_const]
  have hmul := mul_le_mul_of_nonneg_right hR hq
  rw [hsumConst] at hsum
  calc
    (∑ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y (z r) r) ≤
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hsum
    _ ≤ (10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) + 1) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hmul
    _ = (10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * C := by
      field_simp [hlogX.ne', hloglog.ne']

theorem dyadicEndpointLargeHighPower_mass_le_of_uniform_source_large_budget
    (X P Y Rmax : ℕ) (hP : 1 < P) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (hPupper : ∀ r ∈ Finset.range Rmax, 0 < r →
      (P : ℝ) < ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹))
    (z : ℝ) (hz : 1 < z) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)))
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentLargeBrunBudget X P Y z r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (10 * C) := by
  have hmass := dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_range
    X P Y Rmax hP hY hYlt hExp hPupper z hz
  have hsum := sourceExponentLargeBrunBudget_sum_le_of_uniform
    X P Y Rmax z C hC hlogX hloglog hR hB
  exact hmass.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

noncomputable def sourceExponentBrunBudget
    (X Y : ℕ) (z : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else
    (2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
        ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z +
      6 * z * (1 + Real.log z) ^ 3) /
      ((Y : ℝ) ^ ((r : ℝ)⁻¹))

theorem sourceExponentBrunBudget_nonneg
    (X Y : ℕ) (hY : 0 < Y) (hYle : Y ≤ 2 * X)
    (z : ℝ) (hz : 1 < z) (r : ℕ) :
    0 ≤ sourceExponentBrunBudget X Y z r := by
  by_cases hr0 : r = 0
  · simp [sourceExponentBrunBudget, hr0]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
    have hYleR : (Y : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast hYle
    have hpow : (Y : ℝ) ^ ((r : ℝ)⁻¹) ≤
        ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hYleR (inv_pos.mpr hrR).le
    have hdiff : 0 ≤ ((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹) -
        (Y : ℝ) ^ ((r : ℝ)⁻¹) := sub_nonneg.mpr hpow
    have hlog : 0 < Real.log z := Real.log_pos hz
    have hmain : 0 ≤
        2 * ((((2 * X : ℕ) : ℝ) ^ ((r : ℝ)⁻¹)) -
          ((Y : ℝ) ^ ((r : ℝ)⁻¹))) / Real.log z := by
      positivity
    have herror : 0 ≤ 6 * z * (1 + Real.log z) ^ 3 := by
      positivity
    have hden : 0 < (Y : ℝ) ^ ((r : ℝ)⁻¹) :=
      Real.rpow_pos_of_pos hYpos _
    rw [sourceExponentBrunBudget, ite_eq_right hr0]
    exact div_nonneg (add_nonneg hmain herror) hden.le

/- Finite summation shell for the sharp source estimate.  If every exponent layer costs at most
   `C * log log X / log X` and the range has length at most `10 log X/log log X`, the complete
   Brun budget is bounded by the constant `10 C`.  The analytic work is intentionally isolated in
   the per-layer hypothesis `hB` and the range certificate `hR`. -/
theorem sourceExponentBrunBudget_sum_le_of_uniform
    (X Y Rmax : ℕ) (z : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)))
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentBrunBudget X Y z r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ r ∈ Finset.range Rmax, sourceExponentBrunBudget X Y z r) ≤ 10 * C := by
  have hsum : (∑ r ∈ Finset.range Rmax,
      sourceExponentBrunBudget X Y z r) ≤
      ∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hB r hr
  have hq : 0 ≤ C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
    positivity
  have hsumConst :
      (∑ r ∈ Finset.range Rmax,
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) =
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := by
    simp [Finset.sum_const]
  have hmul := mul_le_mul_of_nonneg_right hR hq
  rw [hsumConst] at hsum
  calc
    (∑ r ∈ Finset.range Rmax, sourceExponentBrunBudget X Y z r) ≤
        (Rmax : ℝ) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hsum
    _ ≤ (10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) *
          (C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) := hmul
    _ = 10 * C := by
      field_simp [hlogX.ne', hloglog.ne']

theorem dyadicEndpointLargeHighPower_mass_le_of_uniform_source_budget
    (X P Y Rmax : ℕ) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (z : ℝ) (hz : 1 < z) (C : ℝ) (hC : 0 ≤ C)
    (hlogX : 0 < Real.log (X : ℝ))
    (hloglog : 0 < Real.log (Real.log (X : ℝ)))
    (hR : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)))
    (hB : ∀ r ∈ Finset.range Rmax,
      sourceExponentBrunBudget X Y z r ≤
        C * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (10 * C) := by
  have hmass :
      (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) *
          (∑ r ∈ Finset.range Rmax, sourceExponentBrunBudget X Y z r) := by
    apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_interval_budget
      X P Y Rmax (sourceExponentBrunBudget X Y z) hExp
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp [sourceExponentBrunBudget, sourceExponentInterval_zero_empty X Y hY]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hbrun := sourceExponentInterval_reciprocal_mass_le_brun
        X Y r hrpos hY hYlt z hz
      simpa [sourceExponentBrunBudget, hr0] using hbrun
  have hsum := sourceExponentBrunBudget_sum_le_of_uniform
    X Y Rmax z C hC hlogX hloglog hR hB
  exact hmass.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

theorem dyadicEndpointLargeHighPower_mass_le_source_brun_budget_of_log_range
    (X P Y : ℕ) (hP : 1 < P) (hX : 1 < 2 * X)
    (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range
          (Nat.ceil (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))),
          sourceExponentBrunBudget X Y z r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_interval_budget
    X P Y (Nat.ceil (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ)))
    (sourceExponentBrunBudget X Y z)
    (dyadicPrimeLargeHighPower_natLog_lt_ceil_log_ratio X P Y hP hX)
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp [sourceExponentBrunBudget, sourceExponentInterval_zero_empty X Y hY]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    simpa [sourceExponentBrunBudget, hr0] using
      (sourceExponentInterval_reciprocal_mass_le_brun X Y r hrpos hY hYlt z hz)

theorem dyadicEndpointLargeHighPower_mass_le_source_brun_budget
    (X P Y : ℕ) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range (Nat.log 2 (2 * X) + 1),
          sourceExponentBrunBudget X Y z r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_interval_budget
    X P Y (sourceExponentBrunBudget X Y z)
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp [sourceExponentBrunBudget, sourceExponentInterval_zero_empty X Y hY]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    simpa [sourceExponentBrunBudget, hr0] using
      (sourceExponentInterval_reciprocal_mass_le_brun X Y r hrpos hY hYlt z hz)

theorem dyadicEndpointLargeHighPower_mass_le_source_brun_budget_of_range
    (X P Y Rmax : ℕ) (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (z : ℝ) (hz : 1 < z) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        (∑ r ∈ Finset.range Rmax, sourceExponentBrunBudget X Y z r) := by
  apply dyadicEndpointLargeHighPower_mass_le_of_exponent_range_interval_budget
    X P Y Rmax (sourceExponentBrunBudget X Y z) hExp
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp [sourceExponentBrunBudget, sourceExponentInterval_zero_empty X Y hY]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    simpa [sourceExponentBrunBudget, hr0] using
      (sourceExponentInterval_reciprocal_mass_le_brun X Y r hrpos hY hYlt z hz)

theorem dyadicEndpointLargeHighPower_mass_le_dyadic_brun_budget
    (X P Y : ℕ) (hm : 10 ≤ Nat.log 16 (2 * X) + 1) :
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) * (harmonic (Nat.log 16 (2 * X) + 1) : ℝ) + 324) := by
  have hcover := dyadicEndpointLargeHighPower_mass_le_dyadic_cover X P Y
  have hbudget := dyadicDisjointPrimeFamily_mass_le_harmonic_brun
    (Nat.log 16 (2 * X) + 1) hm
  have hcoef : 0 ≤ 4 * (X : ℝ) := by positivity
  calc
    (∑ p ∈ dyadicPrimeLargeHighPowerSet X P Y, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) *
          (∑ i ∈ Finset.range (Nat.log 16 (2 * X) + 1),
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) := hcover
    _ = (4 * (X : ℝ)) *
        (∑ p ∈ dyadicDisjointPrimeFamily (Nat.log 16 (2 * X) + 1),
          ((p : ℝ)⁻¹)) := by
      rw [dyadicDisjointPrimeFamily_mass_eq]
    _ ≤ (4 * (X : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) * (harmonic (Nat.log 16 (2 * X) + 1) : ℝ) + 324) := by
      exact mul_le_mul_of_nonneg_left hbudget hcoef

theorem dyadicPrimeSmallPrimeSet_subset_primesLE (X P : ℕ) :
    dyadicPrimeSmallPrimeSet X P ⊆ Nat.primesLE P := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpprime := (Finset.mem_filter.mp hp'.1).2
  exact Nat.mem_primesLE.mpr ⟨hp'.2, hpprime⟩

/- Finite source-shaped version of equation (22)'s elementary reduction.  Since every endpoint
   power is at most `2X`, the weight is at most `4X/p`; only the reciprocal-prime mass below the
   chosen base cutoff remains to be estimated analytically. -/
theorem dyadicEndpointSmallPrime_mass_le_reciprocal_mass
    (X P : ℕ) (hX : 0 < X) :
    (∑ p ∈ dyadicPrimeSmallPrimeSet X P, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) * (∑ p ∈ Nat.primesLE P, ((p : ℝ)⁻¹)) := by
  have hpoint : ∀ p ∈ dyadicPrimeSmallPrimeSet X P,
      dyadicEndpointWeight X p ≤ (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hp'.1
    have hpprime := hpbase.2
    have hp0 : 0 < p := hpprime.pos
    have hpow : p ^ Nat.log p (2 * X) ≤ 2 * X :=
      Nat.pow_log_le_self p (by omega)
    have hpowR : ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) ≤ (2 * X : ℝ) := by
      exact_mod_cast hpow
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    unfold dyadicEndpointWeight
    have hdiv := div_le_div_of_nonneg_right hpowR (le_of_lt hpR)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) ≤
          2 * ((2 * X : ℝ) / (p : ℝ)) := hmul
      _ = (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
        simp [div_eq_mul_inv]
        ring
  calc
    (∑ p ∈ dyadicPrimeSmallPrimeSet X P, dyadicEndpointWeight X p) ≤
        ∑ p ∈ dyadicPrimeSmallPrimeSet X P,
          (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ ≤ (4 * (X : ℝ)) * (∑ p ∈ Nat.primesLE P, ((p : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (dyadicPrimeSmallPrimeSet_subset_primesLE X P)
      intro p hp hnot
      positivity

/- Combining the preceding source-shaped reduction with the LeanPool-backed dyadic reciprocal
   mass estimate gives the explicit nested-log budget for the whole base-prime cutoff branch. -/
theorem dyadicEndpointSmallPrime_mass_le_dyadic_log
    (X P : ℕ) (hX : 0 < X) (hP : 10 ≤ Nat.log 16 P + 1) :
    (∑ p ∈ dyadicPrimeSmallPrimeSet X P, dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 P + 1 : ℕ) : ℝ)) + 324) := by
  have hsmall := dyadicEndpointSmallPrime_mass_le_reciprocal_mass X P hX
  have hcut := primesLE_mass_le_dyadic_log P hP
  have hcoef : 0 ≤ 4 * (X : ℝ) := by positivity
  exact hsmall.trans (mul_le_mul_of_nonneg_left hcut hcoef)

/- Combined finite block budget.  This theorem deliberately keeps the low-power reciprocal mass
   and the dyadic-block harmonic budget visible, so that later work can replace only the high-branch
   coarse cover by the source's exponent-indexed Brun estimate. -/
theorem summatory_f_div_Icc_le_source_three_way_brun_budget
    (X P Y : ℕ) (hX : 0 < X)
    (hP : 10 ≤ Nat.log 16 P + 1)
    (hm : 10 ≤ Nat.log 16 (2 * X) + 1) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
      (4 * (X : ℝ)) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 P + 1 : ℕ) : ℝ)) + 324) +
        (4 * (X : ℝ)) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (harmonic (Nat.log 16 (2 * X) + 1) : ℝ) + 324) +
        (2 * (Y : ℝ)) *
          (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) := by
  have hend :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
    simpa [dyadicPrimeSet, dyadicEndpointWeight] using
      (summatory_f_div_Icc_le_two_mul_prime_power_weight X hX)
  rw [dyadic_endpoint_weight_source_three_way_split] at hend
  have hsmall := dyadicEndpointSmallPrime_mass_le_dyadic_log X P hX hP
  have hlow := dyadicEndpointLargeLowPower_mass_le_cutoff_reciprocal_mass X P Y
  have hhigh := dyadicEndpointLargeHighPower_mass_le_dyadic_brun_budget X P Y hm
  have hsum := add_le_add (add_le_add hsmall hhigh) hlow
  exact hend.trans (hsum.trans_eq (by ring))

/- Source-aligned dyadic block bound using the truncated exponent range.  Once an analytic proof
   supplies `hExp` and estimates the displayed budget sum, this theorem replaces the coarse
   base-16 high-branch term in the earlier three-way bound. -/
theorem summatory_f_div_Icc_le_source_three_way_source_brun_budget
    (X P Y Rmax : ℕ) (hX : 0 < X)
    (hP : 10 ≤ Nat.log 16 P + 1)
    (hY : 0 < Y) (hYlt : Y < 2 * X)
    (hExp : ∀ p ∈ dyadicPrimeLargeHighPowerSet X P Y,
      Nat.log p (2 * X) < Rmax)
    (z : ℝ) (hz : 1 < z) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
      (4 * (X : ℝ)) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 P + 1 : ℕ) : ℝ)) + 324) +
        (2 * (Y : ℝ)) *
          (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) +
        (4 * (X : ℝ)) *
          (∑ r ∈ Finset.range Rmax, sourceExponentBrunBudget X Y z r) := by
  have hend :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
    simpa [dyadicPrimeSet, dyadicEndpointWeight] using
      (summatory_f_div_Icc_le_two_mul_prime_power_weight X hX)
  rw [dyadic_endpoint_weight_source_three_way_split] at hend
  have hsmall := dyadicEndpointSmallPrime_mass_le_dyadic_log X P hX hP
  have hlow := dyadicEndpointLargeLowPower_mass_le_cutoff_reciprocal_mass X P Y
  have hhigh := dyadicEndpointLargeHighPower_mass_le_source_brun_budget_of_range
    X P Y Rmax hY hYlt hExp z hz
  have hsum := add_le_add (add_le_add hsmall hlow) hhigh
  exact hend.trans (by simpa [add_assoc, add_left_comm, add_comm] using hsum)

/- Canonical integer version of the paper's base-prime cutoff `(log X)^10`.  The floor is taken
   in `ℕ`, so every subsequent finite prime set remains an ordinary `Finset ℕ`. -/
noncomputable def sourceBasePrimeCutoff (X : ℕ) : ℕ :=
  Nat.floor ((Real.log (X : ℝ)) ^ (10 : ℕ))

theorem tendsto_sourceBasePrimeCutoff :
    Tendsto sourceBasePrimeCutoff atTop atTop := by
  unfold sourceBasePrimeCutoff
  exact (tendsto_nat_floor_atTop (α := ℝ)).comp
    ((tendsto_pow_atTop (n := 10) (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/- The floor in the canonical cutoff does not spoil the elementary lower bound needed for the
   source exponent range: eventually the cutoff dominates `log X` itself.  We use `ceil (log X)`
   as the integer witness and the coarse inequality `log X + 1 ≤ (log X)^10` once `log X ≥ 2`. -/
theorem eventually_source_log_le_cutoff :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ≤ (sourceBasePrimeCutoff X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ))] with X hL
  let L : ℝ := Real.log (X : ℝ)
  have hLtwo : (2 : ℝ) ≤ L := by simpa [L] using hL
  have hLone : (1 : ℝ) ≤ L := le_trans (by norm_num) hLtwo
  have hLnonneg : 0 ≤ L := by linarith
  have hLsq : L + 1 ≤ L ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (L - 1)]
  have hLpow8 : (1 : ℝ) ≤ L ^ (8 : ℕ) := one_le_pow₀ hLone
  have hLsqnonneg : 0 ≤ L ^ (2 : ℕ) := by positivity
  have hLsqpow : L ^ (2 : ℕ) ≤ L ^ (10 : ℕ) := by
    calc
      L ^ (2 : ℕ) = L ^ (2 : ℕ) * 1 := by ring
      _ ≤ L ^ (2 : ℕ) * L ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left hLpow8 hLsqnonneg
      _ = L ^ (10 : ℕ) := by ring
  have hLpow : L + 1 ≤ L ^ (10 : ℕ) := hLsq.trans hLsqpow
  have hceil : (Nat.ceil L : ℝ) < L + 1 :=
    Nat.ceil_lt_add_one hLnonneg
  have hceilpow : (Nat.ceil L : ℝ) ≤ L ^ (10 : ℕ) :=
    (hceil.trans_le hLpow).le
  have hnat : Nat.ceil L ≤ sourceBasePrimeCutoff X := by
    unfold sourceBasePrimeCutoff
    exact Nat.le_floor hceilpow
  have hcast : (Nat.ceil L : ℝ) ≤ (sourceBasePrimeCutoff X : ℝ) := by
    exact_mod_cast hnat
  exact (Nat.le_ceil L).trans hcast

/- A stronger floor-cutoff estimate used by the cubic Brun-error bound.  The tenth power in the
   source cutoff dominates the eighth power after the natural floor, so the estimate is uniform in
   the exponent layer. -/
theorem eventually_source_log_pow8_le_cutoff :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (8 : ℕ) ≤ (sourceBasePrimeCutoff X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (4 : ℝ))] with X hL
  let L : ℝ := Real.log (X : ℝ)
  have hLfour : (4 : ℝ) ≤ L := by simpa [L] using hL
  have hLnonneg : 0 ≤ L := by linarith
  have hL8nonneg : 0 ≤ L ^ (8 : ℕ) := by positivity
  have hL8pos : 0 < L ^ (8 : ℕ) := by positivity
  have hL8one : 1 ≤ L ^ (8 : ℕ) := by
    exact one_le_pow₀ (by linarith)
  have hL2 : 2 ≤ L ^ (2 : ℕ) := by
    nlinarith [sq_nonneg L]
  have hL10 : L ^ (8 : ℕ) + 1 ≤ L ^ (10 : ℕ) := by
    calc
      L ^ (8 : ℕ) + 1 ≤ L ^ (8 : ℕ) + L ^ (8 : ℕ) := by linarith
      _ = L ^ (8 : ℕ) * 2 := by ring
      _ ≤ L ^ (8 : ℕ) * L ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hL2 hL8nonneg
      _ = L ^ (10 : ℕ) := by ring
  have hceil : (Nat.ceil (L ^ (8 : ℕ)) : ℝ) < L ^ (8 : ℕ) + 1 :=
    Nat.ceil_lt_add_one hL8nonneg
  have hceilpow : (Nat.ceil (L ^ (8 : ℕ)) : ℝ) ≤ L ^ (10 : ℕ) :=
    (hceil.trans_le hL10).le
  have hnat : Nat.ceil (L ^ (8 : ℕ)) ≤ sourceBasePrimeCutoff X := by
    unfold sourceBasePrimeCutoff
    exact Nat.le_floor hceilpow
  have hcast : (Nat.ceil (L ^ (8 : ℕ)) : ℝ) ≤ (sourceBasePrimeCutoff X : ℝ) := by
    exact_mod_cast hnat
  exact (Nat.le_ceil (L ^ (8 : ℕ))).trans (by simpa [L] using hcast)

/- Local forward version of the harmless tenth-power comparison.  The public theorem with the
   shorter name appears below as part of the source-range API; this early copy keeps the uniform
   error corollary independent of declaration order. -/
theorem eventually_source_log_pow_le_two_mul_pre :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (10 : ℕ) ≤ 2 * (X : ℝ) := by
  have hratio : Tendsto (fun X : ℕ ↦
      (Real.log (X : ℝ)) ^ (10 : ℕ) / (X : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 10 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hlt : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (10 : ℕ) / (X : ℝ) < 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with X hX hXp
  have hXpR : 0 < (X : ℝ) := by exact_mod_cast hXp
  have hmul := (div_lt_iff₀ hXpR).mp hX
  linarith

/- Uniform source-cutoff corollary for the cubic Brun remainder.  The auxiliary scale `Y` may vary
   with `X`; the conclusion is uniform in every natural exponent layer, including the harmless
   `r = 0` layer (where the reciprocal root is `1`). -/
theorem eventually_source_sqrt_cubic_error_le_loglog_div_log
    (Y : ℕ → ℕ)
    (hY : ∀ᶠ X : ℕ in atTop, 1 < Y X)
    (hYupper : ∀ᶠ X : ℕ in atTop, Y X ≤ 2 * X) :
    ∀ᶠ X : ℕ in atTop, ∀ r : ℕ,
      (6 * Real.sqrt (max (sourceBasePrimeCutoff X : ℝ)
          ((Y X : ℝ) ^ ((r : ℝ)⁻¹))) *
          (1 + Real.log (Real.sqrt (max (sourceBasePrimeCutoff X : ℝ)
            ((Y X : ℝ) ^ ((r : ℝ)⁻¹))))) ^ 3) /
        max (sourceBasePrimeCutoff X : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)) ≤
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
  have hL : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
    exact h
  have hLL : ∀ᶠ X : ℕ in atTop,
      48 ≤ Real.log (Real.log (X : ℝ)) := by
    have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (48 : ℝ))
    exact h
  have hlogXpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    exact h
  have hXtwo : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hPupper := eventually_source_log_pow_le_two_mul_pre
  have hPsmall := eventually_source_log_pow8_le_cutoff
  filter_upwards [hL, hLL, hlogXpos, hXtwo, hY, hYupper, hPupper, hPsmall]
    with X hLX hLLX hLpos hX2 hYX hYXupper hPup hPsmall
  intro r
  let A : ℝ := max (sourceBasePrimeCutoff X : ℝ)
    ((Y X : ℝ) ^ ((r : ℝ)⁻¹))
  have hAlower : (Real.log (X : ℝ)) ^ (8 : ℕ) ≤ A := by
    exact hPsmall.trans (le_max_left _ _)
  have hPfloor : (sourceBasePrimeCutoff X : ℝ) ≤
      (Real.log (X : ℝ)) ^ (10 : ℕ) := by
    unfold sourceBasePrimeCutoff
    exact Nat.floor_le (by positivity)
  have hPupperR : (sourceBasePrimeCutoff X : ℝ) ≤ 2 * (X : ℝ) :=
    hPfloor.trans hPup
  have hYupperR : (Y X : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hYXupper
  have hα1 : (r : ℝ)⁻¹ ≤ 1 := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · apply inv_le_one_of_one_le₀
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr0)
  have hYoneR : (1 : ℝ) ≤ (Y X : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hYX)
  have hroot_le_Y : (Y X : ℝ) ^ ((r : ℝ)⁻¹) ≤ (Y X : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hYoneR hα1
  have hrootupper : (Y X : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (X : ℝ) :=
    hroot_le_Y.trans hYupperR
  have hAupper : A ≤ 2 * (X : ℝ) := by
    exact max_le hPupperR hrootupper
  have hL8pos : 0 < (Real.log (X : ℝ)) ^ (8 : ℕ) := by positivity
  have hApos : 0 < A := lt_of_lt_of_le hL8pos hAlower
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hX2
  have hlogA : Real.log A ≤ 2 * Real.log (X : ℝ) := by
    have hlog2X' : Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
      rw [Real.log_mul (by norm_num) (by exact_mod_cast (show X ≠ 0 by omega))]
      nlinarith
    exact (Real.log_le_log hApos hAupper).trans hlog2X'
  have herr := sqrt_cubic_error_le_of_log_bounds hLX hAlower hlogA
  have hquot : (48 : ℝ) / Real.log (X : ℝ) ≤
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) :=
    div_le_div_of_nonneg_right hLLX (le_of_lt hLpos)
  simpa [A] using herr.trans hquot

/- A complete per-layer reduction for the source-shaped Brun budget.  The hypotheses are now only
   scalar eventual estimates on `Y`: its size window, the relative ratio `(2X/Y)-1`, and the lower
   logarithmic scale.  Under these elementary inputs the budget is uniformly
   `(8K+1) log log X / log X`; the prime-distribution content has been isolated in the earlier
   finite Brun theorem. -/
theorem eventually_source_sqrt_brun_budget_le_uniform
    (Y : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ᶠ X : ℕ in atTop, 1 < Y X)
    (hYlt : ∀ᶠ X : ℕ in atTop, Y X < 2 * X)
    (hYratio : ∀ᶠ X : ℕ in atTop,
      ((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1 ≤
        K * Real.log (Real.log (X : ℝ)))
    (hYlog : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ≤ 2 * Real.log (Y X : ℝ)) :
    ∀ᶠ X : ℕ in atTop, ∀ r : ℕ,
      sourceExponentLargeBrunBudget X (sourceBasePrimeCutoff X) (Y X)
          (Real.sqrt (max (sourceBasePrimeCutoff X : ℝ)
            ((Y X : ℝ) ^ ((r : ℝ)⁻¹)))) r ≤
        (8 * K + 1) * Real.log (Real.log (X : ℝ)) /
          Real.log (X : ℝ) := by
  have hL : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
    exact h
  have hLL : ∀ᶠ X : ℕ in atTop,
      48 ≤ Real.log (Real.log (X : ℝ)) := by
    have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (48 : ℝ))
    exact h
  have hlogXpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    exact h
  have hP2 : ∀ᶠ X : ℕ in atTop, 2 ≤ sourceBasePrimeCutoff X :=
    (tendsto_sourceBasePrimeCutoff).eventually (eventually_ge_atTop 2)
  have hErr := eventually_source_sqrt_cubic_error_le_loglog_div_log Y
    hY (hYlt.mono (fun X h ↦ Nat.le_of_lt h))
  filter_upwards [hL, hLL, hlogXpos, hP2, hY, hYlt, hYratio, hYlog, hErr]
    with X hLX hLLX hLpos hP hYX hYXlt hratio hlogY herr
  intro r
  by_cases hr0 : r = 0
  · simp [sourceExponentLargeBrunBudget, hr0]
    positivity
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hbase := sourceExponentLargeBrunBudget_le_log_ratio_plus_sqrt_error
      X (sourceBasePrimeCutoff X) (Y X) r hP hrpos hYX hYXlt
    have hlogYpos : 0 < Real.log (Y X : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hYX)
    have hmain0 : 4 * ((((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1) /
        Real.log (Y X : ℝ)) ≤
        4 * (K * Real.log (Real.log (X : ℝ)) / Real.log (Y X : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hratio hlogYpos.le) (by norm_num)
    have hcoef : 0 ≤ 4 * K * Real.log (Real.log (X : ℝ)) := by positivity
    have hcross : (4 * K * Real.log (Real.log (X : ℝ))) *
        Real.log (X : ℝ) ≤
        (2 * (4 * K * Real.log (Real.log (X : ℝ)))) * Real.log (Y X : ℝ) := by
      calc
        (4 * K * Real.log (Real.log (X : ℝ))) * Real.log (X : ℝ) ≤
            (4 * K * Real.log (Real.log (X : ℝ))) *
              (2 * Real.log (Y X : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogY hcoef
        _ = (2 * (4 * K * Real.log (Real.log (X : ℝ)))) *
              Real.log (Y X : ℝ) := by ring
    have hdiv : (4 * K * Real.log (Real.log (X : ℝ))) /
        Real.log (Y X : ℝ) ≤
        (2 * (4 * K * Real.log (Real.log (X : ℝ)))) /
          Real.log (X : ℝ) := by
      exact (div_le_div_iff₀ hlogYpos hLpos).2 hcross
    have hmain : 4 * ((((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1) /
        Real.log (Y X : ℝ)) ≤
        8 * K * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
      have htmp := hmain0.trans (by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv)
      calc
        4 * ((((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1) /
            Real.log (Y X : ℝ)) ≤
            K * (2 * (4 * ((Real.log (X : ℝ))⁻¹ *
              Real.log (Real.log (X : ℝ))))) := htmp
        _ = 8 * K * Real.log (Real.log (X : ℝ)) /
            Real.log (X : ℝ) := by
          field_simp [hLpos.ne']
          ring
    have herrX := herr r
    have hsum := add_le_add hmain herrX
    have htarget :
        8 * K * Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) +
          Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) =
        (8 * K + 1) * Real.log (Real.log (X : ℝ)) /
          Real.log (X : ℝ) := by
      field_simp [hLpos.ne']
    exact hbase.trans (hsum.trans_eq htarget)

/- Uniform high-branch mass reduction with the source cutoff.  The exact logarithmic exponent
   range is retained, while the ceiling is paid for by the explicit `+1` in the finite sum
   lemma.  The remaining analytic input is the scalar choice of `Y`, encoded by the four
   eventual hypotheses below. -/
theorem eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget
    (Y : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ᶠ X : ℕ in atTop, 1 < Y X)
    (hYlt : ∀ᶠ X : ℕ in atTop, Y X < 2 * X)
    (hYratio : ∀ᶠ X : ℕ in atTop,
      ((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1 ≤
        K * Real.log (Real.log (X : ℝ)))
    (hYlog : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ≤ 2 * Real.log (Y X : ℝ)) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeLargeHighPowerSet X (sourceBasePrimeCutoff X) (Y X),
        dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * (8 * K + 1)) := by
  have hL : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 0 < Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))
  have hX2 : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hP2 : ∀ᶠ X : ℕ in atTop, 2 ≤ sourceBasePrimeCutoff X :=
    (tendsto_sourceBasePrimeCutoff).eventually (eventually_ge_atTop 2)
  have hPlog : ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) ≤
        Real.log (sourceBasePrimeCutoff X : ℝ) := by
    have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_source_log_le_cutoff] with X hL hcut
    have hlogXpos : 0 < Real.log (X : ℝ) := by linarith
    exact Real.log_le_log hlogXpos hcut
  have hlog2 : ∀ᶠ X : ℕ in atTop,
      Real.log ((2 * X : ℕ) : ℝ) ≤ 10 * Real.log (X : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ X by omega)
    have hlog2le : Real.log (2 : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hX
    rw [show ((2 * X : ℕ) : ℝ) = (2 : ℝ) * (X : ℝ) by norm_num,
      Real.log_mul (by norm_num) hXpos.ne']
    nlinarith
  have hB := eventually_source_sqrt_brun_budget_le_uniform Y hK hY hYlt hYratio hYlog
  filter_upwards [hL, hLL, hX2, hP2, hPlog, hlog2, hY, hYlt, hB]
    with X hLX hLLX hX2X hP2X hPlogX hlog2X hYX hYXlt hBX
  let P : ℕ := sourceBasePrimeCutoff X
  let Rmax : ℕ := Nat.ceil
    (Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ))
  let z : ℕ → ℝ := fun r ↦
    Real.sqrt (max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)))
  have hPgt : 1 < P := by
    dsimp [P]
    omega
  have hXgt : 1 < 2 * X := by omega
  have hYpos : 0 < Y X := by omega
  have hYltX : Y X < 2 * X := hYXlt
  have hlogPpos : 0 < Real.log (P : ℝ) :=
    lt_of_lt_of_le hLLX hPlogX
  have hnum : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * X by omega)
  have hratio : Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) := by
    have hratio0 := div_le_div_of_nonneg_right hlog2X (le_of_lt hlogPpos)
    have hratio1 : (10 * Real.log (X : ℝ)) / Real.log (P : ℝ) ≤
        (10 * Real.log (X : ℝ)) / Real.log (Real.log (X : ℝ)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hPlogX
    exact hratio0.trans hratio1
  have hRceil : (Rmax : ℝ) ≤
      10 * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) + 1 := by
    have hratio0 : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) / Real.log (P : ℝ) :=
      div_nonneg hnum (le_of_lt hlogPpos)
    have hceil := Nat.ceil_lt_add_one hratio0
    have hadd := add_le_add hratio (le_refl (1 : ℝ))
    exact le_of_lt (hceil.trans_le hadd)
  have hz : ∀ r : ℕ, 1 < z r := by
    intro r
    dsimp [z]
    have hA2 : (2 : ℝ) ≤ max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)) := by
      have hP2R : (2 : ℝ) ≤ (P : ℝ) := by
        exact_mod_cast (show 2 ≤ P by simpa [P] using hP2X)
      exact hP2R.trans (le_max_left _ _)
    have hApos : 0 ≤ max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)) := by positivity
    have hsnonneg : 0 ≤ Real.sqrt (max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹))) :=
      Real.sqrt_nonneg _
    have hssq : (Real.sqrt (max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)))) ^ 2 =
        max (P : ℝ) ((Y X : ℝ) ^ ((r : ℝ)⁻¹)) := by
      exact Real.sq_sqrt hApos
    nlinarith
  have hsum := sourceExponentLargeBrunBudget_sum_le_of_uniform_variable_z_le_add_one
    X P (Y X) Rmax z (8 * K + 1) (by positivity) hLX hLLX hRceil (by
      intro r hr
      simpa [P, z] using hBX r)
  have hmass := dyadicEndpointLargeHighPower_mass_le_source_large_brun_budget_of_log_range_variable_z
    X P (Y X) hPgt hXgt hYpos hYltX z hz
  have hfinal := hmass.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  simpa [P, Rmax, z] using hfinal

/- A concrete, deliberately non-sharp instantiation.  Taking `Y(X)=X` discharges all four scalar
   eventual hypotheses with `K=1`; this is useful as a compile-checked sanity check for the
   abstract source-scale adapter, although it is not sufficient for the full three-way asymptotic
   because the low-power branch is then too large. -/
theorem eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget_id :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeLargeHighPowerSet X (sourceBasePrimeCutoff X) X,
        dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 9) := by
  have hX : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hL : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  have hmain := eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget
    (Y := fun X ↦ X) (K := (1 : ℝ)) (by norm_num)
    (by
      filter_upwards [hX] with X hX
      omega)
    (by
      filter_upwards [hX] with X hX
      omega)
    (by
      filter_upwards [hX, hLL] with X hX hLLX
      have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
      have hratio : ((2 * X : ℕ) : ℝ) / (X : ℝ) - 1 = 1 := by
        field_simp [hXR]
        norm_num [Nat.cast_mul]
        ring
      rw [hratio]
      simpa using hLLX)
    (by
      filter_upwards [hL] with X hLX
      linarith)
  convert hmain using 1; norm_num

/- A harmless eventual estimate for the doubled endpoint.  Together with the cutoff lemma above,
   it supplies the two real hypotheses needed by the source-shaped exponent-range corollary. -/
theorem eventually_source_log_two_mul_le_ten_log :
    ∀ᶠ X : ℕ in atTop,
      Real.log ((2 * X : ℕ) : ℝ) ≤ 10 * Real.log (X : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ X by omega)
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hX
  rw [show ((2 * X : ℕ) : ℝ) = (2 : ℝ) * (X : ℝ) by norm_num,
    Real.log_mul (by norm_num) hXpos.ne']
  nlinarith

theorem eventually_source_loglog_le_cutoff_log :
    ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) ≤
        Real.log (sourceBasePrimeCutoff X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_source_log_le_cutoff] with X hL hcut
  have hlogXpos : 0 < Real.log (X : ℝ) := by linarith
  exact Real.log_le_log hlogXpos hcut

theorem eventually_source_exponent_range (Y : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      ∀ p ∈ dyadicPrimeLargeHighPowerSet X (sourceBasePrimeCutoff X) Y,
        Nat.log p (2 * X) <
          Nat.ceil (10 * Real.log (X : ℝ) /
            Real.log (Real.log (X : ℝ))) := by
  have hlog : ∀ᶠ X : ℕ in atTop, (2 : ℝ) ≤ Real.log (X : ℝ) := by
    have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop (2 : ℝ))
  have hcutlog := eventually_source_loglog_le_cutoff_log
  have hcut2 : ∀ᶠ X : ℕ in atTop, 2 ≤ sourceBasePrimeCutoff X :=
    (tendsto_sourceBasePrimeCutoff).eventually (eventually_ge_atTop (2 : ℕ))
  have hlog2 := eventually_source_log_two_mul_le_ten_log
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog, hcutlog, hcut2, hlog2]
    with X hXnat hL hPlog hP2 hlog2X
  intro p hp
  have hPgt : 1 < sourceBasePrimeCutoff X := by omega
  have hXgt : 1 < 2 * X := by omega
  have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := by linarith
  have hloglogpos : 0 < Real.log (Real.log (X : ℝ)) := by
    apply Real.log_pos
    linarith
  exact dyadicPrimeLargeHighPower_natLog_lt_ceil_ten_log_div_loglog_of_loglog_le
    X (sourceBasePrimeCutoff X) Y hPgt hXgt hlogXnonneg hloglogpos hPlog hlog2X p hp

theorem eventually_summatory_f_div_Icc_le_source_three_way_source_cutoff
    (Y : ℕ) (hY : 0 < Y) (z : ℝ) (hz : 1 < z) :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (4 * (X : ℝ)) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) +
          (2 * (Y : ℝ)) *
            (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) +
          (4 * (X : ℝ)) *
            (∑ r ∈ Finset.range
              (Nat.ceil (10 * Real.log (X : ℝ) /
                Real.log (Real.log (X : ℝ)))),
              sourceExponentBrunBudget X Y z r) := by
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X :=
    eventually_gt_atTop (0 : ℕ)
  have hP : ∀ᶠ X : ℕ in atTop,
      10 ≤ Nat.log 16 (sourceBasePrimeCutoff X) + 1 := by
    have hcut := (tendsto_sourceBasePrimeCutoff).eventually
      (eventually_ge_atTop ((16 : ℕ) ^ 9))
    filter_upwards [hcut] with X hX
    have hP0 : sourceBasePrimeCutoff X ≠ 0 := by
      intro hzero
      simp [hzero] at hX
    have hlog : 9 ≤ Nat.log 16 (sourceBasePrimeCutoff X) := by
      apply (Nat.le_log_iff_pow_le (by norm_num) hP0).2
      exact hX
    omega
  have hYlt : ∀ᶠ X : ℕ in atTop, Y < 2 * X := by
    filter_upwards [eventually_ge_atTop (Y + 1)] with X hX
    omega
  have hExp := eventually_source_exponent_range Y
  filter_upwards [hXpos, hP, hYlt, hExp] with X hX hP hYlt hExp
  exact summatory_f_div_Icc_le_source_three_way_source_brun_budget
    X (sourceBasePrimeCutoff X)
      Y
      (Nat.ceil (10 * Real.log (X : ℝ) /
        Real.log (Real.log (X : ℝ))))
      hX hP hY hYlt hExp z hz

theorem eventually_source_log_pow_le_two_mul :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (10 : ℕ) ≤ 2 * (X : ℝ) := by
  have hratio : Tendsto (fun X : ℕ ↦
      (Real.log (X : ℝ)) ^ (10 : ℕ) / (X : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 10 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hlt : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (10 : ℕ) / (X : ℝ) < 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with X hX hXp
  have hXpR : 0 < (X : ℝ) := by exact_mod_cast hXp
  have hmul := (div_lt_iff₀ hXpR).mp hX
  linarith

theorem mem_dyadicPrimeSmallPrimeSet_of_lt_source_cutoff
    (X p : ℕ) (_hX : 0 < X)
    (hlogX : (Real.log (X : ℝ)) ^ (10 : ℕ) ≤ 2 * (X : ℝ))
    (hp : p.Prime)
    (hpLog : (p : ℝ) < (Real.log (X : ℝ)) ^ (10 : ℕ)) :
    p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X) := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    apply Finset.mem_Icc.mpr
    refine ⟨hp.two_le, ?_⟩
    have hp2Xr : (p : ℝ) ≤ (2 * X : ℝ) := hpLog.le.trans hlogX
    exact_mod_cast hp2Xr
  · unfold sourceBasePrimeCutoff
    exact Nat.le_floor hpLog.le

theorem eventually_sourceBasePrimeCutoff_log16_large :
    ∀ᶠ X : ℕ in atTop,
      10 ≤ Nat.log 16 (sourceBasePrimeCutoff X) + 1 := by
  have hcut := (tendsto_sourceBasePrimeCutoff).eventually
    (eventually_ge_atTop ((16 : ℕ) ^ 9))
  filter_upwards [hcut] with X hX
  have hP0 : sourceBasePrimeCutoff X ≠ 0 := by
    intro hzero
    simp [hzero] at hX
  have hlog : 9 ≤ Nat.log 16 (sourceBasePrimeCutoff X) := by
    apply (Nat.le_log_iff_pow_le (by norm_num) hP0).2
    exact hX
  omega

/- Eventual source-shaped form of the low endpoint-power branch.  It exposes the only remaining
   scalar factor, `Y(X)`, while replacing the reciprocal-prime mass up to `2X` by the existing
   LeanPool-backed dyadic logarithmic budget. -/
theorem eventually_dyadicEndpointLargeLowPower_mass_le_source_dyadic_log
    (Y : ℕ → ℕ) (hY : ∀ᶠ X : ℕ in atTop, 0 < Y X) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeLargeLowPowerSet X (sourceBasePrimeCutoff X) (Y X),
        dyadicEndpointWeight X p) ≤
      (2 * (Y X : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) + 324) := by
  have hM : ∀ᶠ X : ℕ in atTop,
      10 ≤ Nat.log 16 (2 * X) + 1 := by
    filter_upwards [eventually_ge_atTop ((16 : ℕ) ^ 9)] with X hX
    have hN0 : (2 * X) ≠ 0 := by omega
    have hpow : (16 : ℕ) ^ 9 ≤ 2 * X := by omega
    have hlog : 9 ≤ Nat.log 16 (2 * X) := by
      apply (Nat.le_log_iff_pow_le (by norm_num) hN0).2
      exact hpow
    omega
  filter_upwards [hY, hM] with X hYX hMX
  have hlow := dyadicEndpointLargeLowPower_mass_le_cutoff_reciprocal_mass
    X (sourceBasePrimeCutoff X) (Y X)
  have hcut := primesLE_mass_le_dyadic_log (2 * X) hMX
  exact hlow.trans (mul_le_mul_of_nonneg_left hcut (by positivity))

/- Scalar form of the low-branch reduction.  If the auxiliary scale satisfies
   `Y(X)·log log X ≤ C·X` and the reciprocal-prime mass up to `2X` is at most
   `D·log log X`, the whole low branch is bounded by `2CD·X`. -/
theorem eventually_dyadicEndpointLargeLowPower_mass_le_of_scale
    (Y : ℕ → ℕ) {C D : ℝ} (hD : 0 ≤ D)
    (hY : ∀ᶠ X : ℕ in atTop, 0 < Y X)
    (hYscale : ∀ᶠ X : ℕ in atTop,
      (Y X : ℝ) * Real.log (Real.log (X : ℝ)) ≤ C * (X : ℝ))
    (hprimeMass : ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) ≤
        D * Real.log (Real.log (X : ℝ))) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeLargeLowPowerSet X (sourceBasePrimeCutoff X) (Y X),
        dyadicEndpointWeight X p) ≤ 2 * C * D * (X : ℝ) := by
  have hL : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 0 ≤ Real.log (Real.log (X : ℝ)) := by
    exact (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (0 : ℝ)))
  filter_upwards [hY, hYscale, hprimeMass, hL, hLL] with X hYX hscale hmass hLX hLLX
  have hlow := dyadicEndpointLargeLowPower_mass_le_cutoff_reciprocal_mass
    X (sourceBasePrimeCutoff X) (Y X)
  have hfirst := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2 * (Y X : ℝ))
  have hsecond : 2 * (Y X : ℝ) * (D * Real.log (Real.log (X : ℝ))) ≤
      2 * C * D * (X : ℝ) := by
    have hscale' := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
    calc
      2 * (Y X : ℝ) * (D * Real.log (Real.log (X : ℝ))) =
          (2 * D) * ((Y X : ℝ) * Real.log (Real.log (X : ℝ))) := by ring
      _ ≤ (2 * D) * (C * (X : ℝ)) := hscale'
      _ = 2 * C * D * (X : ℝ) := by ring
  exact (hlow.trans hfirst).trans hsecond

/- Fully instantiated finite form of the source's small-prime branch.  Only the later estimate of
   the complementary large-prime branch is still outside this theorem. -/
theorem eventually_dyadicEndpointSmallPrime_mass_le_source_cutoff_log :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
      (4 * (X : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      eventually_sourceBasePrimeCutoff_log16_large] with X hX hP
  exact dyadicEndpointSmallPrime_mass_le_dyadic_log X
    (sourceBasePrimeCutoff X) (by omega) hP

/- Full eventual source-scale block inequality.  The three finite branches are now combined with
   the variable-`Y` high-branch theorem; only a later scalar estimate of the displayed budgets is
   needed to turn this certificate into the target `H(X)` asymptotic. -/
theorem eventually_summatory_f_div_Icc_le_source_three_way_uniform
    (Y : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ᶠ X : ℕ in atTop, 1 < Y X)
    (hYlt : ∀ᶠ X : ℕ in atTop, Y X < 2 * X)
    (hYratio : ∀ᶠ X : ℕ in atTop,
      ((2 * X : ℕ) : ℝ) / (Y X : ℝ) - 1 ≤
        K * Real.log (Real.log (X : ℝ)))
    (hYlog : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ≤ 2 * Real.log (Y X : ℝ)) :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (4 * (X : ℝ)) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) +
          (2 * (Y X : ℝ)) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) + 324) +
          (4 * (X : ℝ)) *
            ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * (8 * K + 1)) := by
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X := eventually_gt_atTop (0 : ℕ)
  have hsmall := eventually_dyadicEndpointSmallPrime_mass_le_source_cutoff_log
  have hlow := eventually_dyadicEndpointLargeLowPower_mass_le_source_dyadic_log Y
    (hY.mono (fun X h ↦ Nat.zero_lt_of_lt h))
  have hhigh := eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget
    Y hK hY hYlt hYratio hYlog
  filter_upwards [hXpos, hsmall, hlow, hhigh] with X hX hsmallX hlowX hhighX
  have hend :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
    simpa [dyadicPrimeSet, dyadicEndpointWeight] using
      (summatory_f_div_Icc_le_two_mul_prime_power_weight X hX)
  rw [dyadic_endpoint_weight_source_three_way_split] at hend
  have hsum := add_le_add (add_le_add hsmallX hhighX) hlowX
  exact hend.trans (hsum.trans_eq (by ring))

/- A concrete source-scale candidate.  The ceiling keeps the target an ordinary natural-valued
   function while preserving the lower bound `X/log log X` needed in the high branch. -/
noncomputable def sourceAuxScale (X : ℕ) : ℕ :=
  Nat.ceil ((X : ℝ) / Real.log (Real.log (X : ℝ)))

theorem eventually_sourceAuxScale_conditions :
    (∀ᶠ X : ℕ in atTop, 1 < sourceAuxScale X) ∧
      (∀ᶠ X : ℕ in atTop, sourceAuxScale X < 2 * X) ∧
      (∀ᶠ X : ℕ in atTop,
        ((2 * X : ℕ) : ℝ) / (sourceAuxScale X : ℝ) - 1 ≤
          2 * Real.log (Real.log (X : ℝ))) ∧
      (∀ᶠ X : ℕ in atTop,
        Real.log (X : ℝ) ≤
          2 * Real.log (sourceAuxScale X : ℝ)) := by
  have hL : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
  have hX : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hLL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  rw [← Filter.eventually_and, ← Filter.eventually_and, ← Filter.eventually_and]
  filter_upwards [hL, hX, hLL] with X hLX hXX hLLX
  let L : ℝ := Real.log (X : ℝ)
  let LL : ℝ := Real.log (Real.log (X : ℝ))
  let q : ℝ := (X : ℝ) / LL
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hLpos : 0 < L := by simpa [L] using (show (0 : ℝ) < Real.log (X : ℝ) by linarith)
  have hLLpos : 0 < LL := by simpa [LL] using (show (0 : ℝ) < Real.log (Real.log (X : ℝ)) by linarith)
  have hLfour : (4 : ℝ) ≤ L := by simpa [L] using hLX
  have hLLone : (1 : ℝ) ≤ LL := by simpa [LL] using hLLX
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos hXreal hLLpos
  have hqceil : q ≤ (sourceAuxScale X : ℝ) := by
    dsimp [sourceAuxScale, q, LL]
    exact Nat.le_ceil _
  have hceilq : (sourceAuxScale X : ℝ) < q + 1 := by
    dsimp [sourceAuxScale, q, LL]
    exact Nat.ceil_lt_add_one hqpos.le
  have hLLltX : LL < (X : ℝ) := by
    have hlogL : LL ≤ L := by
      dsimp [LL, L]
      exact Real.log_le_self (by positivity)
    have hlogXlt : L < (X : ℝ) := by
      dsimp [L]
      exact (Real.log_lt_sub_one_of_pos hXreal (by exact_mod_cast (show X ≠ 1 by omega))).trans
        (by linarith)
    exact hlogL.trans_lt hlogXlt
  have hqone : (1 : ℝ) < q := by
    apply (lt_div_iff₀ hLLpos).2
    simpa using hLLltX
  have hYone : 1 < sourceAuxScale X := by
    exact_mod_cast (show (1 : ℝ) < (sourceAuxScale X : ℝ) from hqone.trans_le hqceil)
  have hqleX : q ≤ (X : ℝ) := by
    apply (div_le_iff₀ hLLpos).2
    nlinarith [hLLone]
  have hYlt : sourceAuxScale X < 2 * X := by
    have hXplus : (X : ℝ) + 1 ≤ (2 * X : ℕ) := by
      exact_mod_cast (show X + 1 ≤ 2 * X by omega)
    have hYreal : (sourceAuxScale X : ℝ) < (2 * X : ℕ) := by
      have hqplus : q + 1 ≤ (X : ℝ) + 1 := add_le_add hqleX (le_refl (1 : ℝ))
      exact hceilq.trans_le (hqplus.trans hXplus)
    exact_mod_cast hYreal
  have hYpos : 0 < (sourceAuxScale X : ℝ) := by positivity
  have hratio : ((2 * X : ℕ) : ℝ) / (sourceAuxScale X : ℝ) - 1 ≤ 2 * LL := by
    have hmul : (X : ℝ) ≤ LL * (sourceAuxScale X : ℝ) := by
      have := (div_le_iff₀ hLLpos).mp hqceil
      nlinarith
    have hdiv : ((2 * X : ℕ) : ℝ) / (sourceAuxScale X : ℝ) ≤ 2 * LL := by
      apply (div_le_iff₀ hYpos).2
      rw [show ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) by norm_num]
      nlinarith [hmul]
    linarith [hdiv]
  have hsqrt : 2 ≤ Real.sqrt L := by
    have hsq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    have hsnonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    nlinarith
  have hlogsqrt : Real.log (Real.sqrt L) = LL / 2 := by
    dsimp [LL]
    exact Real.log_sqrt hLpos.le
  have hlog_sqrt_bound : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := by
    exact Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hLpos)
  have hLLhalf : LL ≤ L / 2 := by
    have hsq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    nlinarith [sq_nonneg (Real.sqrt L - 2)]
  have hlogLL : Real.log LL ≤ LL := Real.log_le_self hLLpos.le
  have hlogq : Real.log q = L - Real.log LL := by
    dsimp [q]
    rw [Real.log_div hXreal.ne' hLLpos.ne']
  have hlogqLower : L / 2 ≤ Real.log q := by
    rw [hlogq]
    nlinarith
  have hlogY : Real.log q ≤ Real.log (sourceAuxScale X : ℝ) := by
    exact Real.log_le_log hqpos hqceil
  have hYlog : Real.log (X : ℝ) ≤ 2 * Real.log (sourceAuxScale X : ℝ) := by
    have hlogqLower' : L / 2 ≤ Real.log (sourceAuxScale X : ℝ) :=
      hlogqLower.trans hlogY
    dsimp [L] at hlogqLower'
    nlinarith
  exact ⟨hYone, hYlt, by simpa [LL] using hratio, hYlog⟩

theorem eventually_sourceAuxScale_mul_loglog_le_two_mul_self :
    ∀ᶠ X : ℕ in atTop,
      (sourceAuxScale X : ℝ) * Real.log (Real.log (X : ℝ)) ≤
        2 * (X : ℝ) := by
  have hL : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
  have hX : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hLL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hL, hX, hLL] with X hLX hXX hLLX
  let L : ℝ := Real.log (X : ℝ)
  let LL : ℝ := Real.log (Real.log (X : ℝ))
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hLpos : 0 < L := by simpa [L] using (show (0 : ℝ) < Real.log (X : ℝ) by linarith)
  have hLLpos : 0 < LL := by simpa [LL] using (show (0 : ℝ) < Real.log (Real.log (X : ℝ)) by linarith)
  have hLLltX : LL < (X : ℝ) := by
    have hlogL : LL ≤ L := by
      dsimp [LL, L]
      exact Real.log_le_self (by positivity)
    have hlogXlt : L < (X : ℝ) := by
      dsimp [L]
      exact (Real.log_lt_sub_one_of_pos hXreal
        (by exact_mod_cast (show X ≠ 1 by omega))).trans (by linarith)
    exact hlogL.trans_lt hlogXlt
  have hceil : (sourceAuxScale X : ℝ) <
      (X : ℝ) / LL + 1 := by
    dsimp [sourceAuxScale, LL]
    exact Nat.ceil_lt_add_one (by positivity)
  have hmul : (sourceAuxScale X : ℝ) * LL < (X : ℝ) + LL := by
    have hmul' := mul_lt_mul_of_pos_right hceil hLLpos
    field_simp [hLLpos.ne'] at hmul'
    nlinarith
  have htarget : (sourceAuxScale X : ℝ) * LL ≤ 2 * (X : ℝ) := by
    nlinarith [hLLltX]
  simpa [LL] using htarget

/- The dyadic logarithmic index is no larger than a constant multiple of the source
   `log log` scale.  This is the scalar comparison needed to turn the existing
   `primesLE_mass_le_dyadic_log` estimate into a `D · log log X` hypothesis. -/
theorem eventually_natLog16_two_mul_log_index_le_two_loglog :
    ∀ᶠ X : ℕ in atTop,
      Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ) ≤
        2 * Real.log (Real.log (X : ℝ)) := by
  have hX : ∀ᶠ X : ℕ in atTop, 4 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))
  have hXnat : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  filter_upwards [hX, hXnat] with X hLX hXX
  have hXpos : 0 < X := by omega
  have hNpos : 0 < 2 * X := by omega
  have hNone : (2 * X) ≠ 0 := by omega
  let L : ℝ := Real.log (X : ℝ)
  let LN : ℝ := Real.log ((2 * X : ℕ) : ℝ)
  let LL : ℝ := Real.log L
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLX' : (4 : ℝ) ≤ L := by simpa [L] using hLX
  have hLNpos : 0 < LN := by
    dsimp [LN]
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hlog16 : (2 : ℝ) ≤ Real.log (16 : ℝ) := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    calc
      (2 : ℝ) = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 4 * Real.log (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = Real.log (16 : ℝ) := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        ring
  have hkfloor :
      (Nat.log 16 (2 * X) : ℝ) ≤ LN / Real.log (16 : ℝ) := by
    rw [natLog_eq_floor_log_div (b := 16) (n := 2 * X) (by norm_num) hNone]
    exact Nat.floor_le (div_nonneg hLNpos.le
      (le_trans (by norm_num : (0 : ℝ) ≤ 2) hlog16))
  have hk : (Nat.log 16 (2 * X) : ℝ) ≤ LN / 2 := by
    have hden : 0 < Real.log (16 : ℝ) := lt_of_lt_of_le (by norm_num) hlog16
    have hdiv : LN / Real.log (16 : ℝ) ≤ LN / 2 := by
      apply (div_le_div_iff₀ hden (by norm_num)).2
      nlinarith [hLNpos.le, hlog16]
    exact hkfloor.trans hdiv
  have hNlog_eq : LN = L + Real.log 2 := by
    dsimp [LN, L]
    rw [show ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) by norm_num, Real.log_mul]
    · ring
    · norm_num
    · exact_mod_cast (show X ≠ 0 by omega)
  have hlog2_le_L : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ X by omega)
  have hNlog_le : LN ≤ L + Real.log 2 := hNlog_eq.le
  have hLN_le_twoL : LN ≤ 2 * L := by linarith
  have hLN_ge_L : L ≤ LN := by
    rw [hNlog_eq]
    have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hLNtwo : (2 : ℝ) ≤ LN := by
    linarith [hLN_ge_L, hLX']
  have hkplus : ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ) ≤ LN := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [hk, hLNtwo]
  have hlogindex :
      Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ) ≤ LN.log := by
    exact Real.log_le_log (by positivity) hkplus
  have hLLpos : 0 < LL := by
    dsimp [LL]
    exact Real.log_pos (by linarith [hLX'])
  have hlogLN : LN.log ≤ LL + Real.log 2 := by
    have hLN_upper : LN ≤ 2 * L := hLN_le_twoL
    have hlogupper := Real.log_le_log hLNpos hLN_upper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at hlogupper
    simpa [LL, add_comm] using hlogupper
  have hlog2_le_LL : Real.log 2 ≤ LL := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ Real.log (X : ℝ) by linarith [hLX'])
  linarith [hlogindex, hlogLN, hlog2_le_LL]

/- The finite LeanPool/Brun reciprocal-prime bound now has the source `log log` scale.  The
   constant is intentionally left as the explicit ten-block expression already present in
   `PrimeMass`; no numerical evaluation of that finite constant is needed. -/
theorem eventually_primesLE_mass_le_source_loglog :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) ≤
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          3 * (15 / Real.log 2) + 324) *
          Real.log (Real.log (X : ℝ)) := by
  let A : ℝ := ∑ i ∈ Finset.range 10,
    ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)
  let c : ℝ := 15 / Real.log 2
  let D : ℝ := A + 3 * c + 324
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hbase : 0 ≤ A + c + 324 := by positivity
  have hLL : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  have hM : ∀ᶠ X : ℕ in atTop,
      10 ≤ Nat.log 16 (2 * X) + 1 := by
    filter_upwards [eventually_ge_atTop ((16 : ℕ) ^ 9)] with X hX
    have hN0 : (2 * X) ≠ 0 := by omega
    have hpow : (16 : ℕ) ^ 9 ≤ 2 * X := by omega
    have hlog : 9 ≤ Nat.log 16 (2 * X) := by
      apply (Nat.le_log_iff_pow_le (by norm_num) hN0).2
      exact hpow
    omega
  have hindex := eventually_natLog16_two_mul_log_index_le_two_loglog
  filter_upwards [hLL, hM, hindex] with X hLLX hMX hidx
  have hcut := primesLE_mass_le_dyadic_log (2 * X) hMX
  have hcut' :
      (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) ≤
        A + c * (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) + 324 := by
    simpa [A, c] using hcut
  have hlogterm :
      c * (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) ≤
        c * (1 + 2 * Real.log (Real.log (X : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (by linarith [hidx]) hc
  have hmid :
      A + c * (1 + 2 * Real.log (Real.log (X : ℝ))) + 324 ≤
        D * Real.log (Real.log (X : ℝ)) := by
    dsimp [D]
    nlinarith [hLLX, hbase, hc]
  have hcut'' :
      (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) ≤
        A + c * (1 + 2 * Real.log (Real.log (X : ℝ))) + 324 := by
    exact hcut'.trans (by linarith [hlogterm])
  have hfinal := hcut''.trans hmid
  simpa [A, c, D] using hfinal

/- The canonical cutoff itself is below the doubled endpoint eventually.  Monotonicity of
   `Nat.log` then transfers the preceding index comparison from `2X` to the small-prime branch. -/
theorem eventually_source_cutoff_log_index_le_two_loglog :
    ∀ᶠ X : ℕ in atTop,
      Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) ≤
        2 * Real.log (Real.log (X : ℝ)) := by
  have hpow := eventually_source_log_pow_le_two_mul_pre
  have hidx := eventually_natLog16_two_mul_log_index_le_two_loglog
  filter_upwards [hpow, hidx] with X hpowX hidxX
  have hPle : sourceBasePrimeCutoff X ≤ 2 * X := by
    unfold sourceBasePrimeCutoff
    have hfloor :
        ((Nat.floor ((Real.log (X : ℝ)) ^ (10 : ℕ)) : ℕ) : ℝ) ≤
          (Real.log (X : ℝ)) ^ (10 : ℕ) :=
      Nat.floor_le (by positivity)
    have hpowX' : (Real.log (X : ℝ)) ^ (10 : ℕ) ≤
        ((2 * X : ℕ) : ℝ) := by simpa using hpowX
    have hfloor' :
        ((Nat.floor ((Real.log (X : ℝ)) ^ (10 : ℕ)) : ℕ) : ℝ) ≤
          ((2 * X : ℕ) : ℝ) := hfloor.trans hpowX'
    exact_mod_cast hfloor'
  have hlogmono :
      Nat.log 16 (sourceBasePrimeCutoff X) + 1 ≤ Nat.log 16 (2 * X) + 1 := by
    exact Nat.add_le_add_right (Nat.log_mono_right hPle) 1
  have hcast :
      ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) ≤
        ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlogmono
  have hpos :
      0 < ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos (Nat.log 16 (sourceBasePrimeCutoff X)))
  exact (Real.log_le_log hpos hcast).trans hidxX

/- Using the actual tenth-power cutoff, rather than the coarse bound `P ≤ 2X`, improves the
   nested logarithm in the small-prime branch by one level. -/
theorem eventually_source_cutoff_log_index_le_two_logloglog :
    ∀ᶠ X : ℕ in atTop,
      Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) ≤
        2 * Real.log (Real.log (Real.log (X : ℝ))) := by
  have hL : ∀ᶠ X : ℕ in atTop, 16 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (16 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 6 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (6 : ℝ))
  have hXnat : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hP := eventually_sourceBasePrimeCutoff_log16_large
  filter_upwards [hL, hLL, hXnat, hP] with X hLX hLLX hXX hPX
  let L : ℝ := Real.log (X : ℝ)
  let LL : ℝ := Real.log L
  let L3 : ℝ := Real.log LL
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLLpos : 0 < LL := by
    dsimp [LL]
    exact Real.log_pos (by linarith [hLX])
  have hP0 : sourceBasePrimeCutoff X ≠ 0 := by
    intro hzero
    simp [hzero] at hPX
  have hP2 : 2 ≤ sourceBasePrimeCutoff X := by
    by_contra hsmall
    have hcases : sourceBasePrimeCutoff X = 0 ∨ sourceBasePrimeCutoff X = 1 := by omega
    rcases hcases with hzero | hone
    · exact hP0 hzero
    · simp [hone] at hPX
  have hPpos : 0 < (sourceBasePrimeCutoff X : ℝ) := by
    exact_mod_cast (show 0 < sourceBasePrimeCutoff X by omega)
  have hPupper :
      (sourceBasePrimeCutoff X : ℝ) ≤ L ^ (10 : ℕ) := by
    have hfloor :
        ((Nat.floor ((Real.log (X : ℝ)) ^ (10 : ℕ)) : ℕ) : ℝ) ≤
          (Real.log (X : ℝ)) ^ (10 : ℕ) := Nat.floor_le (by positivity)
    simpa [sourceBasePrimeCutoff, L] using hfloor
  have hlogP : Real.log (sourceBasePrimeCutoff X : ℝ) ≤ 10 * LL := by
    calc
      Real.log (sourceBasePrimeCutoff X : ℝ) ≤ Real.log (L ^ (10 : ℕ)) :=
        Real.log_le_log hPpos hPupper
      _ = 10 * Real.log L := by rw [Real.log_pow]; ring
      _ = 10 * LL := by rfl
  have hlog16 : (2 : ℝ) ≤ Real.log (16 : ℝ) := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    calc
      (2 : ℝ) = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 4 * Real.log (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = Real.log (16 : ℝ) := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        ring
  have hlogPnonneg : 0 ≤ Real.log (sourceBasePrimeCutoff X : ℝ) :=
    (Real.log_pos (by exact_mod_cast hP2)).le
  have hkfloor :
      (Nat.log 16 (sourceBasePrimeCutoff X) : ℝ) ≤
        Real.log (sourceBasePrimeCutoff X : ℝ) / Real.log (16 : ℝ) := by
    rw [natLog_eq_floor_log_div (b := 16) (n := sourceBasePrimeCutoff X)
      (by norm_num) hP0]
    exact Nat.floor_le (div_nonneg hlogPnonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 2) hlog16))
  have hdiv :
      Real.log (sourceBasePrimeCutoff X : ℝ) / Real.log (16 : ℝ) ≤ 5 * LL := by
    apply (div_le_iff₀ (by linarith [hlog16])).2
    nlinarith [hlogP, hlog16, hLLX]
  have hk : (Nat.log 16 (sourceBasePrimeCutoff X) : ℝ) ≤ 5 * LL :=
    hkfloor.trans (hdiv)
  have hkplus :
      ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) ≤ 6 * LL := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [hk, hLLX]
  have hindex :
      Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ) ≤
        Real.log (6 * LL) := by
    exact Real.log_le_log (by positivity) hkplus
  have hlog6 : Real.log (6 : ℝ) ≤ L3 := by
    dsimp [L3]
    exact Real.log_le_log (by norm_num) hLLX
  have hlogupper : Real.log (6 * LL) = Real.log 6 + L3 := by
    dsimp [L3]
    rw [Real.log_mul (by norm_num) hLLpos.ne']
  dsimp [L3] at hlog6 hlogupper ⊢
  rw [hlogupper] at hindex
  linarith

/- The small-prime endpoint branch is consequently `O(X log log X)` with the same explicit
   reciprocal-mass constant as the low branch. -/
theorem eventually_dyadicEndpointSmallPrime_mass_le_source_loglog :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            3 * (15 / Real.log 2) + 324) *
            Real.log (Real.log (X : ℝ)) := by
  let A : ℝ := ∑ i ∈ Finset.range 10,
    ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)
  let c : ℝ := 15 / Real.log 2
  let D : ℝ := A + 3 * c + 324
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hbase : 0 ≤ A + c + 324 := by positivity
  have hLL : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  have hidx := eventually_source_cutoff_log_index_le_two_loglog
  have hsmall := eventually_dyadicEndpointSmallPrime_mass_le_source_cutoff_log
  filter_upwards [hLL, hidx, hsmall] with X hLLX hidxX hsmallX
  have hsmall' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) *
          (A + c * (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) := by
    simpa [A, c, mul_assoc] using hsmallX
  have hlogterm :
      c * (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) ≤
        c * (1 + 2 * Real.log (Real.log (X : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (by linarith [hidxX]) hc
  have hmid :
      A + c * (1 + 2 * Real.log (Real.log (X : ℝ))) + 324 ≤
        D * Real.log (Real.log (X : ℝ)) := by
    dsimp [D]
    nlinarith [hLLX, hbase, hc]
  have hsmall'' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) * (D * Real.log (Real.log (X : ℝ))) := by
    exact hsmall'.trans (mul_le_mul_of_nonneg_left
      (by linarith [hlogterm, hbase]) (by positivity))
  simpa [A, c, D, mul_assoc, mul_left_comm, mul_comm] using hsmall''

/- The tenth-power cutoff removes one more logarithm from the small-prime branch. -/
theorem eventually_dyadicEndpointSmallPrime_mass_le_source_logloglog :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            3 * (15 / Real.log 2) + 324) *
            Real.log (Real.log (Real.log (X : ℝ))) := by
  let A : ℝ := ∑ i ∈ Finset.range 10,
    ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)
  let c : ℝ := 15 / Real.log 2
  let D : ℝ := A + 3 * c + 324
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hbase : 0 ≤ A + c + 324 := by positivity
  have hL3 : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (Real.log (X : ℝ))) := by
    exact (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
  have hidx := eventually_source_cutoff_log_index_le_two_logloglog
  have hsmall := eventually_dyadicEndpointSmallPrime_mass_le_source_cutoff_log
  filter_upwards [hL3, hidx, hsmall] with X hL3X hidxX hsmallX
  have hsmall' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) *
          (A + c * (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) := by
    simpa [A, c, mul_assoc] using hsmallX
  have hlogterm :
      c * (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) ≤
        c * (1 + 2 * Real.log (Real.log (Real.log (X : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left (by linarith [hidxX]) hc
  have hmid :
      A + c * (1 + 2 * Real.log (Real.log (Real.log (X : ℝ)))) + 324 ≤
        D * Real.log (Real.log (Real.log (X : ℝ))) := by
    dsimp [D]
    nlinarith [hL3X, hbase, hc]
  have hsmall'' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) * (D * Real.log (Real.log (Real.log (X : ℝ)))) := by
    exact hsmall'.trans (mul_le_mul_of_nonneg_left
      (by linarith [hlogterm, hbase]) (by positivity))
  simpa [A, c, D, mul_assoc, mul_left_comm, mul_comm] using hsmall''

/- A complete scalar `O(X log log X)` certificate for one doubled dyadic block.  This is the
   strongest unconditional summatory statement currently available in the development; the
   remaining Erdős #878 targets require converting this block estimate into the density-one and
   maximal-order assertions. -/
theorem eventually_summatory_f_div_Icc_le_source_O_X_loglog :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (8 * ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            3 * (15 / Real.log 2) + 324) + 748) *
          (X : ℝ) * Real.log (Real.log (X : ℝ)) := by
  let A : ℝ := ∑ i ∈ Finset.range 10,
    ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)
  let c : ℝ := 15 / Real.log 2
  let D : ℝ := A + 3 * c + 324
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmass := eventually_primesLE_mass_le_source_loglog
  have hsmall := eventually_dyadicEndpointSmallPrime_mass_le_source_loglog
  have hcond := eventually_sourceAuxScale_conditions
  have hlow := eventually_dyadicEndpointLargeLowPower_mass_le_of_scale
    sourceAuxScale hD
    (hcond.1.mono (fun X h ↦ Nat.zero_lt_of_lt h))
    eventually_sourceAuxScale_mul_loglog_le_two_mul_self
    (by simpa [A, c, D] using hmass)
  have hhigh := eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget
    (Y := sourceAuxScale) (K := (2 : ℝ)) (by norm_num)
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have hL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X := eventually_gt_atTop (0 : ℕ)
  filter_upwards [hsmall, hlow, hhigh, hL, hLL, hXpos]
    with X hsmallX hlowX hhighX hLX hLLX hXposX
  have hend :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
    simpa [dyadicPrimeSet, dyadicEndpointWeight] using
      (summatory_f_div_Icc_le_two_mul_prime_power_weight X hXposX)
  rw [dyadic_endpoint_weight_source_three_way_split] at hend
  have hsum := add_le_add (add_le_add hsmallX hhighX) hlowX
  have hblock := hend.trans (by
    simpa [add_assoc, add_left_comm, add_comm] using hsum)
  have hratio :
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.log (X : ℝ))).2
    have hLLle : Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
      exact Real.log_le_self (by positivity)
    simpa using hLLle
  have hhigh' :
      (4 * (X : ℝ)) *
          ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 17) ≤
        748 * (X : ℝ) := by
    have hfactor :
        (10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 17 ≤ 11 * 17 := by
      nlinarith [hratio]
    nlinarith [hfactor]
  have hlow' : 4 * D * (X : ℝ) ≤ 4 * D * (X : ℝ) * Real.log (Real.log (X : ℝ)) := by
    have hcoef : 0 ≤ 4 * D * (X : ℝ) := by positivity
    exact le_mul_of_one_le_right hcoef hLLX
  have hsum' :
      4 * (X : ℝ) * D * Real.log (Real.log (X : ℝ)) +
          748 * (X : ℝ) + 4 * D * (X : ℝ) ≤
        (8 * D + 748) * (X : ℝ) * Real.log (Real.log (X : ℝ)) := by
    nlinarith [hlow', hLLX]
  have hsmall' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) * D * Real.log (Real.log (X : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsmallX
  have hblock' :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        4 * (X : ℝ) * D * Real.log (Real.log (X : ℝ)) +
          748 * (X : ℝ) + 4 * D * (X : ℝ) := by
    exact hblock.trans (by
      have htmp := add_le_add (add_le_add hsmall' hhigh') hlowX
      nlinarith [htmp])
  have hfinal := hblock'.trans hsum'
  simpa [A, c, D, mul_assoc, mul_left_comm, mul_comm] using hfinal

/- Replacing the coarse small-prime estimate by the tenth-power cutoff estimate sharpens the
   same doubled block to `O(X log log log X)`.  This is still a local block statement; a global
   bound for `sourceH` needs a separate dyadic summation argument. -/
theorem eventually_summatory_f_div_Icc_le_source_O_X_logloglog :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (8 * ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            3 * (15 / Real.log 2) + 324) + 748) *
          (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
  let A : ℝ := ∑ i ∈ Finset.range 10,
    ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)
  let c : ℝ := 15 / Real.log 2
  let D : ℝ := A + 3 * c + 324
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmass := eventually_primesLE_mass_le_source_loglog
  have hsmall := eventually_dyadicEndpointSmallPrime_mass_le_source_logloglog
  have hcond := eventually_sourceAuxScale_conditions
  have hlow := eventually_dyadicEndpointLargeLowPower_mass_le_of_scale
    sourceAuxScale hD
    (hcond.1.mono (fun X h ↦ Nat.zero_lt_of_lt h))
    eventually_sourceAuxScale_mul_loglog_le_two_mul_self
    (by simpa [A, c, D] using hmass)
  have hhigh := eventually_dyadicEndpointLargeHighPower_mass_le_uniform_source_brun_budget
    (Y := sourceAuxScale) (K := (2 : ℝ)) (by norm_num)
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have hL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hLL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
  have hL3 : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (Real.log (X : ℝ))) := by
    exact (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 < X := eventually_gt_atTop (0 : ℕ)
  filter_upwards [hsmall, hlow, hhigh, hL, hLL, hL3, hXpos]
    with X hsmallX hlowX hhighX hLX hLLX hL3X hXposX
  have hend :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
    simpa [dyadicPrimeSet, dyadicEndpointWeight] using
      (summatory_f_div_Icc_le_two_mul_prime_power_weight X hXposX)
  rw [dyadic_endpoint_weight_source_three_way_split] at hend
  have hsum := add_le_add (add_le_add hsmallX hhighX) hlowX
  have hblock := hend.trans (by
    simpa [add_assoc, add_left_comm, add_comm] using hsum)
  have hratio :
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.log (X : ℝ))).2
    have hLLle : Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
      exact Real.log_le_self (by positivity)
    simpa using hLLle
  have hhigh' :
      (4 * (X : ℝ)) *
          ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 17) ≤
        748 * (X : ℝ) := by
    have hfactor :
        (10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 17 ≤ 11 * 17 := by
      nlinarith [hratio]
    nlinarith [hfactor]
  have hsmall' :
      (∑ p ∈ dyadicPrimeSmallPrimeSet X (sourceBasePrimeCutoff X),
        dyadicEndpointWeight X p) ≤
        4 * (X : ℝ) * D * Real.log (Real.log (Real.log (X : ℝ))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsmallX
  have hlow' :
      4 * D * (X : ℝ) ≤
        4 * D * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
    have hcoef : 0 ≤ 4 * D * (X : ℝ) := by positivity
    exact le_mul_of_one_le_right hcoef hL3X
  have hhigh'' :
      748 * (X : ℝ) ≤ 748 * (X : ℝ) *
        Real.log (Real.log (Real.log (X : ℝ))) := by
    have hcoef : 0 ≤ 748 * (X : ℝ) := by positivity
    exact le_mul_of_one_le_right hcoef hL3X
  have hsum' :
      4 * (X : ℝ) * D * Real.log (Real.log (Real.log (X : ℝ))) +
          748 * (X : ℝ) + 4 * D * (X : ℝ) ≤
        (8 * D + 748) * (X : ℝ) *
          Real.log (Real.log (Real.log (X : ℝ))) := by
    nlinarith [hlow', hhigh'', hL3X]
  have hblock' :
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        4 * (X : ℝ) * D * Real.log (Real.log (Real.log (X : ℝ))) +
          748 * (X : ℝ) + 4 * D * (X : ℝ) := by
    exact hblock.trans (by
      have htmp := add_le_add (add_le_add hsmall' hhigh') hlowX
      nlinarith [htmp])
  have hfinal := hblock'.trans hsum'
  simpa [A, c, D, mul_assoc, mul_left_comm, mul_comm] using hfinal

/- The local doubled-block estimate can now be summed globally.  The regularized triple-log
   comparison function is positive at every integer, so the finite initial range required by the
   dyadic recursion is discharged by one explicit finite sum rather than by a hidden asymptotic
   convention. -/
theorem exists_global_summatory_f_div_Icc_le_source_regularized :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) *
          (1 + max 0 (Real.log (Real.log (Real.log (X : ℝ))))) := by
  let g : ℕ → ℝ := fun n ↦ (f n : ℝ) / (n : ℝ)
  let tlog : ℕ → ℝ := fun X ↦ Real.log (Real.log (Real.log (X : ℝ)))
  let φ : ℕ → ℝ := fun X ↦ 1 + max 0 (tlog X)
  let C₀ : ℝ :=
    8 * ((∑ i ∈ Finset.range 10,
          ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
        3 * (15 / Real.log 2) + 324) + 748
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    dsimp [g]
    exact div_nonneg (by positivity) (by positivity)
  have hpos1 : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  have hpos2 : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Real.log (n : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))
  have hpos3 : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Real.log (Real.log (n : ℝ))) := by
    exact (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) ∧
        0 < Real.log (Real.log (n : ℝ)) ∧
          0 < Real.log (Real.log (Real.log (n : ℝ))) := by
    filter_upwards [hpos1, hpos2, hpos3] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨Npos, hNpos⟩ := (eventually_atTop.1 hpos)
  obtain ⟨Nblock, hNblock⟩ :=
    (eventually_atTop.1 eventually_summatory_f_div_Icc_le_source_O_X_logloglog)
  let N : ℕ := max 1 (max Npos Nblock)
  have hNpos_le : Npos ≤ N := by
    dsimp [N]
    omega
  have hNblock_le : Nblock ≤ N := by
    dsimp [N]
    omega
  have hφpos : ∀ n : ℕ, N ≤ n → 0 < φ n := by
    intro n hn
    dsimp [φ]
    have hmax : 0 ≤ max 0 (tlog n) := le_max_left _ _
    linarith
  have hφmono : ∀ {a b : ℕ}, N ≤ a → a ≤ b → φ a ≤ φ b := by
    intro a b ha hab
    have haN : Npos ≤ a := le_trans hNpos_le ha
    have hbN : Npos ≤ b := le_trans haN hab
    have hpa := hNpos a haN
    have hpb := hNpos b hbN
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have haNat : 0 < a := by
      have hNone : 1 ≤ N := by
        dsimp [N]
        omega
      omega
    have haR : 0 < (a : ℝ) := by exact_mod_cast haNat
    have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log haR habR
    have hloglog : Real.log (Real.log (a : ℝ)) ≤
        Real.log (Real.log (b : ℝ)) :=
      Real.log_le_log hpa.1 hlog
    have hlogloglog : Real.log (Real.log (Real.log (a : ℝ))) ≤
        Real.log (Real.log (Real.log (b : ℝ))) :=
      Real.log_le_log hpa.2.1 hloglog
    dsimp [φ, tlog]
    simpa [add_comm] using
      (add_le_add_left (max_le_max (le_refl (0 : ℝ)) hlogloglog) 1)
  let G : ℝ := ∑ n ∈ Finset.Icc 1 (2 * N), g n
  let C : ℝ := C₀ + G
  have hG : 0 ≤ G := by
    dsimp [G]
    exact Finset.sum_nonneg (fun n hn ↦ hg n)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbase : ∀ X : ℕ, X < 2 * N + 1 →
      (∑ n ∈ Finset.Icc 1 X, g n) ≤ C * (X : ℝ) * φ X := by
    intro X hX
    by_cases hX0 : X = 0
    · subst X
      simp [φ]
    · have hXpos : 0 < X := Nat.pos_of_ne_zero hX0
      have hXle : X ≤ 2 * N := by omega
      have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 (2 * N) := by
        intro n hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
          (Finset.mem_Icc.mp hn).2.trans hXle⟩
      have hsum : (∑ n ∈ Finset.Icc 1 X, g n) ≤ G := by
        dsimp [G]
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn hnot
        exact hg n
      have hGone : G ≤ C := by
        dsimp [C]
        linarith
      have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hX0)
      have hφone : (1 : ℝ) ≤ φ X := by
        dsimp [φ]
        have hmax : 0 ≤ max 0 (tlog X) := le_max_left _ _
        linarith
      have hCX : C ≤ C * (X : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hXreal hC]
      have hCXφ : C * (X : ℝ) ≤ C * (X : ℝ) * φ X := by
        have hnonneg : 0 ≤ C * (X : ℝ) := mul_nonneg hC (by positivity)
        simpa using (mul_le_mul_of_nonneg_left hφone hnonneg)
      exact hsum.trans (hGone.trans (hCX.trans hCXφ))
  have hblock : ∀ X : ℕ, N ≤ X →
      (∑ n ∈ Finset.Icc X (2 * X), g n) ≤ C * (X : ℝ) * φ X := by
    intro X hX
    have hXblock : Nblock ≤ X := le_trans hNblock_le hX
    have hraw := hNblock X hXblock
    have hXpos : 0 < (X : ℝ) := by
      have hNone : 1 ≤ N := by
        dsimp [N]
        omega
      have : 0 < X := by omega
      exact_mod_cast this
    have hC₀C : C₀ ≤ C := by
      dsimp [C]
      linarith
    have htriple : 0 ≤ tlog X := le_of_lt (hNpos X (le_trans hNpos_le hX)).2.2
    have hφdom : tlog X ≤ φ X := by
      dsimp [φ]
      linarith [le_max_right (0 : ℝ) (tlog X)]
    have hfirst : C₀ * (X : ℝ) * tlog X ≤ C * (X : ℝ) * tlog X := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₀C hXpos.le) htriple
    have hsecond : C * (X : ℝ) * tlog X ≤ C * (X : ℝ) * φ X := by
      exact mul_le_mul_of_nonneg_left hφdom
        (mul_nonneg hC hXpos.le)
    have hraw' : (∑ n ∈ Finset.Icc X (2 * X), g n) ≤
        C₀ * (X : ℝ) * tlog X := by
      simpa [g, C₀, tlog] using hraw
    exact hraw'.trans (hfirst.trans hsecond)
  have hglobal := sum_Icc_le_of_dyadic_block_bound g φ N C hC hg
    (fun n hn ↦ hφpos n hn) hφmono hbase hblock
  refine ⟨C, hC, ?_⟩
  intro X
  simpa [g, φ, tlog] using hglobal X

/- Removing the regularization recovers the raw triple-log upper bound eventually.  This is the
   global `H(X) << X log log log X` certificate needed by the density-one `f`-side argument. -/
theorem exists_global_summatory_f_div_Icc_le_source_logloglog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
  rcases exists_global_summatory_f_div_Icc_le_source_regularized with ⟨C, hC, hglobal⟩
  have hL3 : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (Real.log (X : ℝ))) := by
    exact (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
  have hXpos : ∀ᶠ X : ℕ in atTop, 0 ≤ (X : ℝ) := by
    filter_upwards [eventually_ge_atTop (0 : ℕ)] with X hX
    exact_mod_cast hX
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hL3, hXpos] with X hL3X hXposX
  have hreg := hglobal X
  have hmax : max 0 (Real.log (Real.log (Real.log (X : ℝ)))) =
      Real.log (Real.log (Real.log (X : ℝ))) := by
    exact max_eq_right (by linarith)
  rw [hmax] at hreg
  have hlin : 1 + Real.log (Real.log (Real.log (X : ℝ))) ≤
      2 * Real.log (Real.log (Real.log (X : ℝ))) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlin
    (mul_nonneg hC hXposX)
  have htarget : C * (X : ℝ) *
      (1 + Real.log (Real.log (Real.log (X : ℝ)))) ≤
      (2 * C) * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact hreg.trans htarget

theorem eventually_dyadicEndpointLargeLowPower_mass_le_auxScale_of_reciprocal_loglog
    {D : ℝ} (hD : 0 ≤ D)
    (hprimeMass : ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) ≤
        D * Real.log (Real.log (X : ℝ))) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicPrimeLargeLowPowerSet X (sourceBasePrimeCutoff X) (sourceAuxScale X),
        dyadicEndpointWeight X p) ≤ 4 * D * (X : ℝ) := by
  have hcond := eventually_sourceAuxScale_conditions
  have hY : ∀ᶠ X : ℕ in atTop, 0 < sourceAuxScale X := by
    exact hcond.1.mono (fun X h ↦ Nat.zero_lt_of_lt h)
  have hscale := eventually_sourceAuxScale_mul_loglog_le_two_mul_self
  have hlow := eventually_dyadicEndpointLargeLowPower_mass_le_of_scale
    sourceAuxScale hD hY hscale hprimeMass
  convert hlow using 1; norm_num

/- Concrete source-scale specialization of the complete block certificate.  The high-branch
   constant is explicit (`K=2`); the remaining displayed low/small budgets are the scalar terms
   to be estimated in the final summatory asymptotic. -/
theorem eventually_summatory_f_div_Icc_le_source_three_way_auxScale :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (4 * (X : ℝ)) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (sourceBasePrimeCutoff X) + 1 : ℕ) : ℝ)) + 324) +
          (2 * (sourceAuxScale X : ℝ)) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) + 324) +
          (4 * (X : ℝ)) *
            ((10 + Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) * 17) := by
  rcases eventually_sourceAuxScale_conditions with ⟨hY, hYlt, hYratio, hYlog⟩
  have hmain := eventually_summatory_f_div_Icc_le_source_three_way_uniform
    (Y := sourceAuxScale) (K := (2 : ℝ)) (by norm_num)
    hY hYlt hYratio hYlog
  convert hmain using 1; norm_num

noncomputable def dyadicEndpointSmallSet (X Y : ℕ) : Finset ℕ :=
  (dyadicPrimeSet X).filter (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y)

noncomputable def dyadicEndpointLargeSet (X Y : ℕ) : Finset ℕ :=
  (dyadicPrimeSet X).filter (fun p ↦ Y < p ^ Nat.log p (2 * X))

/- The small endpoint branch is controlled by the reciprocal mass of primes below the threshold.
   This is a finite bridge: the endpoint power is at most `Y`, while the prime itself is at most
   that power, so each weight is bounded by `2Y/p`.  The sharper source estimate (22) can later be
   supplied by instantiating the reciprocal-prime certificate on the right. -/
theorem dyadicEndpointSmall_mass_le_cutoff_reciprocal_mass (X Y : ℕ) (hY : 0 < Y) :
    (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) ≤
      (2 * (Y : ℝ)) * (∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹)) := by
  have hsub : dyadicEndpointSmallSet X Y ⊆ Nat.primesLE Y := by
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hpS.1
    have hpI := Finset.mem_Icc.mp hpbase.1
    have hpprime := hpbase.2
    have hpow := hpS.2
    have hlogpos : 0 < Nat.log p (2 * X) :=
      Nat.log_pos hpprime.one_lt hpI.2
    have hple : p ≤ Y := by
      exact le_trans (Nat.le_pow hlogpos) hpow
    exact Nat.mem_primesLE.mpr ⟨hple, hpprime⟩
  have hpoint : ∀ p ∈ dyadicEndpointSmallSet X Y,
      dyadicEndpointWeight X p ≤ (2 * (Y : ℝ)) * ((p : ℝ)⁻¹) := by
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpbase := Finset.mem_filter.mp hpS.1
    have hpprime := hpbase.2
    have hpow := hpS.2
    have hp0 : 0 < p := hpprime.pos
    have hpowR : ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast hpow
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    unfold dyadicEndpointWeight
    have hdiv := div_le_div_of_nonneg_right hpowR (le_of_lt hpR)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  calc
    (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) ≤
        ∑ p ∈ dyadicEndpointSmallSet X Y, (2 * (Y : ℝ)) * ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ ≤ (2 * (Y : ℝ)) * (∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      · intro p hp hnot
        positivity

/- Substituting the dyadic cutoff estimate gives an explicit nested-log certificate for the small
   endpoint branch.  This is still a coarse `2Y` majorant; the paper's sharper choice of `Y` and
   its equation (22) are the remaining analytic refinement. -/
theorem dyadicEndpointSmall_mass_le_cutoff_log (X Y : ℕ)
    (hY : 0 < Y) (hlog : 10 ≤ Nat.log 16 Y + 1) :
    (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) ≤
      (2 * (Y : ℝ)) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 Y + 1 : ℕ) : ℝ)) + 324) := by
  have hsmall := dyadicEndpointSmall_mass_le_cutoff_reciprocal_mass X Y hY
  have hcut := primesLE_mass_le_dyadic_log Y hlog
  have hnonneg : 0 ≤ 2 * (Y : ℝ) := by positivity
  exact hsmall.trans (mul_le_mul_of_nonneg_left hcut hnonneg)

theorem dyadic_endpoint_weight_split (X Y : ℕ) :
    (∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p) =
      (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) +
      ∑ p ∈ dyadicEndpointLargeSet X Y, dyadicEndpointWeight X p := by
  have h := Finset.sum_filter_add_sum_filter_not
    (dyadicPrimeSet X) (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y)
    (fun p ↦ dyadicEndpointWeight X p)
  rw [← h]
  have hsmallfilter :
      (dyadicPrimeSet X).filter (fun p ↦ p ^ Nat.log p (2 * X) ≤ Y) =
        dyadicEndpointSmallSet X Y := by
    rfl
  have hlargefilter :
      (dyadicPrimeSet X).filter (fun p ↦ ¬ p ^ Nat.log p (2 * X) ≤ Y) =
        dyadicEndpointLargeSet X Y := by
    ext p
    simp [dyadicEndpointLargeSet, not_le]
  rw [hsmallfilter, hlargefilter]

theorem summatory_f_div_Icc_le_dyadic_endpoint
    (X : ℕ) (hX : 0 < X) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
      ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p := by
  simpa [dyadicPrimeSet, dyadicEndpointWeight] using
    summatory_f_div_Icc_le_two_mul_prime_power_weight X hX

/- As a sanity baseline, the same cutoff budget gives an unconditional coarse estimate for one
   `[X,2X]` summatory block.  It is only of `X log log X` strength; recording it explicitly makes
   clear that the missing improvement is exactly the source's sharper small/large split. -/
theorem eventually_summatory_f_div_Icc_le_coarse_dyadic_log :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        (4 * (X : ℝ)) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (2 * X) + 1 : ℕ) : ℝ)) + 324) := by
  have hlog := tendsto_nat_log_base_atTop (b := 16) (by norm_num)
  filter_upwards [eventually_ge_atTop (4 : ℕ),
      hlog.eventually (eventually_ge_atTop 10)] with X hX hlogX
  have hXpos : 0 < X := by omega
  have hlog2X : 10 ≤ Nat.log 16 (2 * X) + 1 := by
    have hmono : Nat.log 16 X ≤ Nat.log 16 (2 * X) :=
      Nat.log_mono_right (by omega)
    omega
  have hcut := primesLE_mass_le_dyadic_log (2 * X) hlog2X
  have hweight :
      (∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p) ≤
        (4 * (X : ℝ)) * (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) := by
    have hsub : dyadicPrimeSet X ⊆ Nat.primesLE (2 * X) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Icc.mp hp'.1
      exact Nat.mem_primesLE.mpr ⟨hpI.2, hp'.2⟩
    have hpoint : ∀ p ∈ dyadicPrimeSet X,
        dyadicEndpointWeight X p ≤ (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Icc.mp hp'.1
      have hpprime := hp'.2
      have hp0 : 0 < p := hpprime.pos
      have hpow : p ^ Nat.log p (2 * X) ≤ 2 * X :=
        Nat.pow_log_le_self p (by omega)
      have hpowR : ((p ^ Nat.log p (2 * X) : ℕ) : ℝ) ≤ (2 * X : ℝ) := by
        exact_mod_cast hpow
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
      unfold dyadicEndpointWeight
      have hdiv := div_le_div_of_nonneg_right hpowR (le_of_lt hpR)
      have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
      calc
        2 * (((p ^ Nat.log p (2 * X) : ℕ) : ℝ) / (p : ℝ)) ≤
            2 * ((2 * X : ℝ) / (p : ℝ)) := hmul
        _ = (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
          simp [div_eq_mul_inv]
          ring
    calc
      (∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p) ≤
          ∑ p ∈ dyadicPrimeSet X, (4 * (X : ℝ)) * ((p : ℝ)⁻¹) := by
        exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
      _ ≤ (4 * (X : ℝ)) * (∑ p ∈ Nat.primesLE (2 * X), ((p : ℝ)⁻¹)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        · intro p hp hnot
          positivity
  have hend := summatory_f_div_Icc_le_dyadic_endpoint X hXpos
  have htotal := hend.trans hweight
  have hcoef : 0 ≤ 4 * (X : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcut hcoef
  exact htotal.trans hmul

/- Conditional packaging of the paper's (22), (24), and (28) estimates.  Once the small- and
   large-endpoint sums have analytic bounds `A` and `B`, this theorem closes the whole finite
   dyadic block without hiding any unproved analytic fact in an axiom. -/
theorem summatory_f_div_Icc_le_of_dyadic_endpoint_piece_bounds
    (X Y : ℕ) (hX : 0 < X) (A B : ℝ)
    (hsmall :
      (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) ≤ A)
    (hlarge :
      (∑ p ∈ dyadicEndpointLargeSet X Y, dyadicEndpointWeight X p) ≤ B) :
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤ A + B := by
  calc
    (∑ n ∈ Finset.Icc X (2 * X), (f n : ℝ) / (n : ℝ)) ≤
        ∑ p ∈ dyadicPrimeSet X, dyadicEndpointWeight X p :=
      summatory_f_div_Icc_le_dyadic_endpoint X hX
    _ =
        (∑ p ∈ dyadicEndpointSmallSet X Y, dyadicEndpointWeight X p) +
          ∑ p ∈ dyadicEndpointLargeSet X Y, dyadicEndpointWeight X p :=
      dyadic_endpoint_weight_split X Y
    _ ≤ A + B := add_le_add hsmall hlarge

/- The preceding sigma sum has a canonical `(p,k)` key: the prime base and its
   integer logarithm in the ambient integer `n`.  We name the finite pair and
   key sets so that the next theorem can regroup the summatory function by
   these keys without making any infinitary or analytic assumption. -/
noncomputable def primeFactorPairSet (X : ℕ) : Finset ((_: ℕ) × ℕ) :=
  (Finset.Icc 1 X).sigma (fun n : ℕ ↦ n.primeFactors)

def primeFactorKey (z : (_ : ℕ) × ℕ) : ℕ × ℕ :=
  (z.2, Nat.log z.2 z.1)

noncomputable def primeFactorKeySet (X : ℕ) : Finset (ℕ × ℕ) :=
  (primeFactorPairSet X).image primeFactorKey

theorem sum_primeFactor_pairs_eq_sum_primeFactor_key_fibres (X : ℕ) :
    (∑ z ∈ primeFactorPairSet X,
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
      ∑ q ∈ primeFactorKeySet X,
        ∑ z ∈ primeFactorPairSet X with primeFactorKey z = q,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
  have hmaps : ∀ z ∈ primeFactorPairSet X,
      primeFactorKey z ∈ primeFactorKeySet X := by
    intro z hz
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  symm
  exact Finset.sum_fiberwise_of_maps_to hmaps (fun z ↦
    (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)))

theorem primeFactorKey_first_prime {X : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ primeFactorPairSet X) :
    (primeFactorKey z).1.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_sigma.mp hz).2

theorem primeFactorKey_first_dvd {X : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ primeFactorPairSet X) :
    (primeFactorKey z).1 ∣ z.1 := by
  exact Nat.dvd_of_mem_primeFactors (Finset.mem_sigma.mp hz).2

theorem primeFactorKey_first_le_X {X : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ primeFactorPairSet X) :
    (primeFactorKey z).1 ≤ X := by
  have hmem := Finset.mem_sigma.mp hz
  have hn1 : 1 ≤ z.1 := (Finset.mem_Icc.mp hmem.1).1
  have hp_le : z.2 ≤ z.1 := Nat.le_of_dvd (by omega)
    (Nat.dvd_of_mem_primeFactors hmem.2)
  simpa [primeFactorKey] using hp_le.trans (Finset.mem_Icc.mp hmem.1).2

theorem primeFactorKeySet_first_le_X {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorKeySet X) : q.1 ≤ X := by
  rcases Finset.mem_image.mp hq with ⟨z, hz, rfl⟩
  exact primeFactorKey_first_le_X hz

theorem primeFactorKey_log_pos {X : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ primeFactorPairSet X) :
    0 < (primeFactorKey z).2 := by
  have hmem := Finset.mem_sigma.mp hz
  have hn1 : 1 ≤ z.1 := (Finset.mem_Icc.mp hmem.1).1
  have hn0 : z.1 ≠ 0 := by omega
  have hp : z.2.Prime := Nat.prime_of_mem_primeFactors hmem.2
  have hp_le : z.2 ≤ z.1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
    (Nat.dvd_of_mem_primeFactors hmem.2)
  simpa [primeFactorKey] using Nat.log_pos hp.one_lt hp_le

theorem primeFactorKeySet_mem_properties {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorKeySet X) :
    q.1.Prime ∧ 0 < q.2 := by
  rcases Finset.mem_image.mp hq with ⟨z, hz, rfl⟩
  constructor
  · simpa [primeFactorKey] using primeFactorKey_first_prime hz
  · simpa [primeFactorKey] using primeFactorKey_log_pos hz

/- Every finite key exponent is below the ambient logarithm `log_p X`.  This is the index-range
   fact needed to split the small-prime sum into nonterminal and terminal exponent blocks. -/
theorem primeFactorKey_second_le_log {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorKeySet X) : q.2 ≤ Nat.log q.1 X := by
  rcases Finset.mem_image.mp hq with ⟨z, hz, rfl⟩
  have hz' : z.1 ∈ Finset.Icc 1 X ∧ z.2 ∈ z.1.primeFactors := by
    simpa [primeFactorPairSet] using (Finset.mem_sigma.mp hz)
  have hnI := Finset.mem_Icc.mp hz'.1
  have hn1 : 1 ≤ z.1 := hnI.1
  have hn0 : z.1 ≠ 0 := by omega
  have hX0 : X ≠ 0 := by omega
  have hp : (primeFactorKey z).1.Prime := primeFactorKey_first_prime hz
  have hpow : (primeFactorKey z).1 ^ (primeFactorKey z).2 ≤ X := by
    have hpowz : z.2 ^ Nat.log z.2 z.1 ≤ z.1 := Nat.pow_log_le_self z.2 hn0
    simpa [primeFactorKey] using hpowz.trans hnI.2
  exact (Nat.le_log_iff_pow_le hp.one_lt hX0).2 hpow

theorem summatory_f_div_eq_sum_primeFactor_key_fibres (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) =
      ∑ q ∈ primeFactorKeySet X,
        ∑ z ∈ primeFactorPairSet X with primeFactorKey z = q,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) =
        ∑ z ∈ primeFactorPairSet X,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) := by
      simpa [primeFactorPairSet] using summatory_f_div_eq_sum_primeFactor_pairs X
    _ = ∑ q ∈ primeFactorKeySet X,
        ∑ z ∈ primeFactorPairSet X with primeFactorKey z = q,
          (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ)) :=
      sum_primeFactor_pairs_eq_sum_primeFactor_key_fibres X

theorem sum_primeFactor_key_fibre_eq_sum_natLog_filter
    (X p k : ℕ) :
    (∑ z ∈ (primeFactorPairSet X).filter (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
      ∑ n ∈ (Finset.Icc 1 X).filter
          (fun n ↦ p ∈ n.primeFactors ∧ Nat.log p n = k),
        (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
  let S : Finset ((_ : ℕ) × ℕ) :=
    (primeFactorPairSet X).filter (fun z ↦ primeFactorKey z = (p, k))
  let T : Finset ℕ :=
    (Finset.Icc 1 X).filter (fun n ↦ p ∈ n.primeFactors ∧ Nat.log p n = k)
  have hsum :
      (∑ z ∈ S, (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
        ∑ n ∈ T, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
    apply Finset.sum_bij (fun z _ ↦ z.1)
    · intro z hz
      have hzS : z ∈ S := by simpa [S] using hz
      have hz' := Finset.mem_sigma.mp (Finset.mem_filter.mp hzS).1
      have hkey := (Finset.mem_filter.mp hzS).2
      have hpz : z.2 = p := by
        simpa [primeFactorKey] using congrArg Prod.fst hkey
      have hkz : Nat.log p z.1 = k := by
        simpa [primeFactorKey, hpz] using congrArg Prod.snd hkey
      apply Finset.mem_filter.mpr
      exact ⟨hz'.1, by simpa [hpz, hkz] using hz'.2⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      have hz₁S : z₁ ∈ S := by simpa [S] using hz₁
      have hz₂S : z₂ ∈ S := by simpa [S] using hz₂
      have hkey₁ := (Finset.mem_filter.mp hz₁S).2
      have hkey₂ := (Finset.mem_filter.mp hz₂S).2
      have hp₁ : z₁.2 = p := by
        simpa [primeFactorKey] using congrArg Prod.fst hkey₁
      have hp₂ : z₂.2 = p := by
        simpa [primeFactorKey] using congrArg Prod.fst hkey₂
      cases z₁ with
      | mk n₁ q₁ =>
        cases z₂ with
        | mk n₂ q₂ =>
          simp only at heq hp₁ hp₂ ⊢
          subst n₂
          subst q₁
          subst q₂
          rfl
    · intro n hn
      have hnT : n ∈ T := by simpa [T] using hn
      have hnI : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hnT).1
      have hnp := (Finset.mem_filter.mp hnT).2
      refine ⟨⟨n, p⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sigma.mpr ⟨hnI, hnp.1⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact hnp.2
    · intro z hz
      have hzS : z ∈ S := by simpa [S] using hz
      have hkey := (Finset.mem_filter.mp hzS).2
      have hpz : z.2 = p := by
        simpa [primeFactorKey] using congrArg Prod.fst hkey
      simp [hpz]
  simpa [S, T] using hsum

theorem sum_primeFactor_key_fibre_le_harmonic_block
    (X p k : ℕ) (hp : 1 < p) :
    (∑ z ∈ (primeFactorPairSet X).filter (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) ≤
      ((p ^ k : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
  let T : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∈ n.primeFactors ∧ Nat.log p n = k)
  let U : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∣ n ∧ Nat.log p n = k)
  let V : Finset ℕ :=
    (Finset.Icc 1 X).filter (fun n ↦ Nat.log p n = k)
  calc
    (∑ z ∈ (primeFactorPairSet X).filter
        (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
        ∑ n ∈ T, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
      simpa [T] using sum_primeFactor_key_fibre_eq_sum_natLog_filter X p k
    _ ≤ ∑ n ∈ T, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnT : n ∈ T := by simpa [T] using hn
      have hmem := (Finset.mem_filter.mp hnT).2.1
      have hnI := (Finset.mem_filter.mp hnT).1
      have hlog := (Finset.mem_filter.mp hnT).2.2
      have hn0 : n ≠ 0 := by
        have : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
        omega
      simpa [hlog] using
        (normalizedPrimePowerWeight_le_reciprocal_floor_quotient hn0 hmem)
    _ ≤ ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnT : n ∈ T := by simpa [T] using hn
        have hnI := (Finset.mem_filter.mp hnT).1
        have hpred := (Finset.mem_filter.mp hnT).2
        apply Finset.mem_filter.mpr
        exact ⟨hnI, Nat.dvd_of_mem_primeFactors hpred.1, hpred.2⟩
      · intro n hnU hnnotT
        positivity
    _ ≤ ∑ n ∈ V, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnU : n ∈ U := by simpa [U] using hn
        have hnI := (Finset.mem_filter.mp hnU).1
        have hpred := (Finset.mem_filter.mp hnU).2
        exact Finset.mem_filter.mpr ⟨hnI, hpred.2⟩
      · intro n hnV hnnotU
        positivity
    _ ≤ ((p ^ k : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
      simpa [V] using sum_inv_div_on_natLog_block_le_harmonic_sub_one X p k hp

theorem summatory_f_div_le_sum_primeFactor_key_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      ∑ q ∈ primeFactorKeySet X,
        (((q.1 ^ q.2 : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) := by
  rw [summatory_f_div_eq_sum_primeFactor_key_fibres]
  apply Finset.sum_le_sum
  intro q hq
  have hprops := primeFactorKeySet_mem_properties hq
  simpa using
    (sum_primeFactor_key_fibre_le_harmonic_block X q.1 q.2 hprops.1.one_lt)

theorem sum_primeFactor_key_fibre_le_harmonic_block_prime_divisor
    (X p k : ℕ) (hp : 1 < p) (hk : 1 ≤ k) :
    (∑ z ∈ (primeFactorPairSet X).filter (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) ≤
      ((p ^ (k - 1) : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
  let T : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∈ n.primeFactors ∧ Nat.log p n = k)
  let U : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∣ n ∧ Nat.log p n = k)
  calc
    (∑ z ∈ (primeFactorPairSet X).filter
        (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
        ∑ n ∈ T, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
      simpa [T] using sum_primeFactor_key_fibre_eq_sum_natLog_filter X p k
    _ ≤ ∑ n ∈ T, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnT : n ∈ T := by simpa [T] using hn
      have hmem := (Finset.mem_filter.mp hnT).2.1
      have hnI := (Finset.mem_filter.mp hnT).1
      have hlog := (Finset.mem_filter.mp hnT).2.2
      have hn0 : n ≠ 0 := by
        have : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
        omega
      simpa [hlog] using
        (normalizedPrimePowerWeight_le_reciprocal_floor_quotient hn0 hmem)
    _ ≤ ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnT : n ∈ T := by simpa [T] using hn
        have hnI := (Finset.mem_filter.mp hnT).1
        have hpred := (Finset.mem_filter.mp hnT).2
        apply Finset.mem_filter.mpr
        exact ⟨hnI, Nat.dvd_of_mem_primeFactors hpred.1, hpred.2⟩
      · intro n hnU hnnotT
        positivity
    _ ≤ ((p ^ (k - 1) : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
      simpa [U] using sum_inv_div_on_prime_natLog_block_le X p k hp hk

theorem sum_primeFactor_key_fibre_le_harmonic_block_prime_divisor_cutoff
    (X p k : ℕ) (hp : 1 < p) (hk : 1 ≤ k) :
    (∑ z ∈ (primeFactorPairSet X).filter (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) ≤
      ((p ^ (k - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / p) (p ^ k - 1)) / p ^ (k - 1) : ℕ) : ℝ) := by
  let T : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∈ n.primeFactors ∧ Nat.log p n = k)
  let U : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun n ↦ p ∣ n ∧ Nat.log p n = k)
  calc
    (∑ z ∈ (primeFactorPairSet X).filter
        (fun z ↦ primeFactorKey z = (p, k)),
      (((z.2 ^ Nat.log z.2 z.1 : ℕ) : ℝ) / (z.1 : ℝ))) =
        ∑ n ∈ T, (((p ^ Nat.log p n : ℕ) : ℝ) / (n : ℝ)) := by
      simpa [T] using sum_primeFactor_key_fibre_eq_sum_natLog_filter X p k
    _ ≤ ∑ n ∈ T, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnT : n ∈ T := by simpa [T] using hn
      have hmem := (Finset.mem_filter.mp hnT).2.1
      have hnI := (Finset.mem_filter.mp hnT).1
      have hlog := (Finset.mem_filter.mp hnT).2.2
      have hn0 : n ≠ 0 := by
        have : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
        omega
      simpa [hlog] using
        (normalizedPrimePowerWeight_le_reciprocal_floor_quotient hn0 hmem)
    _ ≤ ∑ n ∈ U, (((n / p ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnT : n ∈ T := by simpa [T] using hn
        have hnI := (Finset.mem_filter.mp hnT).1
        have hpred := (Finset.mem_filter.mp hnT).2
        apply Finset.mem_filter.mpr
        exact ⟨hnI, Nat.dvd_of_mem_primeFactors hpred.1, hpred.2⟩
      · intro n hnU hnnotT
        positivity
    _ ≤ ((p ^ (k - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / p) (p ^ k - 1)) / p ^ (k - 1) : ℕ) : ℝ) := by
      simpa [U] using sum_inv_div_on_prime_natLog_block_le_cutoff X p k hp hk

theorem summatory_f_div_le_sum_primeFactor_key_harmonic_prime_divisor_cutoff (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      ∑ q ∈ primeFactorKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) / q.1 ^ (q.2 - 1) : ℕ) : ℝ)) := by
  rw [summatory_f_div_eq_sum_primeFactor_key_fibres]
  apply Finset.sum_le_sum
  intro q hq
  have hprops := primeFactorKeySet_mem_properties hq
  have hk : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprops.2)
  simpa using
    (sum_primeFactor_key_fibre_le_harmonic_block_prime_divisor_cutoff
      X q.1 q.2 hprops.1.one_lt hk)

theorem summatory_f_div_le_sum_primeFactor_key_harmonic_prime_divisor (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      ∑ q ∈ primeFactorKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) := by
  rw [summatory_f_div_eq_sum_primeFactor_key_fibres]
  apply Finset.sum_le_sum
  intro q hq
  have hprops := primeFactorKeySet_mem_properties hq
  have hk : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprops.2)
  simpa using
    (sum_primeFactor_key_fibre_le_harmonic_block_prime_divisor
      X q.1 q.2 hprops.1.one_lt hk)

noncomputable def primeFactorSmallKeySet (X : ℕ) : Finset (ℕ × ℕ) :=
  (primeFactorKeySet X).filter (fun q ↦ q.1 ≤ Nat.sqrt X)

/- The small-key sum splits exactly into nonterminal exponents and the terminal exponent.
   The preceding index-range lemma ensures these are exhaustive. -/
theorem sum_primeFactorSmall_cutoff_eq_nonterminal_add_terminal (X : ℕ) :
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) =
      (∑ q ∈ (primeFactorSmallKeySet X).filter
          (fun q ↦ q.2 < Nat.log q.1 X),
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) +
      ∑ q ∈ (primeFactorSmallKeySet X).filter
          (fun q ↦ q.2 = Nat.log q.1 X),
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ)) := by
  let S := primeFactorSmallKeySet X
  let g : (ℕ × ℕ) → ℝ := fun q ↦
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ))
  have hsplit : S =
      S.filter (fun q ↦ q.2 < Nat.log q.1 X) ∪
        S.filter (fun q ↦ q.2 = Nat.log q.1 X) := by
    ext q
    by_cases hq : q ∈ S
    · have hle := primeFactorKey_second_le_log
        (X := X) (q := q) (Finset.mem_filter.mp hq |>.1)
      by_cases hlt : q.2 < Nat.log q.1 X
      · simp [hq, hlt]
      · have heq : q.2 = Nat.log q.1 X :=
          Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
        simp [hq, heq]
    · simp [hq]
  have hdisj : Disjoint
      (S.filter (fun q ↦ q.2 < Nat.log q.1 X))
      (S.filter (fun q ↦ q.2 = Nat.log q.1 X)) := by
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    exact (Nat.not_le_of_lt (Finset.mem_filter.mp hq₁).2)
      (Nat.le_of_eq (Finset.mem_filter.mp hq₂).2.symm)
  rw [show (∑ q ∈ primeFactorSmallKeySet X, g q) = ∑ q ∈ S, g q by rfl]
  rw [hsplit, Finset.sum_union hdisj]

/- Harmonic numbers are monotone after casting to `ℝ`; this elementary lemma lets us replace
   the cutoff harmonic block by the full `(p-1)` block whenever a deliberately coarser certificate
   is preferable. -/
lemma harmonic_real_mono_of_le {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      (Finset.mem_Icc.mp hi).2.trans hab⟩
  · intro i hi hnot
    positivity

lemma harmonic_real_le_nat (n : ℕ) : (harmonic n : ℝ) ≤ (n : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    (∑ i ∈ Finset.Icc 1 n, ((i : ℝ)⁻¹)) ≤
        ∑ _i ∈ Finset.Icc 1 n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hi0 : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
      exact (inv_le_one₀ hi0).2 (by exact_mod_cast hi1)
    _ = ((Finset.Icc 1 n).card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : n + 1 - 1 ≤ n)

theorem primeFactorSmallKey_term_le_untruncated {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X) :
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ)) ≤
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) := by
  have hqkey : q ∈ primeFactorKeySet X := (Finset.mem_filter.mp hq).1
  have hprops := primeFactorKeySet_mem_properties hqkey
  have hp : q.1.Prime := hprops.1
  have hk : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprops.2)
  have hdpos : 0 < q.1 ^ (q.2 - 1) := Nat.pow_pos hp.pos
  have harg :
      (min (X / q.1) (q.1 ^ q.2 - 1)) / q.1 ^ (q.2 - 1) ≤ q.1 - 1 := by
    apply (Nat.div_le_iff_le_mul hdpos).2
    calc
      min (X / q.1) (q.1 ^ q.2 - 1) ≤ q.1 ^ q.2 - 1 := min_le_right _ _
      _ = (q.1 - 1) * q.1 ^ (q.2 - 1) + q.1 ^ (q.2 - 1) - 1 := by
        have hpow : q.1 ^ q.2 = q.1 ^ (q.2 - 1) * q.1 := by
          calc
            q.1 ^ q.2 = q.1 ^ ((q.2 - 1) + 1) := by rw [Nat.sub_add_cancel hk]
            _ = q.1 ^ (q.2 - 1) * q.1 := by rw [Nat.pow_succ]
        rw [hpow, Nat.sub_mul, Nat.one_mul]
        rw [Nat.mul_comm q.1 (q.1 ^ (q.2 - 1))]
        have hle : q.1 ^ (q.2 - 1) ≤ q.1 ^ (q.2 - 1) * q.1 :=
          Nat.le_mul_of_pos_right _ hp.pos
        rw [Nat.sub_add_cancel hle]
  have hh := harmonic_real_mono_of_le harg
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem primeFactorSmallKey_term_le_min_cutoff {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X) :
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ)) ≤
      ((min (X / q.1) (q.1 ^ q.2 - 1) : ℕ) : ℝ) := by
  let d : ℕ := q.1 ^ (q.2 - 1)
  let u : ℕ := min (X / q.1) (q.1 ^ q.2 - 1)
  have hdpos : 0 < d := by
    dsimp [d]
    have hp := (primeFactorKeySet_mem_properties (Finset.mem_filter.mp hq).1).1
    exact Nat.pow_pos hp.pos
  have hh := harmonic_real_le_nat (u / d)
  have hfirst :
      (d : ℝ) * (harmonic (u / d) : ℝ) ≤
        (d : ℝ) * ((u / d : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hmulnat : d * (u / d) ≤ u := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self u d
  have hmulreal : (d : ℝ) * ((u / d : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hmulnat
  change (d : ℝ) * (harmonic (u / d) : ℝ) ≤ (u : ℝ)
  exact hfirst.trans hmulreal

theorem sum_primeFactorSmall_cutoff_le_min_cutoff (X : ℕ) :
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
    ∑ q ∈ primeFactorSmallKeySet X,
      ((min (X / q.1) (q.1 ^ q.2 - 1) : ℕ) : ℝ) := by
  apply Finset.sum_le_sum
  intro q hq
  exact primeFactorSmallKey_term_le_min_cutoff hq

/- For a nonterminal exponent `k < Nat.log p X`, the next power already lies below `X`.
   Consequently the block endpoint is the power endpoint `p^k−1`. -/
theorem primeFactorSmall_nonterminal_min_eq_pow_sub_one {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X)
    (hnonterm : q.2 < Nat.log q.1 X) :
    min (X / q.1) (q.1 ^ q.2 - 1) = q.1 ^ q.2 - 1 := by
  have hqkey : q ∈ primeFactorKeySet X := (Finset.mem_filter.mp hq).1
  have hp : q.1.Prime := (primeFactorKeySet_mem_properties hqkey).1
  have hp_pos : 0 < q.1 := hp.pos
  have hklog : q.2 + 1 ≤ Nat.log q.1 X := by omega
  have hpow_le : q.1 ^ (q.2 + 1) ≤ q.1 ^ Nat.log q.1 X :=
    Nat.pow_le_pow_right hp.one_lt.le hklog
  have hp_le_X : q.1 ≤ X := primeFactorKeySet_first_le_X hqkey
  have hXpos : 0 < X := hp.pos.trans_le hp_le_X
  have hX0 : X ≠ 0 := Nat.ne_of_gt hXpos
  have hpowX : q.1 ^ Nat.log q.1 X ≤ X := Nat.pow_log_le_self q.1 hX0
  have hnext : q.1 ^ (q.2 + 1) ≤ X := hpow_le.trans hpowX
  have hdiv : q.1 ^ q.2 ≤ X / q.1 := by
    apply (Nat.le_div_iff_mul_le hp_pos).2
    simpa [pow_succ, Nat.mul_comm] using hnext
  exact min_eq_right (Nat.le_trans (Nat.sub_le _ _) hdiv)

/- The sharp integer-length estimate therefore bounds every nonterminal block by `p^k`.
   Summing these geometric block bounds is the finite core of the nonterminal branch. -/
theorem primeFactorSmall_nonterminal_term_le_pow {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X)
    (hnonterm : q.2 < Nat.log q.1 X) :
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ)) ≤
      ((q.1 ^ q.2 : ℕ) : ℝ) := by
  have hmin := primeFactorSmall_nonterminal_min_eq_pow_sub_one hq hnonterm
  have hbound := primeFactorSmallKey_term_le_min_cutoff hq
  rw [hmin] at hbound
  rw [hmin]
  exact hbound.trans (by exact_mod_cast (Nat.sub_le (q.1 ^ q.2) 1))

/- The nonterminal keys embed into a finite prime/exponent grid.  This is the exact finite
   reindexing needed before applying a geometric-series or prime-mass estimate: each small key
   contributes to the row for its prime base and to the exponent interval `1 ≤ k < log_p X`. -/
theorem sum_primeFactorSmall_nonterminal_term_le_prime_power_grid (X : ℕ) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 < Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt X),
        ∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ) := by
  classical
  let S₀ : Finset (ℕ × ℕ) :=
    (primeFactorSmallKeySet X).filter (fun q ↦ q.2 < Nat.log q.1 X)
  let e : (ℕ × ℕ) ↪ Sigma (fun _ : ℕ => ℕ) :=
    { toFun := fun q ↦ ⟨q.1, q.2⟩
      inj' := by
        intro a b hab
        cases a with
        | mk a₁ a₂ =>
          cases b with
          | mk b₁ b₂ =>
            simp only [Sigma.mk.injEq] at hab
            cases hab.1
            cases hab.2
            rfl }
  let S : Finset (Sigma (fun _ : ℕ => ℕ)) := S₀.map e
  let U : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    (Nat.primesLE (Nat.sqrt X)).sigma (fun p ↦ Finset.Ico 1 (Nat.log p X))
  let g : Sigma (fun _ : ℕ => ℕ) → ℝ := fun q ↦ ((q.1 ^ q.2 : ℕ) : ℝ)
  have hsubset : S ⊆ U := by
    intro q hq
    rcases Finset.mem_map.mp hq with ⟨r, hr, rfl⟩
    have hqS := Finset.mem_filter.mp hr
    have hqsmall := Finset.mem_filter.mp hqS.1
    have hqkey : r ∈ primeFactorKeySet X := hqsmall.1
    have hsmall : r.1 ≤ Nat.sqrt X := hqsmall.2
    have hprops := primeFactorKeySet_mem_properties hqkey
    have hkpos : 1 ≤ r.2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprops.2)
    have hpLE : r.1 ∈ Nat.primesLE (Nat.sqrt X) :=
      Nat.mem_primesLE.mpr ⟨hsmall, hprops.1⟩
    have hkIco : r.2 ∈ Finset.Ico 1 (Nat.log r.1 X) :=
      Finset.mem_Ico.mpr ⟨hkpos, hqS.2⟩
    exact Finset.mem_sigma.mpr ⟨hpLE, hkIco⟩
  have hnonneg : ∀ q ∈ U, q ∉ S → 0 ≤ g q := by
    intro q hqU hqS
    dsimp [g]
    positivity
  calc
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 < Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        ∑ q ∈ S₀, g (e q) := by
      apply Finset.sum_le_sum
      intro q hq
      change
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ)) ≤
          ((q.1 ^ q.2 : ℕ) : ℝ)
      exact primeFactorSmall_nonterminal_term_le_pow
        (Finset.mem_filter.mp hq |>.1) (Finset.mem_filter.mp hq |>.2)
    _ = ∑ q ∈ S, g q := by
      rw [show S = S₀.map e by rfl]
      rw [Finset.sum_map]
    _ ≤ ∑ q ∈ U, g q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ = ∑ p ∈ Nat.primesLE (Nat.sqrt X),
        ∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ) := by
      rw [show U = (Nat.primesLE (Nat.sqrt X)).sigma
        (fun p ↦ Finset.Ico 1 (Nat.log p X)) by rfl]
      rw [Finset.sum_sigma']

/- A cast-safe geometric-series identity for the nonterminal block aggregation. -/
theorem geometric_sum_natCast_mul_sub_one (p K : ℕ) :
    ((p : ℝ) - 1) *
      (∑ k ∈ Finset.range K, ((p ^ k : ℕ) : ℝ)) =
      (p : ℝ) ^ K - 1 := by
  have h := geom_sum_mul (p : ℝ) K
  simpa only [Nat.cast_pow, mul_comm] using h

/- In particular, multiplying a finite geometric sum by `p−1` never exceeds its last power
   (for `p≥1`); this is the intended competition-style compression after grouping exponents. -/
theorem geometric_sum_natCast_mul_sub_one_le (p K : ℕ) (hp : 1 ≤ p) :
    ((p : ℝ) - 1) *
      (∑ k ∈ Finset.range K, ((p ^ k : ℕ) : ℝ)) ≤
      (p : ℝ) ^ K := by
  rw [geometric_sum_natCast_mul_sub_one]
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith

/- Each prime row in the grid is bounded by the endpoint `X` divided by `p−1`.  The proof
   combines the finite inclusion `Ico 1 K ⊆ range K` with the geometric identity above and
   `p^(log_p X) ≤ X`; this is the first explicit analytic compression after reindexing. -/
theorem prime_power_Ico_sum_le_div {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime) :
    (∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
      (X : ℝ) / ((p : ℝ) - 1) := by
  have hsub : Finset.Ico 1 (Nat.log p X) ⊆ Finset.range (Nat.log p X) := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hrow :
      (∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
        ∑ k ∈ Finset.range (Nat.log p X), ((p ^ k : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk hnot
    positivity
  have hpminus_pos : 0 < (p : ℝ) - 1 := by
    have hpgt : 1 < p := hp.one_lt
    exact sub_pos.mpr (by exact_mod_cast hpgt)
  have hgeomdiv :
      (∑ k ∈ Finset.range (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
        (p : ℝ) ^ Nat.log p X / ((p : ℝ) - 1) := by
    apply (le_div_iff₀ hpminus_pos).2
    simpa [mul_comm] using
      (geometric_sum_natCast_mul_sub_one_le p (Nat.log p X) hp.one_le)
  have hXpos : 0 < X := Nat.zero_lt_of_lt hX
  have hpow_nat : p ^ Nat.log p X ≤ X := Nat.pow_log_le_self p (Nat.ne_of_gt hXpos)
  have hpow_real : (p : ℝ) ^ Nat.log p X ≤ (X : ℝ) := by
    exact_mod_cast hpow_nat
  have hdiv :
      (p : ℝ) ^ Nat.log p X / ((p : ℝ) - 1) ≤
        (X : ℝ) / ((p : ℝ) - 1) :=
    div_le_div_of_nonneg_right hpow_real (le_of_lt hpminus_pos)
  exact hrow.trans (hgeomdiv.trans hdiv)

/- Summing the row estimate and using `1/(p−1) ≤ 2/p` gives a compact reciprocal-prime
   majorant.  It is deliberately finite and unconditional; the remaining loss is exactly the
   reciprocal-prime mass that the PrimeMass module can estimate. -/
theorem sum_prime_power_grid_le_two_mul_X_reciprocal_prime_sum
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ Nat.primesLE (Nat.sqrt X),
      ∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
      2 * (X : ℝ) *
        (∑ p ∈ Nat.primesLE (Nat.sqrt X), ((p : ℝ)⁻¹)) := by
  have hXreal : 0 ≤ (X : ℝ) := by positivity
  have hterm : ∀ p ∈ Nat.primesLE (Nat.sqrt X),
      (∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
        2 * (X : ℝ) * ((p : ℝ)⁻¹) := by
    intro p hpLE
    have hp : p.Prime := (Nat.mem_primesLE.mp hpLE).2
    have hrow := prime_power_Ico_sum_le_div hX hp
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hpminuspos : 0 < (p : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
    have hfrac : (1 : ℝ) / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpminuspos hpRpos).2
      nlinarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.two_le]
    have hmul :
        (X : ℝ) / ((p : ℝ) - 1) ≤ 2 * (X : ℝ) * ((p : ℝ)⁻¹) := by
      calc
        (X : ℝ) / ((p : ℝ) - 1) =
            (X : ℝ) * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ (X : ℝ) * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac hXreal
        _ = 2 * (X : ℝ) * ((p : ℝ)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
    exact hrow.trans hmul
  calc
    (∑ p ∈ Nat.primesLE (Nat.sqrt X),
      ∑ k ∈ Finset.Ico 1 (Nat.log p X), ((p ^ k : ℕ) : ℝ)) ≤
        ∑ p ∈ Nat.primesLE (Nat.sqrt X),
          2 * (X : ℝ) * ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hpLE
      exact hterm p hpLE
    _ = 2 * (X : ℝ) *
        (∑ p ∈ Nat.primesLE (Nat.sqrt X), ((p : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]

/- Combining the nonterminal grid injection with the reciprocal-prime majorant packages the
   complete finite reduction of the small nonterminal branch into one reusable inequality. -/
theorem sum_primeFactorSmall_nonterminal_term_le_two_mul_X_reciprocal_prime_sum
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 < Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      2 * (X : ℝ) *
        (∑ p ∈ Nat.primesLE (Nat.sqrt X), ((p : ℝ)⁻¹)) := by
  exact (sum_primeFactorSmall_nonterminal_term_le_prime_power_grid X).trans
    (sum_prime_power_grid_le_two_mul_X_reciprocal_prime_sum hX)

/- A completely explicit corollary from `PrimeMass`: the finite nonterminal branch is at most
   `2X` times the standard logarithmic reciprocal-prime envelope up to `sqrt X`.  This bound is
   intentionally recorded as a certified baseline; improving its `log(sqrt X)` scale to the
   source's iterated-log scale is one of the genuinely missing analytic steps. -/
theorem sum_primeFactorSmall_nonterminal_term_le_explicit_log_bound
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 < Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      2 * (X : ℝ) *
        ((Real.log (Nat.sqrt X : ℝ) + Real.log 4) / Real.log 2) := by
  have hXpos : 0 < X := Nat.zero_lt_of_lt hX
  have hsqrt : 1 ≤ Nat.sqrt X := by
    exact Nat.sqrt_pos.mpr hXpos
  have hmass :
      (∑ p ∈ Nat.primesLE (Nat.sqrt X), ((p : ℝ)⁻¹)) ≤
        (Real.log (Nat.sqrt X : ℝ) + Real.log 4) / Real.log 2 := by
    apply reciprocal_prime_sum_le_log4_of_lower_endpoint
      (L := 2) (N := Nat.sqrt X) (s := Nat.primesLE (Nat.sqrt X))
    · norm_num
    · exact hsqrt
    · intro p hp
      exact hp
    · intro p hp
      exact (Nat.mem_primesLE.mp hp).2.two_le
  exact (sum_primeFactorSmall_nonterminal_term_le_two_mul_X_reciprocal_prime_sum hX).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

/- The dyadic-family estimate gives a sharper, nested-log baseline whenever its finite cutoff
   side condition is met.  This is still not the paper's final `log log log` estimate, but it
   records the exact point where the existing LeanPool/PrimeMass dyadic machinery can replace the
   coarse `log(sqrt X)` envelope. -/
theorem sum_primeFactorSmall_nonterminal_term_le_dyadic_log_bound
    {X : ℕ} (hX : 1 ≤ X)
    (hlog : 10 ≤ Nat.log 16 (Nat.sqrt X) + 1) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 < Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      2 * (X : ℝ) *
        ((∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) := by
  have hmass := primesLE_mass_le_dyadic_log (Nat.sqrt X) hlog
  exact (sum_primeFactorSmall_nonterminal_term_le_two_mul_X_reciprocal_prime_sum hX).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

/- The cutoff side condition is eventual rather than an additional analytic hypothesis.  We prove
   this directly from `m ≤ sqrt X ↔ m*m ≤ X` and the existing base-16 logarithm divergence. -/
theorem tendsto_nat_sqrt_atTop_for_Erdos878 :
    Tendsto (fun X : ℕ ↦ Nat.sqrt X) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with X hX
  exact Nat.le_sqrt.mpr hX

theorem eventually_sqrt_nat_log16_cutoff :
    ∀ᶠ X : ℕ in atTop, 10 ≤ Nat.log 16 (Nat.sqrt X) + 1 := by
  have hlog := tendsto_nat_log_base_atTop (b := 16) (by norm_num)
  have hcomp : Tendsto (fun X : ℕ ↦ Nat.log 16 (Nat.sqrt X)) atTop atTop :=
    hlog.comp tendsto_nat_sqrt_atTop_for_Erdos878
  filter_upwards [hcomp.eventually (eventually_ge_atTop 9)] with X hX
  omega

/- Eventual form of the preceding dyadic nonterminal certificate, ready to feed into an eventual
   `H(X)` argument. -/
theorem eventually_sum_primeFactorSmall_nonterminal_term_le_dyadic_log_bound :
    ∀ᶠ X : ℕ in atTop,
      (∑ q ∈ (primeFactorSmallKeySet X).filter
          (fun q ↦ q.2 < Nat.log q.1 X),
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        2 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_sqrt_nat_log16_cutoff]
    with X hX hlog
  exact sum_primeFactorSmall_nonterminal_term_le_dyadic_log_bound hX hlog

/- At a terminal exponent `k = Nat.log p X`, the logarithmic block ends before `p^(k+1)`.
   Thus its cutoff is exactly `X/p`, rather than the generic minimum of the two endpoints. -/
theorem primeFactorSmall_terminal_min_eq_div {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X)
    (hterm : q.2 = Nat.log q.1 X) :
    min (X / q.1) (q.1 ^ q.2 - 1) = X / q.1 := by
  have hqkey : q ∈ primeFactorKeySet X := (Finset.mem_filter.mp hq).1
  have hp : q.1.Prime := (primeFactorKeySet_mem_properties hqkey).1
  have hpgt : 1 < q.1 := hp.one_lt
  have hp_pos : 0 < q.1 := hp.pos
  have hlt : X < q.1 ^ (q.2 + 1) := by
    have h := Nat.lt_pow_succ_log_self hpgt X
    simpa [hterm, Nat.succ_eq_add_one] using h
  have hquotlt : X / q.1 < q.1 ^ q.2 := by
    apply (Nat.div_lt_iff_lt_mul hp_pos).2
    simpa [pow_succ, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm] using hlt
  have hquotle : X / q.1 ≤ q.1 ^ q.2 - 1 := Nat.le_sub_one_of_lt hquotlt
  exact min_eq_left hquotle

/- The sharp integer-length estimate specializes on a terminal key to the reciprocal-prime
   envelope `X/p`.  This is the finite starting point for a terminal-prime harmonic estimate. -/
theorem primeFactorSmall_terminal_term_le_div {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorSmallKeySet X)
    (hterm : q.2 = Nat.log q.1 X) :
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ)) ≤
      ((X / q.1 : ℕ) : ℝ) := by
  have hmin := primeFactorSmall_terminal_min_eq_div hq hterm
  have hbound := primeFactorSmallKey_term_le_min_cutoff hq
  rw [hmin] at hbound
  rw [hmin]
  exact hbound

/- Summing terminal terms preserves the reciprocal-prime envelope.  The remaining compression of
   the right side to a distinct prime-base sum is finite bookkeeping; its analytic bound is not
   supplied here. -/
theorem sum_primeFactorSmall_terminal_le_div (X : ℕ) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
    ∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X),
      ((X / q.1 : ℕ) : ℝ) := by
  apply Finset.sum_le_sum
  intro q hq
  exact primeFactorSmall_terminal_term_le_div (Finset.mem_filter.mp hq).1
    (Finset.mem_filter.mp hq).2

/- The terminal branch can now be cut at an arbitrary lower prime endpoint.  The first part is
   finite bookkeeping (terminal keys have a unique exponent for each prime base); the second part
   invokes the logarithmically weighted prime-mass estimate from `PrimeMass`.  This is the precise
   interface needed to turn a source cutoff `p ≥ L` into an `X / log L` budget. -/
theorem sum_primeFactorSmall_terminal_le_div_of_lower_endpoint
    {X L : ℕ} (hX : 1 ≤ X) (hL : 1 < L) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X ∧ L ≤ q.1),
      ((X / q.1 : ℕ) : ℝ)) ≤
      (X : ℝ) *
        ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
  classical
  let T : Finset (ℕ × ℕ) :=
    (primeFactorSmallKeySet X).filter
      (fun q ↦ q.2 = Nat.log q.1 X ∧ L ≤ q.1)
  let S : Finset ℕ := T.image Prod.fst
  have hsumrecip :
      (∑ q ∈ T, ((q.1 : ℝ)⁻¹)) =
        ∑ p ∈ S, ((p : ℝ)⁻¹) := by
    apply Finset.sum_bij (fun q _ ↦ q.1)
    · intro q hq
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have hterm₁ := (Finset.mem_filter.mp hq₁).2.1
      have hterm₂ := (Finset.mem_filter.mp hq₂).2.1
      cases q₁ with
      | mk p₁ k₁ =>
        cases q₂ with
        | mk p₂ k₂ =>
          simp only at heq hterm₁ hterm₂ ⊢
          subst p₂
          apply Prod.ext
          · rfl
          · exact hterm₁.trans hterm₂.symm
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rfl
  have hSsubset : S ⊆ X.primesLE := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hqT : q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X ∧ L ≤ q.1) := by
      simpa [T] using hq
    have hqkey : q ∈ primeFactorKeySet X :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hqT).1).1
    have hprops := primeFactorKeySet_mem_properties hqkey
    exact Nat.mem_primesLE.mpr ⟨primeFactorKeySet_first_le_X hqkey, hprops.1⟩
  have hSge : ∀ p ∈ S, L ≤ p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2.2
  have hmass := reciprocal_prime_sum_le_log4_of_lower_endpoint
    (L := L) (N := X) hL hX hSsubset hSge
  have hdiv :
      (∑ q ∈ T, ((X / q.1 : ℕ) : ℝ)) ≤
        (X : ℝ) * (∑ q ∈ T, ((q.1 : ℝ)⁻¹)) := by
    calc
      (∑ q ∈ T, ((X / q.1 : ℕ) : ℝ)) ≤
          ∑ q ∈ T, (X : ℝ) * ((q.1 : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro q hq
        calc
          ((X / q.1 : ℕ) : ℝ) ≤ (X : ℝ) / (q.1 : ℝ) := Nat.cast_div_le
          _ = (X : ℝ) * ((q.1 : ℝ)⁻¹) := by rw [div_eq_mul_inv]
      _ = (X : ℝ) * (∑ q ∈ T, ((q.1 : ℝ)⁻¹)) := by
        rw [Finset.mul_sum]
  calc
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X ∧ L ≤ q.1),
      ((X / q.1 : ℕ) : ℝ)) = ∑ q ∈ T, ((X / q.1 : ℕ) : ℝ) := by rfl
    _ ≤ (X : ℝ) * (∑ q ∈ T, ((q.1 : ℝ)⁻¹)) := hdiv
    _ = (X : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) := by rw [hsumrecip]
    _ ≤ (X : ℝ) *
        ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)

/- Splitting terminal keys at a lower endpoint isolates the two analytic regimes used in the
   source argument.  The low-prime part is left as a finite reciprocal-prime sum, while the
   high-prime part is already controlled by `X/log L`.  No asymptotic assertion is hidden here. -/
theorem sum_primeFactorSmall_terminal_le_low_reciprocal_add_high_cutoff
    {X L : ℕ} (hX : 1 ≤ X) (hL : 1 < L) :
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) +
        (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
  classical
  let T : Finset (ℕ × ℕ) :=
    (primeFactorSmallKeySet X).filter (fun q ↦ q.2 = Nat.log q.1 X)
  let Tlow : Finset (ℕ × ℕ) := T.filter (fun q ↦ q.1 < L)
  let Thigh : Finset (ℕ × ℕ) := T.filter (fun q ↦ ¬ q.1 < L)
  let Slow : Finset ℕ := Tlow.image Prod.fst
  have hsplit :
      (∑ q ∈ T, ((X / q.1 : ℕ) : ℝ)) =
        (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) +
          ∑ q ∈ Thigh, ((X / q.1 : ℕ) : ℝ) := by
    symm
    simpa [Tlow, Thigh, not_lt] using
      (Finset.sum_filter_add_sum_filter_not T (fun q ↦ q.1 < L)
        (fun q ↦ ((X / q.1 : ℕ) : ℝ)))
  have hsumrecip :
      (∑ q ∈ Tlow, ((q.1 : ℝ)⁻¹)) =
        ∑ p ∈ Slow, ((p : ℝ)⁻¹) := by
    apply Finset.sum_bij (fun q _ ↦ q.1)
    · intro q hq
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have hterm₁ := (Finset.mem_filter.mp hq₁).1
      have hterm₂ := (Finset.mem_filter.mp hq₂).1
      have hbase₁ := (Finset.mem_filter.mp hterm₁).2
      have hbase₂ := (Finset.mem_filter.mp hterm₂).2
      cases q₁ with
      | mk p₁ k₁ =>
        cases q₂ with
        | mk p₂ k₂ =>
          simp only at heq hbase₁ hbase₂ ⊢
          subst p₂
          apply Prod.ext
          · rfl
          · exact hbase₁.trans hbase₂.symm
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rfl
  have hSlow : Slow ⊆ Nat.primesLE (L - 1) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hqsmall : q ∈ primeFactorSmallKeySet X :=
      (Finset.mem_filter.mp hqT).1
    have hqkey : q ∈ primeFactorKeySet X :=
      (Finset.mem_filter.mp hqsmall).1
    have hprops := primeFactorKeySet_mem_properties hqkey
    have hlow : q.1 < L := (Finset.mem_filter.mp hq).2
    exact Nat.mem_primesLE.mpr ⟨by omega, hprops.1⟩
  have hlowdiv :
      (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) ≤
        (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) := by
    have hdiv :
        (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) ≤
          (X : ℝ) * (∑ q ∈ Tlow, ((q.1 : ℝ)⁻¹)) := by
      calc
        (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) ≤
            ∑ q ∈ Tlow, (X : ℝ) * ((q.1 : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ((X / q.1 : ℕ) : ℝ) ≤ (X : ℝ) / (q.1 : ℝ) := Nat.cast_div_le
            _ = (X : ℝ) * ((q.1 : ℝ)⁻¹) := by rw [div_eq_mul_inv]
        _ = (X : ℝ) * (∑ q ∈ Tlow, ((q.1 : ℝ)⁻¹)) := by
          rw [Finset.mul_sum]
    have hmass :
        (∑ p ∈ Slow, ((p : ℝ)⁻¹)) ≤
          ∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSlow
      intro p hp hnot
      positivity
    calc
      (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) ≤
          (X : ℝ) * (∑ q ∈ Tlow, ((q.1 : ℝ)⁻¹)) := hdiv
      _ = (X : ℝ) * (∑ p ∈ Slow, ((p : ℝ)⁻¹)) := by rw [hsumrecip]
      _ ≤ (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
  have hhighdiv :
      (∑ q ∈ Thigh, ((X / q.1 : ℕ) : ℝ)) ≤
        (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
    have hset : Thigh =
        (primeFactorSmallKeySet X).filter
          (fun q ↦ q.2 = Nat.log q.1 X ∧ L ≤ q.1) := by
      ext q
      simp [T, Thigh, not_lt, and_comm, and_left_comm]
    rw [hset]
    exact sum_primeFactorSmall_terminal_le_div_of_lower_endpoint hX hL
  have hterm := sum_primeFactorSmall_terminal_le_div X
  have hterm' :
      (∑ q ∈ T,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        ∑ q ∈ T, ((X / q.1 : ℕ) : ℝ) := by
    simpa [T] using hterm
  calc
    (∑ q ∈ (primeFactorSmallKeySet X).filter
        (fun q ↦ q.2 = Nat.log q.1 X),
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        ∑ q ∈ T, (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ)) := by rfl
    _ ≤ (∑ q ∈ Tlow, ((X / q.1 : ℕ) : ℝ)) +
          ∑ q ∈ Thigh, ((X / q.1 : ℕ) : ℝ) := hterm'.trans_eq hsplit
    _ ≤ (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) +
          (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
      exact add_le_add hlowdiv hhighdiv

/- The small-key cutoff now has a single explicit certificate: a dyadic nested-log bound for
   nonterminal exponents, a finite low-prime reciprocal sum, and the `X/log L` high-prime tail.
   This is the direct finite interface to the remaining optimization in the source H(X) proof. -/
theorem sum_primeFactorSmall_cutoff_le_dyadic_and_terminal_split
    {X L : ℕ} (hX : 1 ≤ X) (hL : 1 < L)
    (hlog : 10 ≤ Nat.log 16 (Nat.sqrt X) + 1) :
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
      2 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
        (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) +
        (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
  have hsplit := sum_primeFactorSmall_cutoff_eq_nonterminal_add_terminal X
  have hnonterm :=
    sum_primeFactorSmall_nonterminal_term_le_dyadic_log_bound hX hlog
  have hterm :=
    sum_primeFactorSmall_terminal_le_low_reciprocal_add_high_cutoff hX hL
  calc
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) =
        (∑ q ∈ (primeFactorSmallKeySet X).filter
          (fun q ↦ q.2 < Nat.log q.1 X),
          (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
            (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
              q.1 ^ (q.2 - 1) : ℕ) : ℝ))) +
          ∑ q ∈ (primeFactorSmallKeySet X).filter
            (fun q ↦ q.2 = Nat.log q.1 X),
            (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
              (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
                q.1 ^ (q.2 - 1) : ℕ) : ℝ)) := hsplit
    _ ≤ 2 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          ∑ q ∈ (primeFactorSmallKeySet X).filter
            (fun q ↦ q.2 = Nat.log q.1 X),
            (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
              (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
                q.1 ^ (q.2 - 1) : ℕ) : ℝ)) := by
      linarith only [hnonterm]
    _ ≤ 2 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          ((X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) +
            (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ))) := by
      linarith only [hterm]
    _ = 2 * (X : ℝ) *
          ((∑ i ∈ Finset.range 10,
              ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
            (15 / Real.log 2) *
              (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
        (X : ℝ) * (∑ p ∈ Nat.primesLE (L - 1), ((p : ℝ)⁻¹)) +
        (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) / Real.log (L : ℝ)) := by
      ring

/- Choosing the terminal split at the integer square-root cutoff removes the two auxiliary
   side conditions from the finite certificate.  The resulting eventual statement is the exact
   small-prime budget that remains to be optimized in the source proof of `H`. -/
theorem eventually_sum_primeFactorSmall_cutoff_le_dyadic_and_sqrt_terminal_split :
    ∀ᶠ X : ℕ in atTop,
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        2 * (X : ℝ) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          (X : ℝ) * (∑ p ∈ Nat.primesLE (Nat.sqrt X - 1), ((p : ℝ)⁻¹)) +
          (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) /
            Real.log (Nat.sqrt X : ℝ)) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_sqrt_nat_log16_cutoff]
    with X hX hlog
  have hsqrt : 2 ≤ Nat.sqrt X := by
    apply Nat.le_sqrt.mpr
    omega
  have hL : 1 < Nat.sqrt X := by omega
  exact sum_primeFactorSmall_cutoff_le_dyadic_and_terminal_split (by omega) hL hlog

/- The finite low-prime term can itself be covered by the same dyadic mass estimate.  This
   removes the last unevaluated finite sum from the square-root instantiation, at the cost of a
   factor three in front of the common dyadic budget. -/
theorem eventually_sum_primeFactorSmall_cutoff_le_three_dyadic_sqrt_bound :
    ∀ᶠ X : ℕ in atTop,
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        3 * (X : ℝ) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) /
            Real.log (Nat.sqrt X : ℝ)) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_sqrt_nat_log16_cutoff]
    with X hX hlog
  have hsqrt : 2 ≤ Nat.sqrt X := by
    apply Nat.le_sqrt.mpr
    omega
  have hL : 1 < Nat.sqrt X := by omega
  have hmass := primesLE_mass_le_dyadic_log (Nat.sqrt X) hlog
  have hlow :
      (∑ p ∈ Nat.primesLE (Nat.sqrt X - 1), ((p : ℝ)⁻¹)) ≤
        (∑ i ∈ Finset.range 10,
            ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
          (15 / Real.log 2) *
            (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324 := by
    calc
      (∑ p ∈ Nat.primesLE (Nat.sqrt X - 1), ((p : ℝ)⁻¹)) ≤
          ∑ p ∈ Nat.primesLE (Nat.sqrt X), ((p : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hp' := Nat.mem_primesLE.mp hp
          apply Nat.mem_primesLE.mpr
          constructor
          · omega
          · exact hp'.2
        · intro p hp hnot
          positivity
      _ ≤ _ := hmass
  have hmain :=
    sum_primeFactorSmall_cutoff_le_dyadic_and_terminal_split (by omega) hL hlog
  have hXnonneg : 0 ≤ (X : ℝ) := by positivity
  have hlow' := mul_le_mul_of_nonneg_left hlow hXnonneg
  calc
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        2 * (X : ℝ) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          (X : ℝ) * (∑ p ∈ Nat.primesLE (Nat.sqrt X - 1), ((p : ℝ)⁻¹)) +
          (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) /
            Real.log (Nat.sqrt X : ℝ)) := hmain
    _ ≤ 3 * (X : ℝ) *
            ((∑ i ∈ Finset.range 10,
                ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
              (15 / Real.log 2) *
                (1 + Real.log ((Nat.log 16 (Nat.sqrt X) + 1 : ℕ) : ℝ)) + 324) +
          (X : ℝ) * ((Real.log (X : ℝ) + Real.log 4) /
            Real.log (Nat.sqrt X : ℝ)) := by
      linarith only [hlow']

theorem sum_primeFactorSmall_cutoff_le_untruncated (X : ℕ) :
    (∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
    ∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) := by
  apply Finset.sum_le_sum
  intro q hq
  exact primeFactorSmallKey_term_le_untruncated hq

noncomputable def primeFactorLargeKeySet (X : ℕ) : Finset (ℕ × ℕ) :=
  (primeFactorKeySet X).filter (fun q ↦ Nat.sqrt X < q.1)

theorem primeFactorLargeKey_log_eq_one {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorLargeKeySet X) :
    q.2 = 1 := by
  rcases Finset.mem_image.mp (show q ∈ primeFactorKeySet X from
    (Finset.mem_filter.mp hq).1) with ⟨z, hz, rfl⟩
  have hz' := Finset.mem_sigma.mp hz
  have hn1 : 1 ≤ z.1 := (Finset.mem_Icc.mp hz'.1).1
  have hn0 : z.1 ≠ 0 := by omega
  have hlarge : Nat.sqrt X < z.2 := by
    simpa [primeFactorKey] using (Finset.mem_filter.mp hq).2
  have hsq : X < z.2 ^ 2 := (Nat.sqrt_lt').mp hlarge
  have hpow : z.2 ^ Nat.log z.2 z.1 ≤ X :=
    (Nat.pow_log_le_self z.2 hn0).trans (Finset.mem_Icc.mp hz'.1).2
  have hlogpos : 0 < Nat.log z.2 z.1 := primeFactorKey_log_pos hz
  by_contra hk
  have hk2 : 2 ≤ Nat.log z.2 z.1 := by
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.ne_of_gt hlogpos, hk⟩
  have hpow2 : z.2 ^ 2 ≤ z.2 ^ Nat.log z.2 z.1 :=
    Nat.pow_le_pow_right (Nat.zero_lt_of_lt
      (Nat.prime_of_mem_primeFactors hz'.2).one_lt) hk2
  have hle : z.2 ^ 2 ≤ X := hpow2.trans hpow
  omega

theorem primeFactorLargeKey_harmonic_weight_eq {X : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ primeFactorLargeKeySet X) :
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) / q.1 ^ (q.2 - 1) : ℕ) : ℝ)) =
      (harmonic (X / q.1) : ℝ) := by
  have hqk := primeFactorLargeKey_log_eq_one hq
  have hlarge := (Finset.mem_filter.mp hq).2
  have hprops := primeFactorKeySet_mem_properties (Finset.mem_filter.mp hq).1
  have hqpos : 0 < q.1 := hprops.1.pos
  have hsq : X < q.1 ^ 2 := (Nat.sqrt_lt').mp hlarge
  have hdivlt : X / q.1 < q.1 := by
    apply (Nat.div_lt_iff_lt_mul hqpos).2
    simpa [pow_two, Nat.mul_comm] using hsq
  have hdivle : X / q.1 ≤ q.1 - 1 := Nat.le_pred_of_lt hdivlt
  rw [hqk]
  have hmin : min (X / q.1) (q.1 - 1) = X / q.1 := min_eq_left hdivle
  simp [hmin]

theorem sum_primeFactorLarge_cutoff_weight_eq_harmonic (X : ℕ) :
    (∑ q ∈ primeFactorLargeKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) =
      ∑ q ∈ primeFactorLargeKeySet X, (harmonic (X / q.1) : ℝ) := by
  apply Finset.sum_congr rfl
  intro q hq
  exact primeFactorLargeKey_harmonic_weight_eq hq

theorem primeFactorLargeKey_first_injective {X : ℕ} :
    Set.InjOn (fun q : ℕ × ℕ ↦ q.1) (primeFactorLargeKeySet X : Set (ℕ × ℕ)) := by
  intro q₁ hq₁ q₂ hq₂ hfirst
  have hq₁k := primeFactorLargeKey_log_eq_one hq₁
  have hq₂k := primeFactorLargeKey_log_eq_one hq₂
  exact Prod.ext hfirst (hq₁k.trans hq₂k.symm)

noncomputable def primeFactorLargeBaseSet (X : ℕ) : Finset ℕ :=
  (primeFactorLargeKeySet X).image Prod.fst

theorem sum_primeFactorLarge_harmonic_eq_sum_base_harmonic (X : ℕ) :
    (∑ q ∈ primeFactorLargeKeySet X, (harmonic (X / q.1) : ℝ)) =
      ∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ) := by
  let S : Finset (ℕ × ℕ) := primeFactorLargeKeySet X
  let T : Finset ℕ := primeFactorLargeBaseSet X
  symm
  apply Finset.sum_bij (fun p _ ↦ (p, 1))
  · intro p hp
    have hpT : p ∈ T := by simpa [T] using hp
    rcases Finset.mem_image.mp hpT with ⟨q, hq, hfst⟩
    have hqk := primeFactorLargeKey_log_eq_one hq
    have hqeq : (p, 1) = q := Prod.ext hfst.symm hqk.symm
    rw [hqeq]
    simpa [S] using hq
  · intro p₁ hp₁ p₂ hp₂ heq
    simpa using heq
  · intro q hq
    have hqS : q ∈ S := by simpa [S] using hq
    have hqk := primeFactorLargeKey_log_eq_one hqS
    refine ⟨q.1, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, hqS, rfl⟩
    · exact Prod.ext rfl hqk.symm
  · intro p hp
    rfl

theorem primeFactorLargeBaseSet_subset_Icc (X : ℕ) :
    primeFactorLargeBaseSet X ⊆ Finset.Icc (Nat.sqrt X + 1) X := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  have hlarge := (Finset.mem_filter.mp hq).2
  have hupper := primeFactorKeySet_first_le_X (Finset.mem_filter.mp hq).1
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hlarge, hupper⟩

theorem primeFactorLargeBaseSet_all_prime (X : ℕ) :
    ∀ p ∈ primeFactorLargeBaseSet X, p.Prime := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  exact (primeFactorKeySet_mem_properties (Finset.mem_filter.mp hq).1).1

theorem primeFactorLargeBaseSet_filter_subset_Icc (X m : ℕ) :
    (primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m) ⊆
      Finset.Icc (Nat.sqrt X + 1) (X / m) := by
  intro p hp
  have hpbase : p ∈ primeFactorLargeBaseSet X := (Finset.mem_filter.mp hp).1
  have hprange := primeFactorLargeBaseSet_subset_Icc X hpbase
  have hupper : p ≤ X / m := (Finset.mem_filter.mp hp).2
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hprange).1, hupper⟩

theorem primeFactorLargeBaseSet_filter_card_le_Icc_card (X m : ℕ) :
    ((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card ≤
      (Finset.Icc (Nat.sqrt X + 1) (X / m)).card := by
  exact Finset.card_le_card (primeFactorLargeBaseSet_filter_subset_Icc X m)

theorem primeFactorLargeBaseSet_filter_card_le_primeCounting (X m : ℕ) :
    ((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card ≤
      Nat.primeCounting (X / m) := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  have hpfilter := Finset.mem_filter.mp hp
  apply Nat.mem_primesLE.mpr
  exact ⟨hpfilter.2, primeFactorLargeBaseSet_all_prime X p hpfilter.1⟩

theorem primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [← Nat.primesLE_card_eq_primeCounting]
    calc
      (Nat.primesLE (n + 1)).card ≤ (Finset.Icc 1 (n + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        have h := Nat.mem_primesLE.mp hp
        exact Finset.mem_Icc.mpr ⟨Nat.Prime.one_le h.2, h.1⟩
      _ = n + 1 := by simp

theorem sum_inv_sq_Icc_le_two (M : ℕ) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Icc 1 M, ((m : ℝ) ^ 2)⁻¹) ≤ 2 := by
  rw [Finset.Icc_eq_cons_Ioc hM, Finset.sum_cons]
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := M)
    (by norm_num) hM
  norm_num at htail ⊢
  have hnonneg : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  linarith

/- The logarithmic side condition needed on the square-root range is automatic with a safe
   coefficient `1/3`.  The sharper `1/2` coefficient is not valid uniformly at nonsquare
   endpoints, so this version is the robust interface for the global prime-counting theorem. -/
theorem eventually_sqrt_log_lower_third :
    ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      0 < Real.log (X / m : ℕ) ∧
        (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ Real.log (X / m : ℕ) := by
  filter_upwards [eventually_ge_atTop (27 : ℕ)] with X hX m hm
  have hs3 : 3 ≤ Nat.sqrt X := by
    have : 9 ≤ X := by omega
    exact (Nat.le_sqrt).2 (by omega)
  have hs_sq : (Nat.sqrt X) * (Nat.sqrt X) ≤ X := Nat.sqrt_le X
  have hs_cube : X ≤ (Nat.sqrt X) ^ 3 := by
    have hlt : X < (Nat.sqrt X + 1) ^ 2 := by
      exact (Nat.sqrt_lt').mp (Nat.lt_succ_self (Nat.sqrt X))
    nlinarith
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmle : m ≤ Nat.sqrt X := (Finset.mem_Icc.mp hm).2
  have hdiv : Nat.sqrt X ≤ X / m := by
    apply (Nat.le_div_iff_mul_le hm0).2
    exact (Nat.mul_le_mul_left _ hmle).trans hs_sq
  have hspos : 0 < (Nat.sqrt X : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hs3)
  have hdivR : ((Nat.sqrt X : ℕ) : ℝ) ≤ ((X / m : ℕ) : ℝ) := by
    exact_mod_cast hdiv
  have hlogdiv : Real.log (Nat.sqrt X : ℝ) ≤ Real.log (X / m : ℕ) := by
    exact Real.log_le_log hspos hdivR
  have hXpowR : (X : ℝ) ≤ (((Nat.sqrt X) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hs_cube
  have hlogpow : Real.log (X : ℝ) ≤ 3 * Real.log (Nat.sqrt X : ℝ) := by
    calc
      Real.log (X : ℝ) ≤ Real.log (((Nat.sqrt X) ^ 3 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) hXpowR
      _ = 3 * Real.log (Nat.sqrt X : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        ring
  have hthird : (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) := by
    nlinarith
  have hlogdivpos : 0 < Real.log (X / m : ℕ) := by
    have hthree : (3 : ℝ) ≤ (X / m : ℕ) := by
      exact_mod_cast (hs3.trans hdiv)
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hthree)
  exact ⟨hlogdivpos, hthird.trans hlogdiv⟩

/- The quotient side condition is also eventual: once `X ≥ (N+1)^2`, every quotient with
   `m≤√X` is at least `N`. -/
theorem eventually_sqrt_quotient_ge (N : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Icc 1 (Nat.sqrt X), N ≤ X / m := by
  filter_upwards [eventually_ge_atTop ((N + 1) ^ 2)] with X hX m hm
  have hsN : N ≤ Nat.sqrt X := by
    apply (Nat.le_sqrt).2
    nlinarith
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmle : m ≤ Nat.sqrt X := (Finset.mem_Icc.mp hm).2
  have hdiv : Nat.sqrt X ≤ X / m := by
    apply (Nat.le_div_iff_mul_le hm0).2
    exact (Nat.mul_le_mul_left _ hmle).trans (Nat.sqrt_le X)
  exact hsN.trans hdiv

/- A quantitative split for the prime-counting reindexing.  It isolates the only local input
   needed to make the large-prime branch o(X): a `C X/(m log X)` bound for the range
   `m ≤ √X`; the complementary tail is handled by `π(y) ≤ y` and the inverse-square sum. -/
theorem primeCounting_reindexed_le_of_sqrt_pointwise
    (X : ℕ) {C : ℝ}
    (hX : 4 ≤ X) (hC : 0 ≤ C)
    (hsmall : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      (Nat.primeCounting (X / m) : ℝ) ≤
        C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ))) :
    (∑ m ∈ Finset.Icc 1 X,
      ((Nat.primeCounting (X / m) : ℕ) : ℝ) / (m : ℝ)) ≤
      2 * C * (X : ℝ) / Real.log (X : ℝ) +
        2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by
    have : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
    exact this)
  have hsqrtX : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  let g : ℕ → ℝ := fun m ↦
    ((Nat.primeCounting (X / m) : ℕ) : ℝ) / (m : ℝ)
  have hsplit :
      (∑ m ∈ Finset.Icc 1 X, g m) =
        (∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ m ≤ Nat.sqrt X), g m) +
          ∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ ¬m ≤ Nat.sqrt X), g m := by
    simpa [g] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 X)
        (p := fun m ↦ m ≤ Nat.sqrt X) (f := g)).symm
  have hsmall_sum :
      (∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ m ≤ Nat.sqrt X), g m) ≤
        2 * C * (X : ℝ) / Real.log (X : ℝ) := by
    have hsub : (Finset.Icc 1 X).filter (fun m ↦ m ≤ Nat.sqrt X) ⊆
        Finset.Icc 1 (Nat.sqrt X) := by
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm'.1).1, hm'.2⟩
    calc
      (∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ m ≤ Nat.sqrt X), g m) ≤
          ∑ m ∈ (Finset.Icc 1 (Nat.sqrt X)), g m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m hm _
        exact div_nonneg (by positivity) (by exact_mod_cast (Nat.zero_le m))
      _ ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt X),
          C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ)) / (m : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact div_le_div_of_nonneg_right (hsmall m hm)
          (by exact_mod_cast (Nat.zero_le m))
      _ = ∑ m ∈ Finset.Icc 1 (Nat.sqrt X),
          (C * (X : ℝ) / Real.log (X : ℝ)) * ((m : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : (m : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        field_simp [hm0]
      _ = (C * (X : ℝ) / Real.log (X : ℝ)) *
          (∑ m ∈ Finset.Icc 1 (Nat.sqrt X), ((m : ℝ) ^ 2)⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * C * (X : ℝ) / Real.log (X : ℝ) := by
        have hsqrtpos : 1 ≤ Nat.sqrt X := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.sqrt_pos.2 (by omega : 0 < X)))
        have hsumsq := sum_inv_sq_Icc_le_two (Nat.sqrt X) hsqrtpos
        have hfactor : 0 ≤ C * (X : ℝ) / Real.log (X : ℝ) := by positivity
        calc
          (C * (X : ℝ) / Real.log (X : ℝ)) *
              (∑ m ∈ Finset.Icc 1 (Nat.sqrt X), ((m : ℝ) ^ 2)⁻¹) ≤
              (C * (X : ℝ) / Real.log (X : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left hsumsq hfactor
          _ = 2 * C * (X : ℝ) / Real.log (X : ℝ) := by ring
  have hlarge_sum :
      (∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ ¬m ≤ Nat.sqrt X), g m) ≤
        2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
    have hsub : (Finset.Icc 1 X).filter (fun m ↦ ¬m ≤ Nat.sqrt X) ⊆
        Finset.Ioo (Nat.sqrt X) (X + 1) := by
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmI := Finset.mem_Icc.mp hm'.1
      exact Finset.mem_Ioo.mpr ⟨Nat.lt_of_not_ge hm'.2, Nat.lt_succ_of_le hmI.2⟩
    calc
      (∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ ¬m ≤ Nat.sqrt X), g m) ≤
          ∑ m ∈ (Finset.Icc 1 X).filter (fun m ↦ ¬m ≤ Nat.sqrt X),
            (X : ℝ) * ((m : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : 0 < m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
        have hm0r : 0 < (m : ℝ) := by exact_mod_cast hm0
        have hpiNat := primeCounting_le_self (X / m)
        have hpiReal : (Nat.primeCounting (X / m) : ℝ) ≤
            ((X / m : ℕ) : ℝ) := by exact_mod_cast hpiNat
        have hpile : (Nat.primeCounting (X / m) : ℝ) ≤
            (X : ℝ) / (m : ℝ) := hpiReal.trans Nat.cast_div_le
        have hdiv := div_le_div_of_nonneg_right hpile hm0r.le
        calc
          g m ≤ ((X : ℝ) / (m : ℝ)) / (m : ℝ) := by simpa [g] using hdiv
          _ = (X : ℝ) * ((m : ℝ) ^ 2)⁻¹ := by field_simp [ne_of_gt hm0r]
      _ ≤ ∑ m ∈ Finset.Ioo (Nat.sqrt X) (X + 1),
            (X : ℝ) * ((m : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m hm _
        positivity
      _ = (X : ℝ) * (∑ m ∈ Finset.Ioo (Nat.sqrt X) (X + 1),
            ((m : ℝ) ^ 2)⁻¹) := by rw [Finset.mul_sum]
      _ ≤ (X : ℝ) * (2 / ((Nat.sqrt X : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left
          (sum_Ioo_inv_sq_le (α := ℝ) (Nat.sqrt X) (X + 1))
        positivity
      _ = 2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by ring
  rw [hsplit]
  linarith

theorem sum_primeFactorLarge_harmonic_le_sum_log_weight (X : ℕ) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      ∑ p ∈ Finset.Icc (Nat.sqrt X + 1) X,
        (1 + Real.log (X / p : ℕ)) := by
  have hsub := primeFactorLargeBaseSet_subset_Icc X
  calc
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
        ∑ p ∈ Finset.Icc (Nat.sqrt X + 1) X, (harmonic (X / p) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      have hnonneg : (0 : ℚ) ≤ harmonic (X / p) := by
        rw [harmonic_eq_sum_Icc]
        positivity
      exact_mod_cast hnonneg
    _ ≤ ∑ p ∈ Finset.Icc (Nat.sqrt X + 1) X,
        (1 + Real.log (X / p : ℕ)) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
        (harmonic_le_one_add_log (X / p))

/- Reindexing identity for a harmonic prime sum.  It swaps the order of the finite `(p,m)`
   pairs and expresses the result as a divisor-count weighted sum over `m`; this is the natural
   finite form for inserting a short-interval prime-counting estimate. -/
theorem sum_harmonic_div_reindex (X : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, (harmonic (X / p) : ℝ)) =
      ∑ m ∈ Finset.Icc 1 X,
        (((P.filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) / (m : ℝ) := by
  let S : Finset ((_ : ℕ) × ℕ) := P.sigma (fun p ↦ Finset.Icc 1 (X / p))
  let T : Finset ((_ : ℕ) × ℕ) :=
    (Finset.Icc 1 X).sigma (fun m ↦ P.filter (fun p ↦ p ≤ X / m))
  have hleft :
      (∑ p ∈ P, (harmonic (X / p) : ℝ)) =
        ∑ z ∈ S, (((z.2 : ℕ) : ℝ)⁻¹) := by
    calc
      (∑ p ∈ P, (harmonic (X / p) : ℝ)) =
          ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 (X / p), (((m : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ = ∑ z ∈ S, (((z.2 : ℕ) : ℝ)⁻¹) := by
        rw [Finset.sum_sigma']
  have hswap :
      (∑ z ∈ S, (((z.2 : ℕ) : ℝ)⁻¹)) =
        ∑ w ∈ T, (((w.1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_bij (s := S) (t := T)
      (fun (z : Σ _ : ℕ, ℕ) _ ↦ (⟨z.2, z.1⟩ : Σ _ : ℕ, ℕ))
    · intro z hz
      have hzS : z ∈ S := by simpa [S] using hz
      have hsig := Finset.mem_sigma.mp hzS
      have hpP : z.1 ∈ P := hsig.1
      have hmI : z.2 ∈ Finset.Icc 1 (X / z.1) := hsig.2
      have hp0 : 0 < z.1 := hP z.1 hpP
      have hm1 : 1 ≤ z.2 := (Finset.mem_Icc.mp hmI).1
      have hm0 : 0 < z.2 := by omega
      have hmX : z.2 ≤ X := by
        exact (Finset.mem_Icc.mp hmI).2.trans
          (Nat.div_le_self X z.1)
      have hmul : z.2 * z.1 ≤ X :=
        (Nat.le_div_iff_mul_le hp0).mp (Finset.mem_Icc.mp hmI).2
      have hpdiv : z.1 ≤ X / z.2 := by
        apply (Nat.le_div_iff_mul_le hm0).2
        simpa [Nat.mul_comm] using hmul
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hm1, hmX⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hpP, hpdiv⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      cases z₁ with
      | mk p₁ m₁ =>
        cases z₂ with
        | mk p₂ m₂ =>
          have hm : m₁ = m₂ := congrArg Sigma.fst heq
          have hp : p₁ = p₂ :=
            congrArg (fun z : Σ _ : ℕ, ℕ ↦ z.2) heq
          cases hm
          cases hp
          rfl
    · intro w hw
      have hwT : w ∈ T := by simpa [T] using hw
      have hsig := Finset.mem_sigma.mp hwT
      have hmI : w.1 ∈ Finset.Icc 1 X := hsig.1
      have hpf := Finset.mem_filter.mp hsig.2
      have hpP : w.2 ∈ P := hpf.1
      have hpdiv : w.2 ≤ X / w.1 := hpf.2
      have hm1 : 1 ≤ w.1 := (Finset.mem_Icc.mp hmI).1
      have hm0 : 0 < w.1 := Nat.zero_lt_of_lt hm1
      have hmul' : w.2 * w.1 ≤ X :=
        (Nat.le_div_iff_mul_le hm0).mp hpdiv
      have hmul : w.1 * w.2 ≤ X := by
        simpa [Nat.mul_comm] using hmul'
      have hmdiv : w.1 ≤ X / w.2 := by
        have hp0 : 0 < w.2 := hP w.2 hpP
        apply (Nat.le_div_iff_mul_le hp0).2
        simpa [Nat.mul_comm] using hmul
      refine ⟨(⟨w.2, w.1⟩ : Σ _ : ℕ, ℕ), ?_, rfl⟩
      apply Finset.mem_sigma.mpr
      exact ⟨hpP, Finset.mem_Icc.mpr ⟨hm1, hmdiv⟩⟩
    · intro z hz
      rfl
  have hright :
      (∑ w ∈ T, (((w.1 : ℕ) : ℝ)⁻¹)) =
        ∑ m ∈ Finset.Icc 1 X,
          (((P.filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) / (m : ℝ) := by
    calc
      (∑ w ∈ T, (((w.1 : ℕ) : ℝ)⁻¹)) =
          ∑ m ∈ Finset.Icc 1 X,
            ∑ p ∈ P.filter (fun p ↦ p ≤ X / m), (((m : ℕ) : ℝ)⁻¹) := by
        rw [Finset.sum_sigma']
      _ = ∑ m ∈ Finset.Icc 1 X,
          (((P.filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) / (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [div_eq_mul_inv, mul_comm]
  exact hleft.trans (hswap.trans hright)

/- The large-prime branch is now in the exact reindexed form used by a
   short-interval prime-counting certificate. -/
theorem sum_primeFactorLarge_harmonic_eq_reindexed (X : ℕ) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) =
      ∑ m ∈ Finset.Icc 1 X,
        ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
          (m : ℝ) := by
  apply sum_harmonic_div_reindex X (primeFactorLargeBaseSet X)
  intro p hp
  exact (primeFactorLargeBaseSet_all_prime X p hp).pos

theorem sum_primeFactorLarge_cutoff_weight_eq_reindexed (X : ℕ) :
    (∑ q ∈ primeFactorLargeKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))) =
      ∑ m ∈ Finset.Icc 1 X,
        ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
          (m : ℝ) := by
  calc
    (∑ q ∈ primeFactorLargeKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) =
        ∑ q ∈ primeFactorLargeKeySet X, (harmonic (X / q.1) : ℝ) :=
      sum_primeFactorLarge_cutoff_weight_eq_harmonic X
    _ =
        ∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ) :=
      sum_primeFactorLarge_harmonic_eq_sum_base_harmonic X
    _ = _ := sum_primeFactorLarge_harmonic_eq_reindexed X

/- A certificate-friendly inequality: any pointwise bound on the filtered prime count
   can be inserted after the finite reindexing without unfolding the pair bookkeeping again. -/
theorem sum_harmonic_div_le_of_filter_card
    (X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (C : ℕ → ℝ)
    (hC : ∀ m ∈ Finset.Icc 1 X,
      (((P.filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) ≤ C m) :
    (∑ p ∈ P, (harmonic (X / p) : ℝ)) ≤
      ∑ m ∈ Finset.Icc 1 X, C m / (m : ℝ) := by
  rw [sum_harmonic_div_reindex X P hP]
  apply Finset.sum_le_sum
  intro m hm
  have hm0r : (0 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.zero_le m)
  exact div_le_div_of_nonneg_right (hC m hm) hm0r

theorem sum_primeFactorLarge_harmonic_le_reindexed_Icc (X : ℕ) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      ∑ m ∈ Finset.Icc 1 X,
        ((((Finset.Icc (Nat.sqrt X + 1) (X / m)).card : ℕ) : ℝ) / (m : ℝ)) := by
  apply sum_harmonic_div_le_of_filter_card X (primeFactorLargeBaseSet X)
    (fun p hp ↦ (primeFactorLargeBaseSet_all_prime X p hp).pos)
    (fun m ↦ (((Finset.Icc (Nat.sqrt X + 1) (X / m)).card : ℕ) : ℝ))
  intro m hm
  exact_mod_cast primeFactorLargeBaseSet_filter_card_le_Icc_card X m

theorem sum_primeFactorLarge_harmonic_le_primeCounting_reindexed (X : ℕ) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      ∑ m ∈ Finset.Icc 1 X,
        (((Nat.primeCounting (X / m) : ℕ) : ℝ) / (m : ℝ)) := by
  apply sum_harmonic_div_le_of_filter_card X (primeFactorLargeBaseSet X)
    (fun p hp ↦ (primeFactorLargeBaseSet_all_prime X p hp).pos)
    (fun m ↦ ((Nat.primeCounting (X / m) : ℕ) : ℝ))
  intro m hm
  exact_mod_cast primeFactorLargeBaseSet_filter_card_le_primeCounting X m

theorem primeCounting_sqrt_pointwise_of_global_bound
    (X N : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hlogX : 0 < Real.log (X : ℝ))
    (hpi : ∀ y ≥ N,
      (Nat.primeCounting y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ))
    (hquot : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X), N ≤ X / m)
    (hlog : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      0 < Real.log (X / m : ℕ) ∧
        (1 / 2 : ℝ) * Real.log (X : ℝ) ≤ Real.log (X / m : ℕ)) :
    ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      (Nat.primeCounting (X / m) : ℝ) ≤
        2 * C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ)) := by
  intro m hm
  have hpi' := hpi (X / m) (hquot m hm)
  have hlog' := hlog m hm
  have hcast : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) := Nat.cast_div_le
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hm0r : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hnum_nonneg : 0 ≤ C * ((X / m : ℕ) : ℝ) := by positivity
  have hden_half : 0 < (1 / 2 : ℝ) * Real.log (X : ℝ) := by positivity
  have hstep1 : C * ((X / m : ℕ) : ℝ) / Real.log (X / m : ℕ) ≤
      C * ((X / m : ℕ) : ℝ) / ((1 / 2 : ℝ) * Real.log (X : ℝ)) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_half hlog'.2
  have hstep2 : C * ((X / m : ℕ) : ℝ) / ((1 / 2 : ℝ) * Real.log (X : ℝ)) ≤
      C * ((X : ℝ) / (m : ℝ)) / ((1 / 2 : ℝ) * Real.log (X : ℝ)) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hcast hC
    · exact le_of_lt hden_half
  calc
    (Nat.primeCounting (X / m) : ℝ) ≤
        C * ((X / m : ℕ) : ℝ) / Real.log (X / m : ℕ) := hpi'
    _ ≤ C * ((X : ℝ) / (m : ℝ)) / ((1 / 2 : ℝ) * Real.log (X : ℝ)) :=
      hstep1.trans hstep2
    _ = 2 * C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ)) := by
      field_simp [hm0r.ne', hlogX.ne']

/- A robust 1/3-log variant of the preceding transfer.  It is the form that can be discharged
   automatically by `eventually_sqrt_log_lower_third`; the resulting constant is 3 instead of 2. -/
theorem primeCounting_sqrt_pointwise_of_global_bound_third
    (X N : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hlogX : 0 < Real.log (X : ℝ))
    (hpi : ∀ y ≥ N,
      (Nat.primeCounting y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ))
    (hquot : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X), N ≤ X / m)
    (hlog : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      0 < Real.log (X / m : ℕ) ∧
        (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ Real.log (X / m : ℕ)) :
    ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      (Nat.primeCounting (X / m) : ℝ) ≤
        3 * C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ)) := by
  intro m hm
  have hpi' := hpi (X / m) (hquot m hm)
  have hlog' := hlog m hm
  have hcast : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) := Nat.cast_div_le
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hm0r : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hnum_nonneg : 0 ≤ C * ((X / m : ℕ) : ℝ) := by positivity
  have hden_third : 0 < (1 / 3 : ℝ) * Real.log (X : ℝ) := by positivity
  have hstep1 : C * ((X / m : ℕ) : ℝ) / Real.log (X / m : ℕ) ≤
      C * ((X / m : ℕ) : ℝ) / ((1 / 3 : ℝ) * Real.log (X : ℝ)) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_third hlog'.2
  have hstep2 : C * ((X / m : ℕ) : ℝ) / ((1 / 3 : ℝ) * Real.log (X : ℝ)) ≤
      C * ((X : ℝ) / (m : ℝ)) / ((1 / 3 : ℝ) * Real.log (X : ℝ)) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hcast hC
    · exact le_of_lt hden_third
  calc
    (Nat.primeCounting (X / m) : ℝ) ≤
        C * ((X / m : ℕ) : ℝ) / Real.log (X / m : ℕ) := hpi'
    _ ≤ C * ((X : ℝ) / (m : ℝ)) / ((1 / 3 : ℝ) * Real.log (X : ℝ)) :=
      hstep1.trans hstep2
    _ = 3 * C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ)) := by
      field_simp [hm0r.ne', hlogX.ne']

theorem sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound
    (X : ℕ) {C : ℝ}
    (hX : 4 ≤ X) (hC : 0 ≤ C)
    (hsmall : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      (Nat.primeCounting (X / m) : ℝ) ≤
        C * (X : ℝ) / ((m : ℝ) * Real.log (X : ℝ))) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      2 * C * (X : ℝ) / Real.log (X : ℝ) +
        2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
  calc
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 X,
          (((Nat.primeCounting (X / m) : ℕ) : ℝ) / (m : ℝ)) :=
      sum_primeFactorLarge_harmonic_le_primeCounting_reindexed X
    _ ≤ _ := primeCounting_reindexed_le_of_sqrt_pointwise X hX hC hsmall

theorem sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound_of_global_primeCounting
    (X N : ℕ) {C : ℝ}
    (hX : 4 ≤ X) (hC : 0 ≤ C) (hlogX : 0 < Real.log (X : ℝ))
    (hpi : ∀ y ≥ N,
      (Nat.primeCounting y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ))
    (hquot : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X), N ≤ X / m)
    (hlog : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      0 < Real.log (X / m : ℕ) ∧
        (1 / 2 : ℝ) * Real.log (X : ℝ) ≤ Real.log (X / m : ℕ)) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      4 * C * (X : ℝ) / Real.log (X : ℝ) +
        2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
  have hsmall' := primeCounting_sqrt_pointwise_of_global_bound X N hC hlogX hpi hquot hlog
  have hbound := sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound X hX (by positivity : 0 ≤ 2 * C)
    hsmall'
  convert hbound using 1
  ring

/- The automatic 1/3-log route gives a fully explicit large-branch bound from the global
   prime-counting estimate, with no local `m`-by-`m` side condition left to the caller. -/
theorem sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound_of_global_primeCounting_third
    (X N : ℕ) {C : ℝ}
    (hX : 4 ≤ X) (hC : 0 ≤ C) (hlogX : 0 < Real.log (X : ℝ))
    (hpi : ∀ y ≥ N,
      (Nat.primeCounting y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ))
    (hquot : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X), N ≤ X / m)
    (hlog : ∀ m ∈ Finset.Icc 1 (Nat.sqrt X),
      0 < Real.log (X / m : ℕ) ∧
        (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ Real.log (X / m : ℕ)) :
    (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
      6 * C * (X : ℝ) / Real.log (X : ℝ) +
        2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
  have hsmall' := primeCounting_sqrt_pointwise_of_global_bound_third X N hC hlogX hpi hquot hlog
  have hbound := sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound X hX
    (by positivity : 0 ≤ 3 * C) hsmall'
  convert hbound using 1
  ring

/- The tail term is itself asymptotically negligible: `Nat.sqrt X + 1` dominates the real
   square root. -/
theorem tendsto_inv_nat_sqrt_add_one_zero :
    Tendsto (fun X : ℕ ↦ 1 / ((Nat.sqrt X : ℝ) + 1)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun X : ℕ ↦ Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ) + 1) atTop atTop := by
    exact Filter.tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun X ↦ Real.real_sqrt_le_nat_sqrt_succ)) hsqrt
  simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden

/- Consequently the large-prime harmonic branch is `o(X)` under the already formalized global
   prime-counting bound.  This theorem closes the entire large-branch analytic interface; the
   remaining H(X) difficulty is confined to the small-prime branch. -/
theorem tendsto_sum_primeFactorLarge_harmonic_div_self_of_global_primeCounting
    (N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hpi : ∀ y ≥ N,
      (Nat.primeCounting y : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ)) :
    Tendsto (fun X : ℕ ↦
      (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloginv : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hterm1 : Tendsto (fun X : ℕ ↦ 6 * C / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa [one_div, div_eq_mul_inv, mul_assoc] using hloginv.const_mul (6 * C)
  have hterm2 : Tendsto (fun X : ℕ ↦ 2 / ((Nat.sqrt X : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div, div_eq_mul_inv, mul_assoc] using
      (tendsto_inv_nat_sqrt_add_one_zero.const_mul 2)
  have hupper : Tendsto (fun X : ℕ ↦
      6 * C / Real.log (X : ℝ) + 2 / ((Nat.sqrt X : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using hterm1.add hterm2
  have hbound : ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
        6 * C * (X : ℝ) / Real.log (X : ℝ) +
          2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := by
    have hlogpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
      exact hlog.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [eventually_ge_atTop (4 : ℕ), hlogpos,
      eventually_sqrt_quotient_ge N, eventually_sqrt_log_lower_third]
      with X hX hlogX hquot hlogthird
    exact sum_primeFactorLarge_harmonic_le_explicit_sqrt_bound_of_global_primeCounting_third
      X N hX hC hlogX hpi hquot hlogthird
  have hnonneg : ∀ X : ℕ,
      0 ≤ ∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ) := by
    intro X
    apply Finset.sum_nonneg
    intro p hp
    have hq : (0 : ℚ) ≤ harmonic (X / p) := by
      rw [harmonic_eq_sum_Icc]
      positivity
    exact_mod_cast hq
  have hratio : ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) / (X : ℝ) ≤
        6 * C / Real.log (X : ℝ) + 2 / ((Nat.sqrt X : ℝ) + 1) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with X hX hXp
    have hXpR : 0 < (X : ℝ) := by exact_mod_cast hXp
    apply (div_le_iff₀ hXpR).2
    calc
      (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) ≤
          6 * C * (X : ℝ) / Real.log (X : ℝ) +
            2 * (X : ℝ) / ((Nat.sqrt X : ℝ) + 1) := hX
      _ = (X : ℝ) * (6 * C / Real.log (X : ℝ) +
          2 / ((Nat.sqrt X : ℝ) + 1)) := by ring_nf
      _ ≤ (6 * C / Real.log (X : ℝ) +
          2 / ((Nat.sqrt X : ℝ) + 1)) * (X : ℝ) := by
            simp [mul_comm]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦
      div_nonneg (hnonneg X) (by positivity))
  · exact hratio
  · exact hupper

/- LeanPool's theorem already supplies the required global estimate, so the preceding conditional
   result has an unconditional project-level specialization. -/
theorem tendsto_sum_primeFactorLarge_harmonic_div_self_of_LeanPool :
    Tendsto (fun X : ℕ ↦
      (∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)) /
        (X : ℝ)) atTop (𝓝 0) := by
  obtain ⟨N, C, hC, hpi⟩ := Upstream.primeCounting_le_mul_bound_nonneg
  exact tendsto_sum_primeFactorLarge_harmonic_div_self_of_global_primeCounting N hC hpi

theorem summatory_f_div_le_small_add_large_cutoff_reindexed (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) +
      ∑ m ∈ Finset.Icc 1 X,
        ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
          (m : ℝ) := by
  let g : (ℕ × ℕ) → ℝ := fun q ↦
    (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
      (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
        q.1 ^ (q.2 - 1) : ℕ) : ℝ))
  calc
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        ∑ q ∈ primeFactorKeySet X, g q := by
      simpa [g] using summatory_f_div_le_sum_primeFactor_key_harmonic_prime_divisor_cutoff X
    _ = (∑ q ∈ primeFactorSmallKeySet X, g q) +
          ∑ q ∈ primeFactorLargeKeySet X, g q := by
      simpa [g, primeFactorSmallKeySet, primeFactorLargeKeySet, Nat.not_le] using
        (Finset.sum_filter_add_sum_filter_not (s := primeFactorKeySet X)
          (p := fun q ↦ q.1 ≤ Nat.sqrt X) (f := g)).symm
    _ = (∑ q ∈ primeFactorSmallKeySet X, g q) +
          ∑ m ∈ Finset.Icc 1 X,
            ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
              (m : ℝ) := by
      rw [sum_primeFactorLarge_cutoff_weight_eq_reindexed]

/- Once the large-prime branch is known to be `o(X)`, a cutoff estimate for
   the small-prime branch transfers directly to the full summatory function.
   This is the main bridge from the finite decomposition to the remaining
   analytic certificate for `H`. -/
theorem summatory_f_div_le_of_small_cutoff_bound_and_global_primeCounting
    {C : ℝ}
    (hsmall : ∀ᶠ X : ℕ in atTop,
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
          (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
            q.1 ^ (q.2 - 1) : ℕ) : ℝ))) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        (C + 1) * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
  let smallTerm : ℕ → ℝ := fun X ↦
    ∑ q ∈ primeFactorSmallKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) *
        (harmonic ((min (X / q.1) (q.1 ^ q.2 - 1)) /
          q.1 ^ (q.2 - 1) : ℕ) : ℝ))
  let largeTerm : ℕ → ℝ := fun X ↦
    ∑ p ∈ primeFactorLargeBaseSet X, (harmonic (X / p) : ℝ)
  have hsmall' : ∀ᶠ X : ℕ in atTop,
      smallTerm X ≤ C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
    simpa [smallTerm] using hsmall
  have hlargeRatio : Tendsto (fun X : ℕ ↦ largeTerm X / (X : ℝ)) atTop (𝓝 0) := by
    simpa [largeTerm] using
      tendsto_sum_primeFactorLarge_harmonic_div_self_of_LeanPool
  have hlargeLe : ∀ᶠ X : ℕ in atTop, largeTerm X ≤ (X : ℝ) := by
    have hlt : ∀ᶠ X : ℕ in atTop, largeTerm X / (X : ℝ) < 1 :=
      hlargeRatio.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with X hX hXp
    have hXpR : 0 < (X : ℝ) := by exact_mod_cast hXp
    have := (div_lt_iff₀ hXpR).mp hX
    linarith
  have hL3 : Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using
      Real.tendsto_log_atTop.comp
        ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
          tendsto_natCast_atTop_atTop)
  have hL3one : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (Real.log (Real.log (X : ℝ))) :=
    hL3.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall', hlargeLe, hL3one,
    eventually_gt_atTop (0 : ℕ)] with X hS hL hL3X hXp
  have hdecomp := summatory_f_div_le_small_add_large_cutoff_reindexed X
  have hsum_reindexed :
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        smallTerm X +
          ∑ m ∈ Finset.Icc 1 X,
            ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
              (m : ℝ) := by
    simpa [smallTerm] using hdecomp
  have hsum :
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤ smallTerm X + largeTerm X := by
    calc
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
          smallTerm X +
            ∑ m ∈ Finset.Icc 1 X,
              ((((primeFactorLargeBaseSet X).filter (fun p ↦ p ≤ X / m)).card : ℕ) : ℝ) /
                (m : ℝ) := hsum_reindexed
      _ = smallTerm X + largeTerm X := by
        rw [← sum_primeFactorLarge_harmonic_eq_reindexed X]
  have hXnonneg : 0 ≤ (X : ℝ) := by positivity
  have hXle : (X : ℝ) ≤ (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hL3X hXnonneg
    simpa using this
  calc
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤ smallTerm X + largeTerm X := hsum
    _ ≤ C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) + (X : ℝ) :=
      add_le_add hS hL
    _ ≤ (C + 1) * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
      calc
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) + (X : ℝ) ≤
            C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) +
              (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) :=
          add_le_add_right hXle _
        _ = (C + 1) * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by ring

/- The preceding bridge also accepts the coarser untruncated `(p-1)` harmonic certificate. -/
theorem summatory_f_div_le_of_small_untruncated_bound_and_global_primeCounting
    {C : ℝ}
    (hsmall : ∀ᶠ X : ℕ in atTop,
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ))) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        (C + 1) * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))) := by
  apply summatory_f_div_le_of_small_cutoff_bound_and_global_primeCounting
  filter_upwards [hsmall] with X hX
  exact (sum_primeFactorSmall_cutoff_le_untruncated X).trans hX

theorem sum_primeFactor_key_harmonic_eq_small_add_large (X : ℕ) :
    (∑ q ∈ primeFactorKeySet X,
      (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ))) =
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ))) +
      ∑ q ∈ primeFactorLargeKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) := by
  classical
  simpa [primeFactorSmallKeySet, primeFactorLargeKeySet, Nat.not_le] using
    (Finset.sum_filter_add_sum_filter_not (s := primeFactorKeySet X)
      (p := fun q ↦ q.1 ≤ Nat.sqrt X)
      (f := fun q ↦
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)))).symm

theorem summatory_f_div_le_small_add_large_prime_divisor_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
      (∑ q ∈ primeFactorSmallKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ))) +
      ∑ q ∈ primeFactorLargeKeySet X,
        (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ) ) := by
  calc
    (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        ∑ q ∈ primeFactorKeySet X,
          (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) :=
      summatory_f_div_le_sum_primeFactor_key_harmonic_prime_divisor X
    _ = (∑ q ∈ primeFactorSmallKeySet X,
          (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ))) +
        ∑ q ∈ primeFactorLargeKeySet X,
          (((q.1 ^ (q.2 - 1) : ℕ) : ℝ) * (harmonic (q.1 - 1) : ℝ)) :=
      sum_primeFactor_key_harmonic_eq_small_add_large X

theorem f_div_le_of_tail_surplus_bound
    {n : ℕ} (hn : n ≠ 0) {A L C : ℝ}
    (hA : Real.log 2 ≤ A) (hAL : A ≤ L) (hL : 0 < L)
    (hTail :
      ∑ p ∈ Finset.Icc (⌊Real.exp A⌋₊ + 1) (⌊Real.exp L⌋₊),
        normalizedPositiveSurplus n L p ≤ C) :
    (f n : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) / L + Real.exp A + C := by
  rw [f_div_eq_normalizedPrimePowerSum (n := n)]
  exact normalizedPrimePowerSum_le_of_tail_surplus_bound hn hA hAL hL hTail

/-- The formula-(17) integer-base relaxation applied to the source function `f`.
The remaining work in Track C is therefore only the explicit finite surplus estimate and the
choice of its parameters; the conversion from prime powers to the relaxed base sum is complete. -/
theorem f_div_le_relaxed_prime_power_upper
    {n : ℕ} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L) {B : Finset ℕ}
    (hB : ∀ p ∈ n.primeFactors, Real.log (p : ℝ) < L → p ∈ B) :
    (f n : ℝ) / (n : ℝ) ≤
      Real.log (n : ℝ) / L +
        ∑ p ∈ B, normalizedPositiveSurplus n L p := by
  unfold f
  rw [Nat.cast_sum, Finset.sum_div]
  simpa [normalizedPrimePowerWeight] using
    (relaxed_prime_power_upper (n := n) hn hL hB)

/-- The number of distinct prime divisors of `n`. -/
noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

/- Every distinct prime divisor lies in `[1,n]`; consequently the number of distinct prime
   factors is at most `n` for positive `n`.  This small cardinality bound is useful when converting
   growth of `h` into elementary endpoint-gap estimates. -/
theorem omega_le_self {n : ℕ} (hn : n ≠ 0) : omega n ≤ n := by
  have hsub : n.primeFactors ⊆ Finset.Icc 1 n := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpone : 1 ≤ p := hpp.one_le
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd
    exact Finset.mem_Icc.mpr ⟨hpone, hpn⟩
  have hcard := Finset.card_le_card hsub
  simpa [omega] using hcard

/-- The non-one admissible terms which are prime powers.  This is used to separate the
single-prime contribution (already present in `f`) from genuinely multi-prime terms. -/
noncomputable def primePowerPart (A : Finset ℕ) : Finset ℕ :=
  (A.erase 1).filter IsPrimePow

/-- The non-one admissible terms having at least two distinct prime divisors. -/
noncomputable def multiPrimePart (A : Finset ℕ) : Finset ℕ :=
  (A.erase 1).filter (fun a ↦ ¬ IsPrimePow a)

lemma primePowerPart_subset_erase (A : Finset ℕ) : primePowerPart A ⊆ A.erase 1 := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

lemma multiPrimePart_subset_erase (A : Finset ℕ) : multiPrimePart A ⊆ A.erase 1 := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

lemma erase_eq_primePowerPart_union_multiPrimePart (A : Finset ℕ) :
    A.erase 1 = primePowerPart A ∪ multiPrimePart A := by
  ext a
  by_cases h : IsPrimePow a <;> simp [primePowerPart, multiPrimePart, h]

lemma primePowerPart_disjoint_multiPrimePart (A : Finset ℕ) :
    Disjoint (primePowerPart A) (multiPrimePart A) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

lemma primePowerPart_sum_add_multiPrimePart_sum (A : Finset ℕ) :
    (∑ a ∈ A.erase 1, a) =
      (∑ a ∈ primePowerPart A, a) + (∑ a ∈ multiPrimePart A, a) := by
  rw [erase_eq_primePowerPart_union_multiPrimePart, Finset.sum_union]
  exact primePowerPart_disjoint_multiPrimePart A

def IsAdmissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧
    (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
    ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n

noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter (IsAdmissible n)).sup fun A ↦ ∑ a ∈ A, a

/-- The canonical admissible family consisting of one largest allowed power for each prime
divisor. -/
noncomputable def primePowerTerms (n : ℕ) : Finset ℕ :=
  n.primeFactors.image fun p ↦ p ^ Nat.log p n

noncomputable def scale (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log (n : ℝ))

theorem eventually_scale_pos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hll
  unfold scale
  exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt hn)) hll

/- The standard Track-A scale is eventually monotone.  This is the order-theoretic fact needed
to pass from an endpoint-X good-count estimate to a pointwise lower bound at every `n ≤ X`. -/
theorem eventually_scale_mono : ∀ᶠ X : ℕ in atTop,
    ∀ ⦃y z : ℕ⦄, X ≤ y → y ≤ z → scale y ≤ scale z := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ))]
    with X hX hlogX hloglogX y z hXy hyz
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hyX : (X : ℝ) ≤ (y : ℝ) := by exact_mod_cast hXy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hyreal : 0 < (y : ℝ) := lt_of_lt_of_le hXreal hyX
  have hzreal : 0 < (z : ℝ) := lt_of_lt_of_le hXreal (hyX.trans hyzR)
  have hlogXY : Real.log (X : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hXreal hyX
  have hlogYZ : Real.log (y : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log hyreal hyzR
  have hylog : 0 < Real.log (y : ℝ) := lt_of_lt_of_le hlogX hlogXY
  have hllXY : Real.log (Real.log (X : ℝ)) ≤
      Real.log (Real.log (y : ℝ)) := Real.log_le_log hlogX hlogXY
  have hllYZ : Real.log (Real.log (y : ℝ)) ≤
      Real.log (Real.log (z : ℝ)) := Real.log_le_log hylog hlogYZ
  have hyllnonneg : 0 ≤ Real.log (Real.log (y : ℝ)) :=
    le_trans (by norm_num) (hloglogX.trans hllXY)
  unfold scale
  calc
    (y : ℝ) * Real.log (Real.log (y : ℝ)) ≤
        (z : ℝ) * Real.log (Real.log (y : ℝ)) :=
      mul_le_mul_of_nonneg_right hyzR hyllnonneg
    _ ≤ (z : ℝ) * Real.log (Real.log (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hllYZ hzreal.le

theorem tendsto_inv_scale_zero :
    Tendsto (fun n : ℕ ↦ 1 / scale n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hscale : Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.log (Real.log (n : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hloglog
  have hinv : Tendsto (fun n : ℕ ↦
      ((n : ℝ) * Real.log (Real.log (n : ℝ)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  convert hinv using 1
  simp only [scale, one_div]

noncomputable def maxUpTo (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sup g

/- The finite maximum is monotone in its endpoint.  This elementary fact is the order-theoretic
   ingredient needed to interpolate a subsequence estimate into an ordinary all-endpoint estimate.
   Keeping it generic avoids reproving the same finite-range inclusion for `f`, `F`, and `omega`. -/
theorem maxUpTo_mono {g : ℕ → ℕ} {x y : ℕ} (hxy : x ≤ y) :
    maxUpTo g x ≤ maxUpTo g y := by
  unfold maxUpTo
  apply Finset.sup_le
  intro n hn
  apply Finset.le_sup (f := g)
  exact Finset.mem_range.mpr (lt_of_lt_of_le
    (Finset.mem_range.mp hn) (Nat.succ_le_succ hxy))

/-- The normalizing scale for the maximal-order question. -/
noncomputable def maximalOrderScale (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log x / Real.log (Real.log x)

/- The maximal-order normalizer is eventually positive.  This elementary sign lemma is kept
   separate because every lower-bound squeeze for Track B needs the same denominator check. -/
theorem eventually_maximalOrderScale_pos : ∀ᶠ x : ℕ in atTop,
    0 < maximalOrderScale x := by
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun x : ℕ ↦ Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hlogx hloglogx hx
  unfold maximalOrderScale
  exact div_pos (mul_pos (by exact_mod_cast hx) hlogx) hloglogx

/- The normalizer itself tends to infinity.  We only need the elementary comparison
   `log log x ≤ log x` after the logarithms are positive; hence this theorem uses no
   prime-number-theoretic input and can be reused by all Track-B endpoint interpolations. -/
theorem tendsto_maximalOrderScale_atTop :
    Tendsto maximalOrderScale atTop atTop := by
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun x : ℕ ↦ Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hratio : ∀ᶠ x : ℕ in atTop,
      1 ≤ Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
      hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with x hlogx hloglogx
    have hll_le : Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
      exact Real.log_le_self hlogx.le
    exact (le_div_iff₀ hloglogx).2 (by simpa using hll_le)
  have hscale_ge : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ≤ maximalOrderScale x := by
    filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with x hratio hx
    have hxR : 0 ≤ (x : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hratio hxR
    simpa [maximalOrderScale, div_eq_mul_inv, mul_assoc] using hmul
  exact tendsto_atTop_mono' atTop hscale_ge tendsto_natCast_atTop_atTop

/- The scale grows faster than the endpoint itself.  This is the normalized form needed when a
   prime-selection certificate is stated as a proportion of `maximalOrderScale X`; the proof is
   the standard fact `log log X = o(log X)` followed by inversion on the positive tail. -/
theorem tendsto_maximalOrderScale_div_self_atTop :
    Tendsto (fun x : ℕ ↦ maximalOrderScale x / (x : ℝ)) atTop atTop := by
  have hzero : Tendsto (fun x : ℕ ↦
      Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    let L : ℕ → ℝ := fun x ↦ Real.log (x : ℝ)
    have hL : Tendsto L atTop atTop := by
      simpa [L, Function.comp_def] using
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have ho : (fun y : ℝ ↦ Real.log y) =o[atTop] id :=
      Real.isLittleO_log_id_atTop
    have h := ho.tendsto_div_nhds_zero.comp hL
    simpa [L, Function.comp_def] using h
  have hlog : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  have hloglog : ∀ᶠ x : ℕ in atTop, 0 < Real.log (Real.log (x : ℝ)) := by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))
  have hpos : ∀ᶠ x : ℕ in atTop,
      Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [hlog, hloglog] with x hx hllx
    exact Set.mem_Ioi.mpr (div_pos hllx hx)
  have hright : Tendsto (fun x : ℕ ↦
      Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards [hlog, hloglog, eventually_gt_atTop (0 : ℕ)] with x hx hllx hxnat
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hxnat
  simp only [Pi.inv_apply, maximalOrderScale]
  field_simp [hx.ne', hllx.ne', hxR.ne']

/-- Erdős's `h(x)`: the largest number of distinct prime factors below `x`. -/
/- The scale is eventually monotone on natural endpoints.  Writing
   `log x / log log x = u / log u` with `u = log x`, this follows from Mathlib's antitonicity
   of `log u / u` on `u ≥ exp 1`; multiplying by the increasing endpoint then preserves order.
   This closes one of the four analytic side conditions in the subsequence-cover adapter. -/
theorem eventually_maximalOrderScale_mono : ∀ᶠ x : ℕ in atTop,
    ∀ ⦃y z : ℕ⦄, x ≤ y → y ≤ z →
      maximalOrderScale y ≤ maximalOrderScale z := by
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (Real.exp 1))] with x hx
  intro y z hxy hyz
  have hxnat : 0 < x := by
    by_contra hx0
    have hxzero : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst x
    have hx' : Real.exp 1 ≤ (0 : ℝ) := by simpa using hx
    exact (not_le_of_gt (Real.exp_pos (1 : ℝ))) hx'
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxnat
  have hyx : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlogxy : Real.log (x : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hxpos hyx
  have hlogyz : Real.log (y : ℝ) ≤ Real.log (z : ℝ) := by
    have hypos : 0 < (y : ℝ) := lt_of_lt_of_le hxpos hyx
    exact Real.log_le_log hypos hyzR
  have hybase : Real.exp 1 ≤ Real.log (y : ℝ) := hx.trans hlogxy
  have hzbase : Real.exp 1 ≤ Real.log (z : ℝ) := hybase.trans hlogyz
  have hanti := Real.log_div_self_antitoneOn hybase hzbase hlogyz
  have hlogy : 0 < Real.log (y : ℝ) := by
    exact lt_of_lt_of_le (Real.exp_pos (1 : ℝ)) hybase
  have hlogz : 0 < Real.log (z : ℝ) := by
    exact lt_of_lt_of_le (Real.exp_pos (1 : ℝ)) hzbase
  have hlogypos : 0 < Real.log (Real.log (y : ℝ)) := by
    have hexp : (1 : ℝ) < Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact Real.log_pos (lt_of_lt_of_le hexp hybase)
  have hlogzpos : 0 < Real.log (Real.log (z : ℝ)) := by
    have hexp : (1 : ℝ) < Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact Real.log_pos (lt_of_lt_of_le hexp hzbase)
  have hypos : 0 < (y : ℝ) := lt_of_lt_of_le hxpos hyx
  have hratio : Real.log (y : ℝ) / Real.log (Real.log (y : ℝ)) ≤
      Real.log (z : ℝ) / Real.log (Real.log (z : ℝ)) := by
    apply (div_le_div_iff₀ hlogypos hlogzpos).2
    have hanti' : Real.log (Real.log (z : ℝ)) / Real.log (z : ℝ) ≤
        Real.log (Real.log (y : ℝ)) / Real.log (y : ℝ) := by
      simpa only [Function.comp_apply] using hanti
    have hcross := (div_le_div_iff₀ hlogz hlogy).mp hanti'
    nlinarith [hcross]
  have hprod : (y : ℝ) *
      (Real.log (y : ℝ) / Real.log (Real.log (y : ℝ))) ≤
      (z : ℝ) *
      (Real.log (z : ℝ) / Real.log (Real.log (z : ℝ))) := by
    calc
      (y : ℝ) * (Real.log (y : ℝ) / Real.log (Real.log (y : ℝ))) ≤
          (z : ℝ) * (Real.log (y : ℝ) / Real.log (Real.log (y : ℝ))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hyz) (by positivity)
      _ ≤ (z : ℝ) * (Real.log (z : ℝ) / Real.log (Real.log (z : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  simpa [maximalOrderScale, div_eq_mul_inv, mul_assoc] using hprod

/- If consecutive selected endpoints have asymptotically unit ratio, then the full
   normalizer `x log x / log log x` also has asymptotically unit adjacent ratio.  This
   removes a separate analytic scale-ratio certificate from the Track-B adapter. -/
theorem tendsto_maximalOrderScale_ratio_of_tendsto_endpoint_ratio
    (Xseq : ℕ → ℕ)
    (hXseq : Tendsto Xseq atTop atTop)
    (hstep : Tendsto (fun k : ℕ ↦
      (Xseq (k + 1) : ℝ) / (Xseq k : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun k : ℕ ↦
      maximalOrderScale (Xseq (k + 1)) / maximalOrderScale (Xseq k)) atTop (𝓝 1) := by
  have log_ratio_of_ratio : ∀ {u v : ℕ → ℝ},
      Tendsto u atTop atTop → Tendsto v atTop atTop →
      Tendsto (fun k : ℕ ↦ v k / u k) atTop (𝓝 1) →
      Tendsto (fun k : ℕ ↦ Real.log (v k) / Real.log (u k)) atTop (𝓝 1) := by
    intro u v hu hv hratio
    have hlogu : Tendsto (fun k : ℕ ↦ Real.log (u k)) atTop atTop :=
      Real.tendsto_log_atTop.comp hu
    have hu_pos : ∀ᶠ k : ℕ in atTop, 0 < u k :=
      hu.eventually (eventually_gt_atTop (0 : ℝ))
    have hv_pos : ∀ᶠ k : ℕ in atTop, 0 < v k :=
      hv.eventually (eventually_gt_atTop (0 : ℝ))
    have hlogratio : Tendsto (fun k : ℕ ↦ Real.log (v k / u k)) atTop (𝓝 0) := by
      have hc := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
      simpa [Function.comp_def] using hc.comp hratio
    have hquot : Tendsto (fun k : ℕ ↦ Real.log (v k / u k) / Real.log (u k))
        atTop (𝓝 0) := hlogratio.div_atTop hlogu
    have hlogupos : ∀ᶠ k : ℕ in atTop, 0 < Real.log (u k) := by
      filter_upwards [hlogu.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
      exact hk
    have hresult : Tendsto
        (fun k : ℕ ↦ (1 : ℝ) + Real.log (v k / u k) / Real.log (u k))
        atTop (𝓝 ((1 : ℝ) + 0)) := tendsto_const_nhds.add hquot
    have hresult' : Tendsto
        (fun k : ℕ ↦ (1 : ℝ) + Real.log (v k / u k) / Real.log (u k))
        atTop (𝓝 1) := by simpa using hresult
    refine hresult'.congr' ?_
    filter_upwards [hu_pos, hv_pos, hlogupos] with k huk hvk hloguk
    have hlogdiv : Real.log (v k / u k) = Real.log (v k) - Real.log (u k) :=
      Real.log_div hvk.ne' huk.ne'
    rw [hlogdiv]
    field_simp [hloguk.ne']
    ring
  have hXreal : Tendsto (fun k : ℕ ↦ (Xseq k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hXseq
  have hXnext : Tendsto (fun k : ℕ ↦ (Xseq (k + 1) : ℝ)) atTop atTop :=
    hXreal.comp (tendsto_add_atTop_nat 1)
  have hstep_inv : Tendsto (fun k : ℕ ↦
      (Xseq k : ℝ) / (Xseq (k + 1) : ℝ)) atTop (𝓝 1) := by
    have hinv := hstep.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [div_eq_mul_inv] using hinv
  have hlogRatio : Tendsto (fun k : ℕ ↦
      Real.log (Xseq (k + 1) : ℝ) / Real.log (Xseq k : ℝ)) atTop (𝓝 1) :=
    log_ratio_of_ratio hXreal hXnext hstep
  have hlogRatioRev : Tendsto (fun k : ℕ ↦
      Real.log (Xseq k : ℝ) / Real.log (Xseq (k + 1) : ℝ)) atTop (𝓝 1) :=
    log_ratio_of_ratio hXnext hXreal hstep_inv
  have hloglogA : Tendsto (fun k : ℕ ↦
      Real.log (Real.log (Xseq k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hXreal)
  have hloglogB : Tendsto (fun k : ℕ ↦
      Real.log (Real.log (Xseq (k + 1) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hXnext)
  have hloglogRatio : Tendsto (fun k : ℕ ↦
      Real.log (Real.log (Xseq k : ℝ)) /
        Real.log (Real.log (Xseq (k + 1) : ℝ))) atTop (𝓝 1) :=
    log_ratio_of_ratio (Real.tendsto_log_atTop.comp hXnext)
      (Real.tendsto_log_atTop.comp hXreal) hlogRatioRev
  have hprod : Tendsto (fun k : ℕ ↦
      ((Xseq (k + 1) : ℝ) / (Xseq k : ℝ)) *
        (Real.log (Xseq (k + 1) : ℝ) / Real.log (Xseq k : ℝ)) *
        (Real.log (Real.log (Xseq k : ℝ)) /
          Real.log (Real.log (Xseq (k + 1) : ℝ)))) atTop (𝓝 1) := by
    simpa using ((hstep.mul hlogRatio).mul hloglogRatio)
  have hpos : ∀ᶠ k : ℕ in atTop,
      0 < (Xseq k : ℝ) ∧ 0 < (Xseq (k + 1) : ℝ) ∧
      0 < Real.log (Xseq k : ℝ) ∧ 0 < Real.log (Xseq (k + 1) : ℝ) ∧
      0 < Real.log (Real.log (Xseq k : ℝ)) ∧
      0 < Real.log (Real.log (Xseq (k + 1) : ℝ)) := by
    filter_upwards [hXreal.eventually (eventually_gt_atTop (0 : ℝ)),
      hXnext.eventually (eventually_gt_atTop (0 : ℝ)),
      (Real.tendsto_log_atTop.comp hXreal).eventually (eventually_gt_atTop (0 : ℝ)),
      (Real.tendsto_log_atTop.comp hXnext).eventually (eventually_gt_atTop (0 : ℝ)),
      hloglogA.eventually (eventually_gt_atTop (0 : ℝ)),
      hloglogB.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hkn hla hlb hlla hllb
    exact ⟨hk, hkn, hla, hlb, hlla, hllb⟩
  refine hprod.congr' ?_
  filter_upwards [hpos] with k hk
  simp only [maximalOrderScale]
  field_simp [hk.1.ne', hk.2.1.ne', hk.2.2.1.ne', hk.2.2.2.1.ne',
    hk.2.2.2.2.1.ne', hk.2.2.2.2.2.ne']

noncomputable def h (x : ℕ) : ℕ := maxUpTo omega x

theorem maxUpTo_omega_le_self (x : ℕ) : maxUpTo omega x ≤ x := by
  unfold maxUpTo
  apply Finset.sup_le
  intro n hn
  have hnx : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hn0 : n = 0
  · simp [hn0, omega]
  · exact (omega_le_self hn0).trans hnx

/- The primorial supplies an explicit lower-bound family for the distinct-prime-factor maximum.
   This elementary bridge is useful for Track C: it records, without an asymptotic hypothesis,
   that the endpoint maximum `h` dominates the prime-counting function along primorial endpoints. -/
theorem omega_primorial_eq_primeCounting (k : ℕ) :
    omega (primorial k) = Nat.primeCounting k := by
  change (primorial k).primeFactors.card = Nat.primeCounting k
  rw [primeFactors_primorial]
  exact Nat.primesLE_card_eq_primeCounting k

theorem primeCounting_le_h_primorial (k : ℕ) :
    Nat.primeCounting k ≤ h (primorial k) := by
  have hmem : primorial k ∈ Finset.range (primorial k + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hmax : omega (primorial k) ≤ maxUpTo omega (primorial k) := by
    exact Finset.le_sup hmem
  simpa [h, omega_primorial_eq_primeCounting] using hmax

/- Finite lower-bound bridge for `h(X)`.  If `k` primes can be chosen below `Y` and their
product is at most `X`, then the product has exactly `k` distinct prime factors and therefore
forces `h(X) ≥ k`.  The analytic prime-counting estimate is deliberately kept as the separate
input `hcount`; no rate claim is hidden here. -/
theorem h_ge_of_prime_count_and_product_bound
    {X Y k : ℕ} (hcount : k ≤ Nat.primeCounting Y)
    (hprod : Y ^ k ≤ X) :
    k ≤ h X := by
  have hcard : k ≤ (Nat.primesLE Y).card := by
    simpa [Nat.primesLE_card_eq_primeCounting] using hcount
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (hSsub hp)
  have hple : ∀ p ∈ S, p ≤ Y := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hSsub hp)).1
  let N : ℕ := ∏ p ∈ S, p
  have hNpos : 0 < N := by
    dsimp [N]
    exact Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)
  have hNle : N ≤ Y ^ k := by
    dsimp [N]
    calc
      (∏ p ∈ S, p) ≤ Y ^ S.card := Finset.prod_le_pow_card S id Y hple
      _ = Y ^ k := by rw [hScard]
  have hNX : N ≤ X := hNle.trans hprod
  have hNprimeFactors : N.primeFactors = S := by
    dsimp [N]
    exact Nat.primeFactors_prod hprime
  have homegaN : omega N = k := by
    rw [omega, hNprimeFactors, hScard]
  have hmax : omega N ≤ h X := by
    unfold h
    apply Finset.le_sup
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hNX)
  exact homegaN ▸ hmax

/- Chebyshev's explicit lower bound `π(Y) ≥ (Y log 2 - log(Y+1))/log Y` can now be fed
directly into the preceding product bridge.  Only the numerical comparison selecting `k` and the
product budget remain to be proved in a concrete Track-C instantiation. -/
theorem h_ge_of_chebyshev_pi_lower
    {X Y k : ℕ} (_hY : 1 < Y)
    (hk : (k : ℝ) ≤
      (((Y : ℝ) * Real.log 2 - Real.log ((Y : ℝ) + 1)) /
        Real.log (Y : ℝ)))
    (hprod : Y ^ k ≤ X) :
    k ≤ h X := by
  have hpi : (k : ℝ) ≤ (Nat.primeCounting Y : ℝ) := by
    exact hk.trans (Chebyshev.pi_ge Y)
  have hcount : k ≤ Nat.primeCounting Y := by
    exact_mod_cast hpi
  exact h_ge_of_prime_count_and_product_bound hcount hprod

/- The product-budget side can be supplied in logarithmic form, which is the natural output of
   the report's choice `k ≈ log X / log Y`.  This bridge converts that analytic inequality into
   the natural-number power bound required by the finite primorial argument. -/
theorem h_ge_of_chebyshev_pi_lower_of_log_budget
    {X Y k : ℕ} (hX : 0 < X) (hY : 1 < Y)
    (hk : (k : ℝ) ≤
      (((Y : ℝ) * Real.log 2 - Real.log ((Y : ℝ) + 1)) /
        Real.log (Y : ℝ)))
    (hbudget : (k : ℝ) * Real.log (Y : ℝ) ≤ Real.log (X : ℝ)) :
    k ≤ h X := by
  have hY0 : 0 < Y := by omega
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY0
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hpowpos : 0 < ((Y ^ k : ℕ) : ℝ) := by positivity
  have hlogpow : Real.log ((Y ^ k : ℕ) : ℝ) =
      (k : ℝ) * Real.log (Y : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlog : Real.log ((Y ^ k : ℕ) : ℝ) ≤ Real.log (X : ℝ) := by
    rw [hlogpow]
    exact hbudget
  have hpowreal : ((Y ^ k : ℕ) : ℝ) ≤ (X : ℝ) :=
    (Real.log_le_log_iff hpowpos hXpos).mp hlog
  have hprod : Y ^ k ≤ X := by exact_mod_cast hpowreal
  exact h_ge_of_chebyshev_pi_lower hY hk hprod

/- Since the prime-counting function diverges, the preceding endpoint estimate already gives
   divergence of `h` along the primorial sequence.  This is an unconditional Track-C lemma;
   no prime-number-theorem asymptotic is needed here. -/
theorem tendsto_h_primorial :
    Tendsto (fun k : ℕ ↦ h (primorial k)) atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall primeCounting_le_h_primorial)
    Nat.tendsto_primeCounting

/- Monotonicity of the finite maximum interpolates the primorial subsequence divergence to all
   endpoints.  This is the basic growth fact needed before any finer maximal-order estimate. -/
theorem tendsto_h_atTop : Tendsto h atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  have hB : ∀ᶠ k : ℕ in atTop, B ≤ h (primorial k) :=
    (tendsto_atTop.1 tendsto_h_primorial) B
  obtain ⟨K, hK⟩ := (eventually_atTop.1 hB)
  have hK' : B ≤ h (primorial K) := hK K le_rfl
  filter_upwards [eventually_ge_atTop (primorial K)] with x hx
  exact hK'.trans (by simpa [h] using maxUpTo_mono hx)

/-- Erdős's `m(x)`: the largest value of `f` below `x`. -/
noncomputable def m (x : ℕ) : ℕ := maxUpTo f x

/-- The nonnegative gap `x h(x) - m(x)` in Erdős's original formula (17). -/
noncomputable def maximalOrderGap (x : ℕ) : ℕ := x * h x - m x

/-- The stronger scale proposed for the gap in the third proof candidate. -/
noncomputable def maximalOrderGapScale (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
    (Real.log (Real.log x)) ^ 2

/- The proposed formula-(17) scale really dominates `x`: this is elementary iterated-log
   arithmetic, independent of the endpoint-band estimate for `h(x)-m(x)`.  Keeping the proof
   here makes the exact source target reducible to a single eventual lower-bound lemma. -/
theorem tendsto_maximalOrderGapScale_div_self_atTop :
    Tendsto (fun x : ℕ ↦
      maximalOrderGapScale x / (x : ℝ)) atTop atTop := by
  have hzero : Tendsto (fun x : ℕ ↦
      Real.log (Real.log (x : ℝ)) ^ 2 / Real.log (x : ℝ)) atTop (𝓝 0) := by
    let L : ℕ → ℝ := fun x ↦ Real.log (x : ℝ)
    have hL : Tendsto L atTop atTop := by
      simpa [L, Function.comp_def] using
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have ho : (fun y : ℝ ↦ Real.log y ^ 2) =o[atTop] id :=
      Real.isLittleO_pow_log_id_atTop
    have h := ho.tendsto_div_nhds_zero.comp hL
    simpa [L, Function.comp_def] using h
  have hratio : Tendsto (fun x : ℕ ↦
      Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) ^ 2) atTop atTop := by
    have hlog : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
      have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
      exact h
    have hll : ∀ᶠ x : ℕ in atTop, 0 < Real.log (Real.log (x : ℝ)) := by
      have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))
      exact h
    have hpos : ∀ᶠ x : ℕ in atTop,
        Real.log (Real.log (x : ℝ)) ^ 2 / Real.log (x : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [hlog, hll] with x hx hllx
      exact Set.mem_Ioi.mpr (by positivity)
    have hright : Tendsto (fun x : ℕ ↦
        Real.log (Real.log (x : ℝ)) ^ 2 / Real.log (x : ℝ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
    have hinv := hright.inv_tendsto_nhdsGT_zero
    refine hinv.congr' ?_
    filter_upwards [hlog, hll] with x hx hllx
    dsimp
    field_simp
  have hthird : Tendsto (fun x : ℕ ↦
      Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using
      Real.tendsto_log_atTop.comp
        ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
          tendsto_natCast_atTop_atTop)
  have hmul := hratio.atTop_mul_atTop₀ hthird
  have hposx : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    exact_mod_cast hx
  refine hmul.congr' ?_
  filter_upwards [hposx] with x hx
  simp only [maximalOrderGapScale]
  field_simp

/- The proposed Track-C scale is eventually positive; this sign fact is needed when converting a
   ratio lower bound into the pointwise comparison `maximalOrderGapScale ≤ maximalOrderGap`. -/
theorem eventually_maximalOrderGapScale_pos :
    ∀ᶠ x : ℕ in atTop, 0 < maximalOrderGapScale x := by
  have hlog : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    exact h
  have hll : ∀ᶠ x : ℕ in atTop, 0 < Real.log (Real.log (x : ℝ)) := by
    have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))
    exact h
  have hlll : ∀ᶠ x : ℕ in atTop,
      0 < Real.log (Real.log (Real.log (x : ℝ))) := by
    have h := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_gt_atTop (0 : ℝ))
    exact h
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog, hll, hlll] with x hx h₁ h₂ h₃
  unfold maximalOrderGapScale
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  positivity

/-- Every admissible finite family supplies a lower bound for the defining maximum `F n`. -/
theorem sum_le_F_of_admissible {n : ℕ} {A : Finset ℕ} (hA : IsAdmissible n A) :
    ∑ a ∈ A, a ≤ F n := by
  unfold F
  apply Finset.le_sup (f := fun B ↦ ∑ a ∈ B, a)
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA⟩

/- The singleton `{n}` is always admissible for `n ≥ 2`.  This elementary baseline is useful
   when a later density argument is split into a trivial branch and a genuinely growing branch. -/
theorem self_le_F {n : ℕ} (hn : 2 ≤ n) : n ≤ F n := by
  have hA : IsAdmissible n ({n} : Finset ℕ) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
      subst a
      subst b
      exact False.elim (hab rfl)
    · intro a ha p hp hpa
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hpa
  simpa using sum_le_F_of_admissible hA

/-- If every member of an admissible family is at least `B`, the family contributes at least
`A.card * B` to `F n`. This is the final finite packing step in the density-one lower bound. -/
theorem card_mul_le_F_of_admissible {n B : ℕ} {A : Finset ℕ}
    (hA : IsAdmissible n A) (hlower : ∀ a ∈ A, B ≤ a) :
    A.card * B ≤ F n := by
  apply le_trans _ (sum_le_F_of_admissible hA)
  calc
    A.card * B = ∑ _a ∈ A, B := by simp
    _ ≤ ∑ a ∈ A, a := by
      gcongr with a ha
      exact hlower a ha

/- A finite-family interface for the Track A lower bound.  The analytic argument only has to
produce the indexed terms and verify these hypotheses; the image construction supplies the
official distinct-set definition of `F`. -/
theorem card_mul_le_F_of_pairwise_terms
    {ι : Type*} [DecidableEq ι] {n B : ℕ} (I : Finset ι) (term : ι → ℕ)
    (hinj : Set.InjOn term (I : Set ι))
    (hnontrivial : ∀ i ∈ I, 2 ≤ term i)
    (hlower : ∀ i ∈ I, B ≤ term i)
    (hupper : ∀ i ∈ I, term i ≤ n)
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j → Nat.Coprime (term i) (term j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ p, p.Prime → p ∣ term i → p ∣ n) :
    I.card * B ≤ F n := by
  let A : Finset ℕ := I.image term
  have hA : IsAdmissible n A := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      change a ∈ I.image term at ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact Finset.mem_Icc.mpr ⟨hnontrivial i hi, hupper i hi⟩
    · intro a ha b hb hab
      change a ∈ I.image term at ha
      change b ∈ I.image term at hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      apply hcop hi hj
      intro hij
      apply hab
      rw [hij]
    · intro a ha p pp hpa
      change a ∈ I.image term at ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact hprime hi p pp hpa
  have hsum : (∑ a ∈ A, a) = ∑ i ∈ I, term i := by
    change (∑ a ∈ I.image term, a) = ∑ i ∈ I, term i
    rw [Finset.sum_image]
    exact hinj
  calc
    I.card * B = ∑ _i ∈ I, B := by simp
    _ ≤ ∑ i ∈ I, term i := by
      gcongr with i hi
      exact hlower i hi
    _ = ∑ a ∈ A, a := hsum.symm
    _ ≤ F n := sum_le_F_of_admissible hA

/- Sum-valued companion of the preceding cardinality interface.  It is the right finite API when
the admissible terms have genuinely different sizes, as happens for prime-power products. -/
theorem sum_pairwise_terms_le_F
    {ι : Type*} [DecidableEq ι] {n : ℕ} (I : Finset ι) (term : ι → ℕ)
    (hinj : Set.InjOn term (I : Set ι))
    (hnontrivial : ∀ i ∈ I, 2 ≤ term i)
    (hupper : ∀ i ∈ I, term i ≤ n)
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (term i) (term j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ p, p.Prime → p ∣ term i → p ∣ n) :
    (∑ i ∈ I, term i) ≤ F n := by
  let A : Finset ℕ := I.image term
  have hA : IsAdmissible n A := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      change a ∈ I.image term at ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact Finset.mem_Icc.mpr ⟨hnontrivial i hi, hupper i hi⟩
    · intro a ha b hb hab
      change a ∈ I.image term at ha
      change b ∈ I.image term at hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      apply hcop hi hj
      intro hij
      apply hab
      rw [hij]
    · intro a ha p pp hpa
      change a ∈ I.image term at ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact hprime hi p pp hpa
  have hsum : (∑ a ∈ A, a) = ∑ i ∈ I, term i := by
    change (∑ a ∈ I.image term, a) = ∑ i ∈ I, term i
    rw [Finset.sum_image]
    exact hinj
  rw [← hsum]
  exact sum_le_F_of_admissible hA

/- The concrete two-window shape used by the fixed-loss route.  All analytic work is pushed into
   the maps `p,q`, the exponents `a,b`, and the displayed finite hypotheses; once those are
   supplied, the product terms are accepted by the official set-valued definition of `F`. -/
theorem card_mul_le_F_of_matched_power_products
    {ι : Type*} [DecidableEq ι] {n B : ℕ} (I : Finset ι)
    (p q a b : ι → ℕ)
    (hinj : Set.InjOn (fun i ↦ p i ^ a i * q i ^ b i) (I : Set ι))
    (hnontrivial : ∀ i ∈ I, 2 ≤ p i ^ a i * q i ^ b i)
    (hlower : ∀ i ∈ I, B ≤ p i ^ a i * q i ^ b i)
    (hupper : ∀ i ∈ I, p i ^ a i * q i ^ b i ≤ n)
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (p i ^ a i * q i ^ b i) (p j ^ a j * q j ^ b j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ p i ^ a i * q i ^ b i → s ∣ n) :
    I.card * B ≤ F n := by
  exact card_mul_le_F_of_pairwise_terms I
    (fun i ↦ p i ^ a i * q i ^ b i)
    hinj hnontrivial hlower hupper hcop hprime

/- Rotation-to-`F` packaging.  The logarithmic gap lemma in `Rotation` produces real interval
   bounds for each product; this wrapper converts those bounds to the natural-number positivity
   and upper-endpoint hypotheses expected by the admissible-family interface.  Consequently, a
   future analytic proof only has to provide the approximation/gap data and the explicit finite
   matching conditions. -/
theorem card_mul_le_F_of_rotation_power_products
    {ι : Type*} [DecidableEq ι] {n B : ℕ} (I : Finset ι)
    (p q a b : ι → ℕ) {L Q t C : ℝ}
    (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i)
    (hn : 0 < n) (hC : 0 < C) (hC_le_n : C ≤ (n : ℝ))
    (hLp : ∀ i ∈ I, L = Real.log (p i : ℝ))
    (hQq : ∀ i ∈ I, Q = Real.log (q i : ℝ))
    (htn : t = Real.log (n : ℝ))
    (hgap : ∀ i ∈ I,
      0 ≤ t - ((a i : ℝ) * L + (b i : ℝ) * Q))
    (hgapC : ∀ i ∈ I,
      t - ((a i : ℝ) * L + (b i : ℝ) * Q) ≤ Real.log C)
    (hnontrivial : ∀ i ∈ I, 2 ≤ p i ^ a i * q i ^ b i)
    (hinj : Set.InjOn (fun i ↦ p i ^ a i * q i ^ b i) (I : Set ι))
    (hlower : ∀ i ∈ I, B ≤ p i ^ a i * q i ^ b i)
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (p i ^ a i * q i ^ b i) (p j ^ a j * q j ^ b j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ p i ^ a i * q i ^ b i → s ∣ n) :
    I.card * B ≤ F n := by
  have hband : ∀ i ∈ I,
      (n : ℝ) / C ≤ ((p i ^ a i * q i ^ b i : ℕ) : ℝ) ∧
        ((p i ^ a i * q i ^ b i : ℕ) : ℝ) ≤ (n : ℝ) := by
    intro i hi
    exact power_product_mem_Icc_of_log_gap (hp i hi) (hq i hi) hn hC
      (hLp i hi) (hQq i hi) htn (hgap i hi) (hgapC i hi)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / C := by
    apply (le_div_iff₀ hC).2
    simpa using hC_le_n
  have hupper : ∀ i ∈ I, p i ^ a i * q i ^ b i ≤ n := by
    intro i hi
    exact_mod_cast (hband i hi).2
  exact card_mul_le_F_of_matched_power_products I p q a b
    hinj hnontrivial hlower hupper hcop hprime

/- Sum-valued rotation companion.  The cardinality version above deliberately replaces every
   product by a common lower bound.  When the approximation data give different product sizes,
   retaining the actual sum avoids that loss and is the natural interface for the sharp Track-A
   coefficient.  The only new work is the same logarithmic-band conversion to the admissibility
   bounds; the pairwise and prime-support obligations are reused unchanged. -/
theorem sum_le_F_of_rotation_power_products
    {ι : Type*} [DecidableEq ι] {n : ℕ} (I : Finset ι)
    (p q a b : ι → ℕ) {L Q t C : ℝ}
    (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i)
    (hn : 0 < n) (hC : 0 < C) (hC_le_n : C ≤ (n : ℝ))
    (hLp : ∀ i ∈ I, L = Real.log (p i : ℝ))
    (hQq : ∀ i ∈ I, Q = Real.log (q i : ℝ))
    (htn : t = Real.log (n : ℝ))
    (hgap : ∀ i ∈ I,
      0 ≤ t - ((a i : ℝ) * L + (b i : ℝ) * Q))
    (hgapC : ∀ i ∈ I,
      t - ((a i : ℝ) * L + (b i : ℝ) * Q) ≤ Real.log C)
    (hnontrivial : ∀ i ∈ I, 2 ≤ p i ^ a i * q i ^ b i)
    (hinj : Set.InjOn (fun i ↦ p i ^ a i * q i ^ b i) (I : Set ι))
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (p i ^ a i * q i ^ b i) (p j ^ a j * q j ^ b j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ p i ^ a i * q i ^ b i → s ∣ n) :
    (∑ i ∈ I, p i ^ a i * q i ^ b i) ≤ F n := by
  have hband : ∀ i ∈ I,
      (n : ℝ) / C ≤ ((p i ^ a i * q i ^ b i : ℕ) : ℝ) ∧
        ((p i ^ a i * q i ^ b i : ℕ) : ℝ) ≤ (n : ℝ) := by
    intro i hi
    exact power_product_mem_Icc_of_log_gap (hp i hi) (hq i hi) hn hC
      (hLp i hi) (hQq i hi) htn (hgap i hi) (hgapC i hi)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / C := by
    apply (le_div_iff₀ hC).2
    simpa using hC_le_n
  have hupper : ∀ i ∈ I, p i ^ a i * q i ^ b i ≤ n := by
    intro i hi
    exact_mod_cast (hband i hi).2
  exact sum_pairwise_terms_le_F I
    (fun i ↦ p i ^ a i * q i ^ b i)
    hinj hnontrivial hupper hcop hprime

theorem sum_matched_power_products_le_F
    {ι : Type*} [DecidableEq ι] {n : ℕ} (I : Finset ι)
    (p q a b : ι → ℕ)
    (hinj : Set.InjOn (fun i ↦ p i ^ a i * q i ^ b i) (I : Set ι))
    (hnontrivial : ∀ i ∈ I, 2 ≤ p i ^ a i * q i ^ b i)
    (hupper : ∀ i ∈ I, p i ^ a i * q i ^ b i ≤ n)
    (hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (p i ^ a i * q i ^ b i) (p j ^ a j * q j ^ b j))
    (hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ p i ^ a i * q i ^ b i → s ∣ n) :
    (∑ i ∈ I, p i ^ a i * q i ^ b i) ≤ F n := by
  exact sum_pairwise_terms_le_F I (fun i ↦ p i ^ a i * q i ^ b i)
    hinj hnontrivial hupper hcop hprime

/- A finite Hall interface for the Track-A pairing step.  Candidate partners are supplied as
   finite sets; the Hall cardinality condition then produces an injective choice, leaving the
   analytic bad-pair estimate entirely outside this combinatorial theorem. -/
theorem exists_injective_matching_of_hall
    {ι κ : Type*} [DecidableEq κ] (I : Finset ι) (cand : ι → Finset κ)
    (hall : ∀ A : Finset {i // i ∈ I},
      A.card ≤ (A.biUnion (fun i ↦ cand i.1)).card) :
    ∃ q : {i // i ∈ I} → κ, Function.Injective q ∧
      ∀ i, q i ∈ cand i.1 := by
  let t : {i // i ∈ I} → Finset κ := fun i ↦ cand i.1
  have hall' : ∀ A : Finset {i // i ∈ I}, A.card ≤ (A.biUnion t).card := by
    intro A
    exact hall A
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall'

/- A convenient sufficient condition for Hall: if every left vertex has at least `I.card`
   candidates, then every nonempty subfamily already has a neighborhood of size at least
   `I.card`.  This is intentionally stronger than necessary, but it is the form most directly
   produced by a uniform bad-degree estimate. -/
theorem hall_of_candidate_card_ge_index_card
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (cand : ι → Finset κ)
    (hcard : ∀ i : {i // i ∈ I}, I.card ≤ (cand i.1).card) :
    ∀ A : Finset {i // i ∈ I},
      A.card ≤ (A.biUnion (fun i ↦ cand i.1)).card := by
  intro A
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    have hsub : cand i.1 ⊆ A.biUnion (fun j ↦ cand j.1) := by
      intro k hk
      rw [Finset.mem_biUnion]
      exact ⟨i, hi, hk⟩
    have hneigh : I.card ≤ (A.biUnion (fun j ↦ cand j.1)).card :=
      (hcard i).trans (Finset.card_le_card hsub)
    have hAcard : A.card ≤ I.card := by
      calc
        A.card ≤ (Finset.univ : Finset {i // i ∈ I}).card :=
          Finset.card_le_card (Finset.subset_univ A)
        _ = I.card := by simp
    exact hAcard.trans hneigh
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [hAempty]

theorem exists_injective_matching_of_candidate_card_ge_index_card
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (cand : ι → Finset κ)
    (hcard : ∀ i : {i // i ∈ I}, I.card ≤ (cand i.1).card) :
    ∃ q : {i // i ∈ I} → κ, Function.Injective q ∧
      ∀ i, q i ∈ cand i.1 :=
  exists_injective_matching_of_hall I cand
    (hall_of_candidate_card_ge_index_card I cand hcard)

/- A weighted-to-cardinality conversion for bad candidate sets.  When every member of `D` is
   positive and at most `U`, each reciprocal weight is at least `1/U`; hence a reciprocal-weight
   upper bound controls the number of bad candidates. -/
theorem card_div_upper_le_reciprocal_sum
    (D : Finset ℕ) (U : ℕ) (hU : 0 < U)
    (hpos : ∀ q ∈ D, 0 < q)
    (hupper : ∀ q ∈ D, q ≤ U) :
    ((D.card : ℕ) : ℝ) / (U : ℝ) ≤
      ∑ q ∈ D, ((q : ℝ)⁻¹) := by
  have hUreal : 0 < (U : ℝ) := by exact_mod_cast hU
  calc
    ((D.card : ℕ) : ℝ) / (U : ℝ) =
        ∑ _q ∈ D, (1 : ℝ) / (U : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ q ∈ D, ((q : ℝ)⁻¹) := by
      gcongr with q hq
      have hqreal : 0 < (q : ℝ) := by exact_mod_cast hpos q hq
      have hqU : (q : ℝ) ≤ (U : ℝ) := by exact_mod_cast hupper q hq
      simpa [one_div] using (one_div_le_one_div_of_le hqreal hqU)

/- A convenient window-level form of the preceding estimate.  The hypotheses are stated on the
   ambient prime family `R`, so callers do not have to repeat the filter projections when the
   selected set is the subfamily of members dividing `n`. -/
theorem reciprocal_mass_filter_ge_card_div_upper
    (R : Finset ℕ) (U n : ℕ) (hU : 0 < U)
    (hprime : ∀ p ∈ R, p.Prime)
    (hupper : ∀ p ∈ R, p ≤ U) :
    ((R.filter (fun p ↦ p ∣ n)).card : ℝ) / (U : ℝ) ≤
      ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
  let D : Finset ℕ := R.filter (fun p ↦ p ∣ n)
  have hpos : ∀ p ∈ D, 0 < p := by
    intro p hp
    exact (hprime p (Finset.mem_filter.mp hp).1).pos
  have hupperD : ∀ p ∈ D, p ≤ U := by
    intro p hp
    exact hupper p (Finset.mem_filter.mp hp).1
  simpa [D] using card_div_upper_le_reciprocal_sum D U hU hpos hupperD

/- The complementary conversion for a dyadic block: if every element is at least `L`, then its
reciprocal mass times `L` is bounded by the block cardinality.  This is the finite bridge needed
to turn the divergent dyadic mass into a candidate-count budget for Hall. -/
theorem card_ge_lower_mul_reciprocal_sum
    (D : Finset ℕ) (L : ℕ)
    (hpos : ∀ q ∈ D, 0 < q)
    (hlower : ∀ q ∈ D, L ≤ q) :
    (L : ℝ) * (∑ q ∈ D, ((q : ℝ)⁻¹)) ≤ (D.card : ℝ) := by
  have hpoint : ∀ q ∈ D,
      (L : ℝ) * ((q : ℝ)⁻¹) ≤ (1 : ℝ) := by
    intro q hq
    have hqreal : 0 < (q : ℝ) := by exact_mod_cast hpos q hq
    have hLq : (L : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlower q hq
    have hdiv : (L : ℝ) / (q : ℝ) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hqreal).2
      simpa using hLq
    simpa [div_eq_mul_inv] using hdiv
  calc
    (L : ℝ) * (∑ q ∈ D, ((q : ℝ)⁻¹)) =
        ∑ q ∈ D, (L : ℝ) * ((q : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ D, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun q hq ↦ hpoint q hq)
    _ = (D.card : ℝ) := by simp

/- Specialization to one disjoint dyadic prime block.  Its endpoint arithmetic supplies the lower
bound automatically, so the block's divergent reciprocal mass can be consumed as a cardinality
budget without reopening any prime-counting argument. -/
theorem dyadicDisjointPrimeBlock_card_ge_lower_mul_mass (i : ℕ) :
    (dyadicDisjointLowerEndpoint i : ℝ) *
        (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (dyadicDisjointPrimeBlock i).card := by
  apply card_ge_lower_mul_reciprocal_sum
  · intro p hp
    exact ((Finset.mem_filter.mp hp).2).pos
  · intro p hp
    have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact le_trans (Nat.le_succ _) hpI.1

theorem dyadicDisjointPrimeTail_card_ge_lower_mul_mass (k m : ℕ) :
    (dyadicDisjointLowerEndpoint k : ℝ) *
        (∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹)) ≤
      (dyadicDisjointPrimeTail k m).card := by
  apply card_ge_lower_mul_reciprocal_sum
  · intro p hp
    unfold dyadicDisjointPrimeTail at hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
    exact ((Finset.mem_filter.mp hpi).2).pos
  · intro p hp
    unfold dyadicDisjointPrimeTail at hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
    have hpiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
    have hlow : dyadicDisjointLowerEndpoint k ≤
        dyadicDisjointLowerEndpoint (i + k) := by
      unfold dyadicDisjointLowerEndpoint
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    exact le_trans hlow (le_trans (Nat.le_succ _) hpiI.1)

/- If `D ⊆ Q` is the bad part of a finite candidate universe, the preceding estimate gives a
   lower bound for the good complement `Q \ D`.  This is the form consumed by the uniform-degree
   Hall wrapper above. -/
theorem card_sdiff_ge_of_reciprocal_weight_le
    (Q D : Finset ℕ) (U : ℕ) {W : ℝ}
    (hDsub : D ⊆ Q) (hU : 0 < U)
    (hpos : ∀ q ∈ D, 0 < q)
    (hupper : ∀ q ∈ D, q ≤ U)
    (hweight : (∑ q ∈ D, ((q : ℝ)⁻¹)) ≤ W) :
    ((Q.card : ℕ) : ℝ) - (U : ℝ) * W ≤ ((Q \ D).card : ℝ) := by
  have hcard := Finset.card_sdiff_add_card_inter Q D
  rw [Finset.inter_eq_right.mpr hDsub] at hcard
  have hcardR : ((Q \ D).card : ℝ) + (D.card : ℝ) = (Q.card : ℝ) := by
    exact_mod_cast hcard
  have hmass := card_div_upper_le_reciprocal_sum D U hU hpos hupper
  have hmassW : ((D.card : ℕ) : ℝ) ≤ (U : ℝ) * W := by
    have hUreal : 0 ≤ (U : ℝ) := by positivity
    have hmul : ((D.card : ℕ) : ℝ) ≤
        (∑ q ∈ D, ((q : ℝ)⁻¹)) * (U : ℝ) :=
      (div_le_iff₀ (by exact_mod_cast hU : 0 < (U : ℝ))).mp hmass
    calc
      ((D.card : ℕ) : ℝ) ≤ (U : ℝ) * (∑ q ∈ D, ((q : ℝ)⁻¹)) := by
        simpa [mul_comm] using hmul
      _ ≤ (U : ℝ) * W := mul_le_mul_of_nonneg_left hweight hUreal
  linarith

/- Application of the weighted complement bound to the concrete bad-q window.  The only
   additional side condition is that the outer prime window has a positive upper endpoint; all
   primality, positivity, and upper-bound facts are read from the window definition. -/
theorem card_good_qWindow_ge_of_local_weight
    {T α β γ δ rho : ℝ} {M r h p : ℕ} {W : ℝ}
    (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    (hweight :
      (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) ≤ W) :
    ((primeWindow T γ δ).card : ℝ) -
        (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W ≤
      ((primeWindow T γ δ \ badPairQWindow T α β γ δ rho M r h p).card : ℝ) := by
  let Q := primeWindow T γ δ
  let D := badPairQWindow T α β γ δ rho M r h p
  let U := Nat.floor (Real.exp (Real.rpow T δ))
  have hDsub : D ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hpos : ∀ q ∈ D, 0 < q := by
    intro q hq
    have hQ := Finset.mem_filter.mp (hDsub hq)
    have hprime : q.Prime := hQ.2.1
    exact hprime.pos
  have hupper : ∀ q ∈ D, q ≤ U := by
    intro q hq
    have hQ := Finset.mem_filter.mp (hDsub hq)
    exact (Finset.mem_Icc.mp hQ.1).2
  have h := card_sdiff_ge_of_reciprocal_weight_le Q D U hDsub hU hpos hupper
    (by simpa [D] using hweight)
  simpa [Q, D, U] using h

/- Local q-window weights now feed Hall directly.  If the selected p-family is small enough
   compared with the q-window after the uniform bad-weight loss `U*W`, every p gets at least
   `I.card` good q-candidates, and a reuse-free q matching follows. -/
theorem exists_q_matching_of_qWindow_weights
    {T α β γ δ rho : ℝ} (I : Finset ℕ)
    {M r h : ℕ} (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) ≤ W) :
    ∃ q : {p // p ∈ I} → ℕ, Function.Injective q ∧
      ∀ p, q p ∈ primeWindow T γ δ \
        badPairQWindow T α β γ δ rho M r h p.1 := by
  let Q := primeWindow T γ δ
  let cand : ℕ → Finset ℕ := fun p ↦
    Q \ badPairQWindow T α β γ δ rho M r h p
  have hcard_cand : ∀ p : {p // p ∈ I}, I.card ≤ (cand p.1).card := by
    intro p
    have hgood := card_good_qWindow_ge_of_local_weight (T := T) (α := α) (β := β)
      (γ := γ) (δ := δ) (rho := rho) (M := M) (r := r) (h := h) (p := p.1)
      hU (hweight p.1 p.property)
    have hreal : (I.card : ℝ) ≤ (cand p.1).card := by
      have hQ := hcard p.1 p.property
      linarith
    exact_mod_cast hreal
  obtain ⟨q, hqinj, hqmem⟩ :=
    exists_injective_matching_of_candidate_card_ge_index_card I cand hcard_cand
  refine ⟨q, hqinj, ?_⟩
  intro p
  exact hqmem p

/- Variable-parameter Hall version.  In the report construction the approximating denominator
   and numerator can depend on the selected first prime, so the fixed `(r,h)` interface above is
   not sufficient.  This theorem keeps that dependence explicit while retaining the same local
   reciprocal-weight certificate. -/
theorem exists_q_matching_of_variable_qWindow_weights
    {T α β γ δ rho : ℝ} (I : Finset ℕ)
    {M : ℕ} (rfun hfun : ℕ → ℕ)
    (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℕ → ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W p ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M (rfun p) (hfun p) p, ((q : ℝ)⁻¹)) ≤ W p) :
    ∃ q : {p // p ∈ I} → ℕ, Function.Injective q ∧
      ∀ p, q p ∈ primeWindow T γ δ \
        badPairQWindow T α β γ δ rho M (rfun p.1) (hfun p.1) p.1 := by
  let Q : Finset ℕ := primeWindow T γ δ
  let cand : ℕ → Finset ℕ := fun p ↦
    Q \ badPairQWindow T α β γ δ rho M (rfun p) (hfun p) p
  have hcard_cand : ∀ p : {p // p ∈ I}, I.card ≤ (cand p.1).card := by
    intro p
    have hgood := card_good_qWindow_ge_of_local_weight
      (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
      (M := M) (r := rfun p.1) (h := hfun p.1) (p := p.1)
      hU (hweight p.1 p.property)
    have hreal : (I.card : ℝ) ≤ (cand p.1).card := by
      have hQ := hcard p.1 p.property
      linarith
    exact_mod_cast hreal
  obtain ⟨q, hqinj, hqmem⟩ :=
    exists_injective_matching_of_candidate_card_ge_index_card I cand hcard_cand
  refine ⟨q, hqinj, ?_⟩
  intro p
  exact hqmem p

/- Ordered-window output form of the variable Hall theorem.  This is a small but useful
   competition-style adapter: once the first window is no later than the second, the selected
   partner is automatically prime and cannot coincide with any first-window prime.  Downstream
   product constructions can therefore consume the matching without reproving the logarithmic
   separation for every use. -/
theorem exists_q_matching_of_variable_qWindow_weights_of_ordered_windows
    {T α β γ δ rho : ℝ} (I : Finset ℕ)
    {M : ℕ} (rfun hfun : ℕ → ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ)
    (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℕ → ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W p ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M (rfun p) (hfun p) p, ((q : ℝ)⁻¹)) ≤ W p)
    (hpwindow : ∀ p ∈ I, p ∈ primeWindow T α β) :
    ∃ q : {p // p ∈ I} → ℕ,
      Function.Injective q ∧
      (∀ p, q p ∈ primeWindow T γ δ \
        badPairQWindow T α β γ δ rho M (rfun p.1) (hfun p.1) p.1) ∧
      (∀ p, (q p).Prime) ∧
      (∀ p, p.1 ≠ q p) := by
  obtain ⟨q, hqinj, hqmem⟩ := exists_q_matching_of_variable_qWindow_weights
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    I rfun hfun hU hcard hweight
  have hqprime : ∀ p, (q p).Prime := by
    intro p
    have hqQ : q p ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem p)).1
    exact (Finset.mem_filter.mp hqQ).2.1
  have hneq : ∀ p, p.1 ≠ q p := by
    intro p
    have hpw : p.1 ∈ primeWindow T α β := hpwindow p.1 p.property
    have hqQ : q p ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem p)).1
    have hpPrime : Nat.Prime p.1 := (Finset.mem_filter.mp hpw).2.1
    have hplogPos : 0 < Real.log (p.1 : ℝ) :=
      Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hratio : 1 < Real.log (q p : ℝ) / Real.log (p.1 : ℝ) :=
      primeWindow_log_ratio_gt_one hpw hqQ hT hβγ
    have hloglt : Real.log (p.1 : ℝ) < Real.log (q p : ℝ) := by
      have h := (lt_div_iff₀ hplogPos).mp hratio
      simpa using h
    intro heq
    rw [← heq] at hloglt
    exact (lt_irrefl _ hloglt)
  exact ⟨q, hqinj, hqmem, hqprime, hneq⟩

/- Finite weighted Markov inequality.  If `u` is a nonnegative vertex weight and `v` is a
   nonnegative bad-degree function, then the total `u`-mass of vertices with bad degree at least
   `θ` is at most `W/θ` whenever the weighted degree sum is at most `W`. -/
theorem weighted_filter_le_of_sum_mul_le
    {α : Type*} [DecidableEq α] (U : Finset α) (u v : α → ℝ)
    {θ W : ℝ} (_hθ : 0 ≤ θ)
    (hu : ∀ x ∈ U, 0 ≤ u x)
    (hv : ∀ x ∈ U, 0 ≤ v x)
    (hsum : ∑ x ∈ U, u x * v x ≤ W) :
    θ * (∑ x ∈ U.filter (fun x ↦ θ ≤ v x), u x) ≤ W := by
  let D : Finset α := U.filter (fun x ↦ θ ≤ v x)
  have hDsub : D ⊆ U := Finset.filter_subset _ _
  have hpoint : ∀ x ∈ D, θ * u x ≤ u x * v x := by
    intro x hx
    have hxθ : θ ≤ v x := (Finset.mem_filter.mp hx).2
    have hxU : x ∈ U := hDsub hx
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hxθ (hu x hxU))
  calc
    θ * (∑ x ∈ D, u x) = ∑ x ∈ D, θ * u x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ D, u x * v x := by
      exact Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
    _ ≤ ∑ x ∈ U, u x * v x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hDsub
        (by intro x hxU hxD; exact mul_nonneg (hu x hxU) (hv x hxU))
    _ ≤ W := hsum

theorem weighted_filter_le_div_of_sum_mul_le
    {α : Type*} [DecidableEq α] (U : Finset α) (u v : α → ℝ)
    {θ W : ℝ} (hθ : 0 < θ)
    (hu : ∀ x ∈ U, 0 ≤ u x)
    (hv : ∀ x ∈ U, 0 ≤ v x)
    (hsum : ∑ x ∈ U, u x * v x ≤ W) :
    (∑ x ∈ U.filter (fun x ↦ θ ≤ v x), u x) ≤ W / θ := by
  apply (le_div_iff₀ hθ).2
  simpa [mul_comm] using
    weighted_filter_le_of_sum_mul_le U u v hθ.le hu hv hsum

/- The local reciprocal mass of the concrete q-window attached to one first prime.  Keeping this
quantity named makes the next Markov estimate readable and lets later analytic bounds refer to the
same finite object without unfolding the window definition repeatedly. -/
noncomputable def badPairQReciprocalWeight
    (T α β γ δ rho : ℝ) (M r h p : ℕ) : ℝ :=
  ∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)

theorem badPairQReciprocalWeight_nonneg
    (T α β γ δ rho : ℝ) (M r h p : ℕ) :
    0 ≤ badPairQReciprocalWeight T α β γ δ rho M r h p := by
  unfold badPairQReciprocalWeight
  positivity

/- The local quantity is bounded by the explicit Brun--Titchmarsh majorant from `PrimeMass`.
This is now imported through the minimal Formal Conjectures interface, avoiding the former
SelbergSieve umbrella collision. -/
theorem badPairQReciprocalWeight_le_brunBound
    {T α β γ δ rho : ℝ} {M r h p : ℕ}
    (hp : p ∈ primeWindow T α β) (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    badPairQReciprocalWeight T α β γ δ rho M r h p ≤
      badPairQWindowBrunBound M r h p := by
  unfold badPairQReciprocalWeight
  have hw := badPairQWindow_hypotheses_of_prime_window hp hM hr hh
  exact badPairQWindow_reciprocal_le_explicit T α β γ δ rho M r h p hw.1 hw.2

theorem localWeight_sum_le_brunBound_sum
    {T α β γ δ rho : ℝ} {M r h : ℕ}
    (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    (∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left
  · exact badPairQReciprocalWeight_le_brunBound hp hM hr hh
  · positivity

/- The explicit main-plus-decay estimate can be stated directly for the named local-weight sum.
This avoids passing through `pairReciprocalWeight` when the next Markov step only needs the
p-slice majorant. -/
theorem localWeight_sum_le_main_plus_decay_sum
    {T α β γ δ rho : ℝ} {M r h : ℕ}
    (hM4 : 4 ≤ M) (hr : 0 < r) (hh : 0 < h)
    (hwidth : ∀ p ∈ primeWindow T α β,
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    (∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (16 / ((h : ℝ) * (M : ℝ)) +
            6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
              (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3) := by
  have hbase := localWeight_sum_le_brunBound_sum
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (M := M) (r := r) (h := h) (by omega) hr hh
  calc
    (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := hbase
    _ ≤ ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (16 / ((h : ℝ) * (M : ℝ)) +
            6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
              (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · exact badPairQWindowBrunBound_le_main_plus_decay_of_width hM4 hr hh
          (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp)
      · positivity

theorem pairReciprocalWeight_qWindows_le_localWeight
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    pairReciprocalWeight (badPairBlockQWindows T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p := by
  simpa [badPairQReciprocalWeight] using
    (pairReciprocalWeight_qWindows_le T α β γ δ rho M r h)

theorem badPairBlockWeight_le_localWeight_sum
    (T α β γ δ rho : ℝ) (M r h : ℕ) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p := by
  exact (badPairBlockWeight_le_qWindows T α β γ δ rho M r h).trans
    (pairReciprocalWeight_qWindows_le_localWeight T α β γ δ rho M r h)

/- The p-sliced block admits the sharper local bound needed when the finite cover is summed with
the p-dependent denominator range. -/
theorem badPairBlockAtPrimeWeight_le_localWeight
    (T α β γ δ rho : ℝ) (M p r h : ℕ)
    (_hp : p ∈ primeWindow T α β) :
    pairReciprocalWeight (badPairBlockAtPrime T α β γ δ rho M p r h) ≤
      ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p := by
  have hsubset := badPairBlockAtPrime_subset_qWindow_image
    T α β γ δ rho M p r h
  calc
    pairReciprocalWeight (badPairBlockAtPrime T α β γ δ rho M p r h) ≤
        pairReciprocalWeight
          ((badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q))) :=
      pairReciprocalWeight_mono hsubset
    _ = ((p : ℝ)⁻¹) *
          (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) :=
      pairReciprocalWeight_image_fixed_left p
        (badPairQWindow T α β γ δ rho M r h p)
    _ = ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p := by
      rfl

/- Finite weighted Markov on the actual p-slices.  Thus any estimate on the displayed weighted
sum immediately removes the p's whose local bad-q reciprocal weight exceeds `θ`, with loss `W/θ`.
No prime-distribution or asymptotic input is hidden in this theorem. -/
theorem reciprocalMass_high_badPairQWeight_le
    {T α β γ δ rho : ℝ} {M r h : ℕ} {θ W : ℝ}
    (hθ : 0 < θ)
    (hsum :
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQReciprocalWeight T α β γ δ rho M r h p ≤ W) :
    (∑ p ∈ (primeWindow T α β).filter
        (fun p ↦ θ ≤ badPairQReciprocalWeight T α β γ δ rho M r h p),
      ((p : ℝ)⁻¹)) ≤ W / θ := by
  let U := primeWindow T α β
  let u : ℕ → ℝ := fun p ↦ ((p : ℝ)⁻¹)
  let v : ℕ → ℝ := fun p ↦ badPairQReciprocalWeight T α β γ δ rho M r h p
  have hu : ∀ p ∈ U, 0 ≤ u p := by
    intro p hp
    dsimp [u]
    positivity
  have hv : ∀ p ∈ U, 0 ≤ v p := by
    intro p hp
    dsimp [v]
    exact badPairQReciprocalWeight_nonneg T α β γ δ rho M r h p
  have hsum' : ∑ p ∈ U, u p * v p ≤ W := by
    simpa [U, u, v] using hsum
  have hmark := weighted_filter_le_div_of_sum_mul_le U u v hθ hu hv hsum'
  simpa [U, u, v] using hmark

theorem reciprocalMass_high_badPairQWeight_le_brunBound
    {T α β γ δ rho : ℝ} {M r h : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    (∑ p ∈ (primeWindow T α β).filter
        (fun p ↦ θ ≤ badPairQReciprocalWeight T α β γ δ rho M r h p),
      ((p : ℝ)⁻¹)) ≤
      (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) / θ := by
  apply reciprocalMass_high_badPairQWeight_le hθ
  exact localWeight_sum_le_brunBound_sum hM hr hh

theorem reciprocalMass_high_badPairQWeight_le_main_plus_decay
    {T α β γ δ rho : ℝ} {M r h : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (hM4 : 4 ≤ M) (hr : 0 < r) (hh : 0 < h)
    (hwidth : ∀ p ∈ primeWindow T α β,
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    (∑ p ∈ (primeWindow T α β).filter
        (fun p ↦ θ ≤ badPairQReciprocalWeight T α β γ δ rho M r h p),
      ((p : ℝ)⁻¹)) ≤
      (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (16 / ((h : ℝ) * (M : ℝ)) +
            6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
              (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3)) / θ := by
  apply reciprocalMass_high_badPairQWeight_le hθ
  exact localWeight_sum_le_main_plus_decay_sum hM4 hr hh hwidth

/- A generic finite total of local q-window weights.  The positive `r` and `h` conjuncts remove
the degenerate denominator/numerator blocks before applying the q-window estimate; the final
conjunct is the same lower-h cutoff used by the Brun decay majorant. -/
noncomputable def localQWeightSum
    (T α β γ δ rho : ℝ) (M H : ℕ) : ℝ :=
  ∑ p ∈ primeWindow T α β,
    ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if 0 < r ∧ 0 < h ∧
            primeWindowHLower T β γ M r ≤ h then
          ((p : ℝ)⁻¹) *
            badPairQReciprocalWeight T α β γ δ rho M r h p
        else 0

/- The concrete finite cover can now be transported all the way to the named local q-weight
total.  The lower h-cutoff removes empty blocks, while r=0 and h=0 are handled explicitly. -/
theorem badPairWeight_le_localQWeightSum_of_report_bounds
    {T α β γ δ rho : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      localQWeightSum T α β γ δ rho M
        (reportHBound T α β δ rho M) := by
  have hcover := badPairs_cover_primeDependent_report_bounds
    T α β γ δ rho M hT hβγ hrho hM hL hpositive
  have hbase := badPairWeight_le_primeDependent_block_sum
    T α β γ δ rho M (fun p ↦ denominatorCutoff p rho)
      (reportHBound T α β δ rho M) hcover
      (by intro p hp; exact le_rfl)
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
              pairReciprocalWeight
                (badPairBlockAtPrime T α β γ δ rho M p r h) := hbase
    _ ≤ localQWeightSum T α β γ δ rho M
        (reportHBound T α β δ rho M) := by
      unfold localQWeightSum
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro h hh
      by_cases hlow : primeWindowHLower T β γ M r ≤ h
      · by_cases hr0 : r = 0
        · subst r
          simp [badPairBlockAtPrime, badPairBlock_zero_r_empty,
            pairReciprocalWeight]
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          by_cases hh0 : h = 0
          · subst h
            have hempty := badPairBlock_h_zero_empty_of_ordered_windows
              T α β γ δ rho M r hT hβγ hM hrpos
            simp [badPairBlockAtPrime, hempty, pairReciprocalWeight]
          · have hhpos : 0 < h := Nat.pos_of_ne_zero hh0
            have hlocal := badPairBlockAtPrimeWeight_le_localWeight
              T α β γ δ rho M p r h hp
            simpa [hrpos, hhpos, hlow] using hlocal
      · have hempty := badPairBlock_empty_below_primeWindowHLower
          (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
          (M := M) (r := r) (h := h) hT (Nat.zero_lt_of_lt hM)
            (Nat.lt_of_not_ge hlow)
        simp [badPairBlockAtPrime, hempty, pairReciprocalWeight, hlow]

noncomputable def reportLocalQWeightSum
    (T α β γ δ rho : ℝ) : ℝ :=
  localQWeightSum T α β γ δ rho
    (reportApproximationScale T δ)
    (reportHBound T α β δ rho (reportApproximationScale T δ))

/- Eventual report-scale form of the preceding cover.  This is the explicit bridge from the
actual bad-pair family to the local q-weight total used by the Markov/Hall strategy. -/
theorem eventually_badPairWeight_le_reportLocalQWeightSum
    {α β γ δ rho : ℝ}
    (_hα : 0 < α) (hβγ : β ≤ γ) (hδ1 : δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      pairReciprocalWeight (badPairsAtReportScale T α β γ δ rho) ≤
        reportLocalQWeightSum T α β γ δ rho := by
  have hT1 : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hMgt : ∀ᶠ T : ℝ in atTop,
      1 < reportApproximationScale T δ :=
    eventually_reportApproximationScale_gt_one hδ1
  filter_upwards [hT1, hTpos, hMgt] with T hT hTposT hMgtT
  have hL : 0 < Real.rpow T α := Real.rpow_pos_of_pos hTposT _
  have hpositive : 0 < Real.rpow T δ / Real.rpow T α :=
    report_endpoint_ratio_pos hTposT
  have hbound := badPairWeight_le_localQWeightSum_of_report_bounds
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (M := reportApproximationScale T δ)
    hT hβγ hrho hMgtT hL hpositive
  simpa [badPairsAtReportScale, badPairsWithScale, reportLocalQWeightSum] using hbound

theorem badPairQWindowBrunDecayError_nonneg
    (M r h p : ℕ) : 0 ≤ badPairQWindowBrunDecayError M r h p := by
  unfold badPairQWindowBrunDecayError
  split <;> positivity

/- Finite decomposition of the local q-weight total.  This is the exact pointwise split of the
Brun majorant into its reciprocal-width main term and exponential decay error; no asymptotic
input is used here. -/
theorem localQWeightSum_le_mainsum_add_errorsum
    {T α β γ δ rho : ℝ} {M H : ℕ}
    (hM4 : 4 ≤ M)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    localQWeightSum T α β γ δ rho M H ≤
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
            else 0) +
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
            else 0) := by
  let good : ℕ → ℕ → ℕ → Prop := fun p r h ↦
    0 < r ∧ 0 < h ∧ primeWindowHLower T β γ M r ≤ h
  let main : ℕ → ℕ → ℕ → ℝ := fun p r h ↦
    ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
  let err : ℕ → ℕ → ℕ → ℝ := fun p r h ↦
    ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
  have hpoint : ∀ p ∈ primeWindow T α β, ∀ r ∈ Finset.range (denominatorCutoff p rho),
      ∀ h ∈ Finset.range H,
      (if good p r h then ((p : ℝ)⁻¹) *
          badPairQReciprocalWeight T α β γ δ rho M r h p else 0) ≤
        (if primeWindowHLower T β γ M r ≤ h then main p r h else 0) +
          (if primeWindowHLower T β γ M r ≤ h then err p r h else 0) := by
    intro p hp r hrange h hhrange
    by_cases hg : good p r h
    · have hrpos : 0 < r := hg.1
      have hhpos : 0 < h := hg.2.1
      have hlow : primeWindowHLower T β γ M r ≤ h := hg.2.2
      have hlocal := badPairQReciprocalWeight_le_brunBound
        (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
        (M := M) (r := r) (h := h) (p := p) hp (by omega) hrpos hhpos
      have hbrun := badPairQWindowBrunBound_le_main_plus_decay_of_width
        (M := M) (r := r) (h := h) (p := p) hM4 hrpos hhpos
        (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp r hrpos)
      have hbrun' : badPairQWindowBrunBound M r h p ≤
          16 / ((h : ℝ) * (M : ℝ)) +
            badPairQWindowBrunDecayError M r h p := by
        simpa [badPairQWindowBrunDecayError, Nat.ne_of_gt hrpos,
          Nat.ne_of_gt hhpos] using hbrun
      have hmul : ((p : ℝ)⁻¹) * badPairQReciprocalWeight
          T α β γ δ rho M r h p ≤
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)) +
            badPairQWindowBrunDecayError M r h p) := by
        exact mul_le_mul_of_nonneg_left (hlocal.trans hbrun') (by positivity)
      simpa [good, main, err, hg, hlow, badPairQWindowBrunDecayError,
        Nat.ne_of_gt hrpos, Nat.ne_of_gt hhpos, mul_add] using hmul
    · by_cases hlow : primeWindowHLower T β γ M r ≤ h
      · have hmain0 : 0 ≤ main p r h := by
          dsimp [main]
          exact mul_nonneg (by positivity) (by positivity)
        have herr0 : 0 ≤ err p r h := by
          dsimp [err]
          exact mul_nonneg (by positivity)
            (badPairQWindowBrunDecayError_nonneg M r h p)
        simpa [good, main, err, hg, hlow] using add_nonneg hmain0 herr0
      · simp [good, main, err, hg, hlow]
  have hsum_point : localQWeightSum T α β γ δ rho M H ≤
      ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              ((if primeWindowHLower T β γ M r ≤ h then main p r h else 0) +
              (if primeWindowHLower T β γ M r ≤ h then err p r h else 0)) := by
    unfold localQWeightSum
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro h hh
    simpa [good] using hpoint p hp r hr h hh
  calc
    localQWeightSum T α β γ δ rho M H ≤
        ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              ((if primeWindowHLower T β γ M r ≤ h then main p r h else 0) +
                (if primeWindowHLower T β γ M r ≤ h then err p r h else 0)) := hsum_point
    _ =
        (∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              if primeWindowHLower T β γ M r ≤ h then main p r h else 0) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range H,
                if primeWindowHLower T β γ M r ≤ h then err p r h else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤
        (∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              if primeWindowHLower T β γ M r ≤ h then main p r h else 0) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range H,
                if primeWindowHLower T β γ M r ≤ h then err p r h else 0) := by
      exact add_le_add (le_rfl) (le_rfl)
    _ =
        (∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              if primeWindowHLower T β γ M r ≤ h then
                ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
              else 0) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range H,
                if primeWindowHLower T β γ M r ≤ h then
                  ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
                else 0) := by
      rfl

/- Report-scale wrapper for the preceding finite split.  The only hypotheses used here are the
eventual width and power conditions already proved in `PrimeMass`; the Mertens estimate itself is
not silently introduced. -/
theorem eventually_reportLocalQWeightSum_le_main_plus_weighted_cube
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      reportLocalQWeightSum T α β γ δ rho ≤
        reportMainTerm T α β δ rho +
          reportWeightedCubeError T α β γ δ rho := by
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hT1 : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hM4 : ∀ᶠ T : ℝ in atTop,
      4 ≤ (reportApproximationScale T δ : ℝ) :=
    eventually_reportApproximationScale_ge_four hδ1
  have hwidth : ∀ᶠ T : ℝ in atTop,
      ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
        2 * Real.log (p : ℝ) ≤ (r : ℝ) *
          (reportApproximationScale T δ : ℝ) :=
    eventually_primeWindow_width_of_reportApproximationScale hβ.le hβδ
  have hpower := eventually_report_decay_exponent_ge_one hα hβγ
  filter_upwards [hTpos, hT1, hM4, hwidth, hpower] with T hT hT1T hM4T hwidthT hpowerT
  let M : ℕ := reportApproximationScale T δ
  let H : ℕ := reportHBound T α β δ rho (reportApproximationScale T δ)
  have hM4nat : 4 ≤ M := by
    dsimp [M]
    exact_mod_cast hM4T
  have hMpos : 0 < M := by omega
  have hfinite := localQWeightSum_le_mainsum_add_errorsum
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (M := M) (H := H) hM4nat (by
      intro p hp r hr
      simpa [M] using hwidthT p hp r hr)
  have hmain_filter :
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
            else 0) ≤
      ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ))) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro h hh
    by_cases hl : primeWindowHLower T β γ M r ≤ h
    · simp [hl]
    · simp [hl]
      positivity
  have hmain_range := pDependent_main_range_le_Icc
    (s := primeWindow T α β) rho M H
  have hmain := pDependent_main_term_le_mertens
    (T := T) (a := α) (b := β) (rho := rho) M H hT hrho hMpos
  have herr := pDependent_decay_error_sum_le_weighted_cube
    (s := primeWindow T α β) (T := T) (α := α) (β := β) (γ := γ)
    (rho := rho) (M := M) (H := H)
    (by intro p hp; exact hp) hT1T hMpos hpowerT (by
      intro p hp r hr
      simpa [M] using hwidthT p hp r hr)
  have hmain_total := hmain_filter.trans (hmain_range.trans hmain)
  calc
    reportLocalQWeightSum T α β γ δ rho ≤
        (∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              if primeWindowHLower T β γ M r ≤ h then
                ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
              else 0) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range H,
                if primeWindowHLower T β γ M r ≤ h then
                  ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
                else 0) := by
      simpa [reportLocalQWeightSum, M, H] using hfinite
    _ ≤
        (∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range H,
              ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range H,
                if primeWindowHLower T β γ M r ≤ h then
                  ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
                else 0) := by
      exact add_le_add hmain_filter (le_rfl)
    _ ≤
        (16 / (M : ℝ)) *
            ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) +
              PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
            (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) +
          (∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
            (H : ℝ) *
            (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
              (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3) := by
      exact add_le_add (hmain_range.trans hmain) herr
    _ = reportMainTerm T α β δ rho + reportWeightedCubeError T α β γ δ rho := by
      rfl

/- The complete finite-to-analytic upper-bound chain, routed through the named local q sum.
This is equivalent in strength to the existing direct majorant theorem, but records explicitly
where the local-weight/Markov/Hall interface enters. -/
theorem eventually_badPairWeight_le_main_plus_weighted_cube_via_localQ
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      pairReciprocalWeight (badPairsAtReportScale T α β γ δ rho) ≤
        reportMainTerm T α β δ rho +
          reportWeightedCubeError T α β γ δ rho := by
  have hcover := eventually_badPairWeight_le_reportLocalQWeightSum
    (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    hα hβγ hδ1 hrho
  have hmajor := eventually_reportLocalQWeightSum_le_main_plus_weighted_cube
    (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    hα hβ hβγ hδ0 hδ1 hβδ hrho
  filter_upwards [hcover, hmajor] with T hT hT'
  exact hT.trans hT'

/- The Hall choice becomes an actual admissible two-prime family once the two marginal prime
   maps are injective and the windows are disjoint.  This theorem is the finite bridge used by
   Track A: all analytic information is confined to the displayed prime/divisibility and size
   hypotheses, while distinctness, coprimality, and the prime-support condition are discharged
   internally. -/
theorem card_mul_le_F_of_injective_prime_pairing
    {ι : Type*} [DecidableEq ι] {n B : ℕ} (I : Finset ι)
    (p q : ι → ℕ)
    (hpprime : ∀ i ∈ I, (p i).Prime)
    (hqprime : ∀ i ∈ I, (q i).Prime)
    (hpdiv : ∀ i ∈ I, p i ∣ n)
    (hqdiv : ∀ i ∈ I, q i ∣ n)
    (hpinj : Set.InjOn p (I : Set ι))
    (hqinj : Set.InjOn q (I : Set ι))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, p i ≠ q j)
    (hlower : ∀ i ∈ I, B ≤ p i * q i)
    (hupper : ∀ i ∈ I, p i * q i ≤ n) :
    I.card * B ≤ F n := by
  let term : ι → ℕ := fun i ↦ p i * q i
  have hinj : Set.InjOn term (I : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    have hpi : (p i).Prime := hpprime i hi
    have hpdivterm : p i ∣ term i := by
      exact dvd_mul_of_dvd_left (dvd_refl _) _
    have hpdivprod : p i ∣ p j * q j := by
      change p i * q i = p j * q j at heq
      rw [← heq]
      exact hpdivterm
    rcases hpi.dvd_mul.mp hpdivprod with hpj | hqj
    · have hpeq : p i = p j :=
        (Nat.prime_dvd_prime_iff_eq hpi (hpprime j hj)).mp hpj
      exact hij (hpinj hi hj hpeq)
    · exact (hcross i hi j hj) ((Nat.prime_dvd_prime_iff_eq hpi (hqprime j hj)).mp hqj)
  have hpositive : ∀ i ∈ I, 2 ≤ term i := by
    intro i hi
    calc
      2 ≤ 2 * 2 := by norm_num
      _ ≤ p i * q i := Nat.mul_le_mul (hpprime i hi).two_le (hqprime i hi).two_le
  have hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (term i) (term j) := by
    intro i hi j hj hij
    have hpp : Nat.Coprime (p i) (p j) := by
      exact (Nat.coprime_primes (hpprime i hi) (hpprime j hj)).2
        (fun heq => hij (hpinj hi hj heq))
    have hqq : Nat.Coprime (q i) (q j) := by
      exact (Nat.coprime_primes (hqprime i hi) (hqprime j hj)).2
        (fun heq => hij (hqinj hi hj heq))
    have hpq : Nat.Coprime (p i) (q j) := by
      exact (Nat.coprime_primes (hpprime i hi) (hqprime j hj)).2 (hcross i hi j hj)
    have hqp : Nat.Coprime (q i) (p j) := by
      exact (Nat.coprime_primes (hqprime i hi) (hpprime j hj)).2
        (fun heq => hcross j hj i hi heq.symm)
    apply (Nat.coprime_mul_iff_right).2
    constructor
    · exact (Nat.coprime_mul_iff_left).2 ⟨hpp, hqp⟩
    · exact (Nat.coprime_mul_iff_left).2 ⟨hpq, hqq⟩
  have hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ term i → s ∣ n := by
    intro i hi s hs hst
    rcases hs.dvd_mul.mp hst with hsp | hsq
    · have hsi : s = p i :=
        (Nat.prime_dvd_prime_iff_eq hs (hpprime i hi)).mp hsp
      simpa [hsi] using hpdiv i hi
    · have hsi : s = q i :=
        (Nat.prime_dvd_prime_iff_eq hs (hqprime i hi)).mp hsq
      simpa [hsi] using hqdiv i hi
  exact card_mul_le_F_of_pairwise_terms I term hinj hpositive hlower hupper hcop hprime

/- Sum-valued companion of the cardinality bridge above.  This is the form needed when the
   analytic argument controls the actual products p_i*q_i rather than a common lower endpoint B. -/
theorem sum_le_F_of_injective_prime_pairing
    {ι : Type*} [DecidableEq ι] {n : ℕ} (I : Finset ι)
    (p q : ι → ℕ)
    (hpprime : ∀ i ∈ I, (p i).Prime)
    (hqprime : ∀ i ∈ I, (q i).Prime)
    (hpdiv : ∀ i ∈ I, p i ∣ n)
    (hqdiv : ∀ i ∈ I, q i ∣ n)
    (hpinj : Set.InjOn p (I : Set ι))
    (hqinj : Set.InjOn q (I : Set ι))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, p i ≠ q j)
    (hupper : ∀ i ∈ I, p i * q i ≤ n) :
    (∑ i ∈ I, p i * q i) ≤ F n := by
  let term : ι → ℕ := fun i ↦ p i * q i
  have hterm_inj : Set.InjOn term (I : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    have hpi : (p i).Prime := hpprime i hi
    have hpdivterm : p i ∣ term i := by
      exact dvd_mul_of_dvd_left (dvd_refl _) _
    have hpdivprod : p i ∣ p j * q j := by
      change p i * q i = p j * q j at heq
      rw [← heq]
      exact hpdivterm
    rcases hpi.dvd_mul.mp hpdivprod with hpj | hqj
    · have hpeq : p i = p j :=
        (Nat.prime_dvd_prime_iff_eq hpi (hpprime j hj)).mp hpj
      exact hij (hpinj hi hj hpeq)
    · exact (hcross i hi j hj) ((Nat.prime_dvd_prime_iff_eq hpi (hqprime j hj)).mp hqj)
  have hpositive : ∀ i ∈ I, 2 ≤ term i := by
    intro i hi
    calc
      2 ≤ 2 * 2 := by norm_num
      _ ≤ p i * q i := Nat.mul_le_mul (hpprime i hi).two_le (hqprime i hi).two_le
  have hcop : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
      Nat.Coprime (term i) (term j) := by
    intro i hi j hj hij
    have hpp : Nat.Coprime (p i) (p j) := by
      exact (Nat.coprime_primes (hpprime i hi) (hpprime j hj)).2
        (fun heq => hij (hpinj hi hj heq))
    have hqq : Nat.Coprime (q i) (q j) := by
      exact (Nat.coprime_primes (hqprime i hi) (hqprime j hj)).2
        (fun heq => hij (hqinj hi hj heq))
    have hpq : Nat.Coprime (p i) (q j) := by
      exact (Nat.coprime_primes (hpprime i hi) (hqprime j hj)).2 (hcross i hi j hj)
    have hqp : Nat.Coprime (q i) (p j) := by
      exact (Nat.coprime_primes (hqprime i hi) (hpprime j hj)).2
        (fun heq => hcross j hj i hi heq.symm)
    apply (Nat.coprime_mul_iff_right).2
    constructor
    · exact (Nat.coprime_mul_iff_left).2 ⟨hpp, hqp⟩
    · exact (Nat.coprime_mul_iff_left).2 ⟨hpq, hqq⟩
  have hprime : ∀ ⦃i⦄, i ∈ I → ∀ s, s.Prime →
      s ∣ term i → s ∣ n := by
    intro i hi s hs hst
    rcases hs.dvd_mul.mp hst with hsp | hsq
    · have hsi : s = p i :=
        (Nat.prime_dvd_prime_iff_eq hs (hpprime i hi)).mp hsp
      simpa [hsi] using hpdiv i hi
    · have hsi : s = q i :=
        (Nat.prime_dvd_prime_iff_eq hs (hqprime i hi)).mp hsq
      simpa [hsi] using hqdiv i hi
  have hupper' : ∀ i ∈ I, term i ≤ n := by
    intro i hi
    exact hupper i hi
  simpa [term] using sum_pairwise_terms_le_F I term hterm_inj hpositive hupper' hcop hprime

/- Concrete q-window specialization of the prime-pair bridge.  The matching may be produced by
   `exists_q_matching_of_qWindow_weights`; membership in the prime window supplies q-primality,
   while the remaining divisibility, cross-window, and product-band facts are exposed exactly as
   the hypotheses needed by the definition of `F`. -/
theorem card_mul_le_F_of_qWindow_matching
    {T α β γ δ rho : ℝ} {n B : ℕ} (I : Finset ℕ)
    {M r h : ℕ} (q : {p // p ∈ I} → ℕ)
    (hqinj : Function.Injective q)
    (hqmem : ∀ p, q p ∈
      primeWindow T γ δ \ badPairQWindow T α β γ δ rho M r h p.1)
    (hpprime : ∀ p ∈ I, p.Prime)
    (hpdiv : ∀ p ∈ I, p ∣ n)
    (hqdiv : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → qv ∣ n)
    (hcross : ∀ p ∈ I, ∀ j ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p ≠ qv)
    (hlower : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → B ≤ p * qv)
    (hupper : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p * qv ≤ n) :
    I.card * B ≤ F n := by
  let J : Finset {p // p ∈ I} := Finset.univ
  let pm : {p // p ∈ I} → ℕ := fun p ↦ p.1
  let qm : {p // p ∈ I} → ℕ := q
  have hpminj : Set.InjOn pm (J : Set {p // p ∈ I}) := by
    intro i hi j hj heq
    exact Subtype.ext heq
  have hqminj : Set.InjOn qm (J : Set {p // p ∈ I}) := by
    intro i hi j hj heq
    exact hqinj heq
  have hpmprime : ∀ i ∈ J, (pm i).Prime := by
    intro i hi
    exact hpprime i.1 i.property
  have hqmprime : ∀ i ∈ J, (qm i).Prime := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact (Finset.mem_filter.mp hqQ).2.1
  have hpmd : ∀ i ∈ J, pm i ∣ n := by
    intro i hi
    exact hpdiv i.1 i.property
  have hqmd : ∀ i ∈ J, qm i ∣ n := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hqdiv i.1 i.property (q i) hqQ
  have hcrossm : ∀ i ∈ J, ∀ j ∈ J, pm i ≠ qm j := by
    intro i hi j hj
    have hqQ : q j ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem j)).1
    exact hcross i.1 i.property j.1 j.property (q j) hqQ
  have hlowerm : ∀ i ∈ J, B ≤ pm i * qm i := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hlower i.1 i.property (q i) hqQ
  have hupperm : ∀ i ∈ J, pm i * qm i ≤ n := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hupper i.1 i.property (q i) hqQ
  have hJ := card_mul_le_F_of_injective_prime_pairing J pm qm
    hpmprime hqmprime hpmd hqmd hpminj hqminj hcrossm hlowerm hupperm
  simpa [J, pm, qm, Fintype.card_coe] using hJ

/- Variable-parameter q-window specialization.  The bad-pair certificate may use a denominator
   and numerator depending on the first prime; only the resulting membership in the common prime
   window is needed by the finite `F` bridge. -/
theorem card_mul_le_F_of_variable_qWindow_matching
    {T α β γ δ rho : ℝ} {n B : ℕ} (I : Finset ℕ)
    {M : ℕ} (rfun hfun : ℕ → ℕ) (q : {p // p ∈ I} → ℕ)
    (hqinj : Function.Injective q)
    (hqmem : ∀ p, q p ∈
      primeWindow T γ δ \
        badPairQWindow T α β γ δ rho M (rfun p.1) (hfun p.1) p.1)
    (hpprime : ∀ p ∈ I, p.Prime)
    (hpdiv : ∀ p ∈ I, p ∣ n)
    (hqdiv : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → qv ∣ n)
    (hcross : ∀ p ∈ I, ∀ j ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p ≠ qv)
    (hlower : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → B ≤ p * qv)
    (hupper : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p * qv ≤ n) :
    I.card * B ≤ F n := by
  let J : Finset {p // p ∈ I} := Finset.univ
  let pm : {p // p ∈ I} → ℕ := fun p ↦ p.1
  let qm : {p // p ∈ I} → ℕ := q
  have hpminj : Set.InjOn pm (J : Set {p // p ∈ I}) := by
    intro i hi j hj heq
    exact Subtype.ext heq
  have hqminj : Set.InjOn qm (J : Set {p // p ∈ I}) := by
    intro i hi j hj heq
    exact hqinj heq
  have hpmprime : ∀ i ∈ J, (pm i).Prime := by
    intro i hi
    exact hpprime i.1 i.property
  have hqmprime : ∀ i ∈ J, (qm i).Prime := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact (Finset.mem_filter.mp hqQ).2.1
  have hpmd : ∀ i ∈ J, pm i ∣ n := by
    intro i hi
    exact hpdiv i.1 i.property
  have hqmd : ∀ i ∈ J, qm i ∣ n := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hqdiv i.1 i.property (q i) hqQ
  have hcrossm : ∀ i ∈ J, ∀ j ∈ J, pm i ≠ qm j := by
    intro i hi j hj
    have hqQ : q j ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem j)).1
    exact hcross i.1 i.property j.1 j.property (q j) hqQ
  have hlowerm : ∀ i ∈ J, B ≤ pm i * qm i := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hlower i.1 i.property (q i) hqQ
  have hupperm : ∀ i ∈ J, pm i * qm i ≤ n := by
    intro i hi
    have hqQ : q i ∈ primeWindow T γ δ :=
      (Finset.mem_sdiff.mp (hqmem i)).1
    exact hupper i.1 i.property (q i) hqQ
  have hJ := card_mul_le_F_of_injective_prime_pairing J pm qm
    hpmprime hqmprime hpmd hqmd hpminj hqminj hcrossm hlowerm hupperm
  simpa [J, pm, qm, Fintype.card_coe] using hJ

/- One-call finite interface for the competitive-programming route
`weight bound → candidate count → Hall matching → F`.  All analytic work is isolated in the
per-p-slice reciprocal-weight and cardinality hypotheses; the matching and admissible-product
bookkeeping are discharged by the preceding theorems. -/
theorem card_mul_le_F_of_qWindow_weights
    {T α β γ δ rho : ℝ} {n B : ℕ} (I : Finset ℕ)
    {M r h : ℕ} (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) ≤ W)
    (hpprime : ∀ p ∈ I, p.Prime)
    (hpdiv : ∀ p ∈ I, p ∣ n)
    (hqdiv : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → qv ∣ n)
    (hcross : ∀ p ∈ I, ∀ j ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p ≠ qv)
    (hlower : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → B ≤ p * qv)
    (hupper : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p * qv ≤ n) :
    I.card * B ≤ F n := by
  obtain ⟨q, hqinj, hqmem⟩ := exists_q_matching_of_qWindow_weights
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    I hU hcard hweight
  exact card_mul_le_F_of_qWindow_matching
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (n := n) (B := B) I q hqinj hqmem hpprime hpdiv hqdiv hcross hlower hupper

/- Variable-parameter one-call interface.  This is the direct finite endpoint for the report's
   prime-dependent rational-approximation route: each `p` has its own `(rfun p, hfun p)` bad set,
   while the common q-window still supplies the prime/divisor/size hypotheses. -/
theorem card_mul_le_F_of_variable_qWindow_weights
    {T α β γ δ rho : ℝ} {n B : ℕ} (I : Finset ℕ)
    {M : ℕ} (rfun hfun : ℕ → ℕ)
    (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℕ → ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W p ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M (rfun p) (hfun p) p, ((q : ℝ)⁻¹)) ≤ W p)
    (hpprime : ∀ p ∈ I, p.Prime)
    (hpdiv : ∀ p ∈ I, p ∣ n)
    (hqdiv : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → qv ∣ n)
    (hcross : ∀ p ∈ I, ∀ j ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p ≠ qv)
    (hlower : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → B ≤ p * qv)
    (hupper : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p * qv ≤ n) :
    I.card * B ≤ F n := by
  obtain ⟨q, hqinj, hqmem⟩ := exists_q_matching_of_variable_qWindow_weights
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    I rfun hfun hU hcard hweight
  exact card_mul_le_F_of_variable_qWindow_matching
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (n := n) (B := B) I rfun hfun q hqinj hqmem hpprime hpdiv hqdiv hcross hlower hupper

/- Ordered-window convenience wrapper.  When the first p-window ends no later than the second
   q-window, `primeWindow_log_ratio_gt_one` discharges the cross-window non-equality required by
   the finite bridge.  Thus a Track-A caller only supplies membership in the first window. -/
theorem card_mul_le_F_of_variable_qWindow_weights_of_ordered_windows
    {T α β γ δ rho : ℝ} {n B : ℕ} (I : Finset ℕ)
    {M : ℕ} (rfun hfun : ℕ → ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ)
    (hU : 0 < Nat.floor (Real.exp (Real.rpow T δ)))
    {W : ℕ → ℝ}
    (hcard : ∀ p ∈ I,
      (I.card : ℝ) + (Nat.floor (Real.exp (Real.rpow T δ)) : ℝ) * W p ≤
        ((primeWindow T γ δ).card : ℝ))
    (hweight : ∀ p ∈ I,
      (∑ q ∈ badPairQWindow T α β γ δ rho M (rfun p) (hfun p) p, ((q : ℝ)⁻¹)) ≤ W p)
    (hpwindow : ∀ p ∈ I, p ∈ primeWindow T α β)
    (hpdiv : ∀ p ∈ I, p ∣ n)
    (hqdiv : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → qv ∣ n)
    (hlower : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → B ≤ p * qv)
    (hupper : ∀ p ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p * qv ≤ n) :
    I.card * B ≤ F n := by
  have hcross : ∀ p ∈ I, ∀ j ∈ I, ∀ qv, qv ∈ primeWindow T γ δ → p ≠ qv := by
    intro p hp j hj qv hqv
    have hpw := hpwindow p hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpw).2.1
    have hplogPos : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hratio : 1 < Real.log (qv : ℝ) / Real.log (p : ℝ) :=
      primeWindow_log_ratio_gt_one hpw hqv hT hβγ
    have hloglt : Real.log (p : ℝ) < Real.log (qv : ℝ) := by
      have h := (lt_div_iff₀ hplogPos).mp hratio
      simpa using h
    intro heq
    subst qv
    exact (lt_irrefl _ hloglt)
  have hpprime : ∀ p ∈ I, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp (hpwindow p hp)).2.1
  exact card_mul_le_F_of_variable_qWindow_weights
    (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
    (n := n) (B := B) I rfun hfun hU hcard hweight hpprime hpdiv hqdiv hcross hlower hupper

/- Full finite Hall-to-`F` bridge.  The candidate values are indexed by `κ`; Hall chooses one
   candidate for every `i ∈ I`, and the hypotheses below ensure that every candidate is prime,
   divides `n`, lies in the desired size band, and is disjoint from the first window.  The subtype
   bookkeeping is internal, so an analytic bad-pair estimate only needs to prove the Hall
   cardinality condition and these candidate-set properties. -/
theorem card_mul_le_F_of_hall_prime_pairing
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {n B : ℕ} (I : Finset ι)
    (p : ι → ℕ) (qval : κ → ℕ) (cand : ι → Finset κ)
    (hall : ∀ A : Finset {i // i ∈ I},
      A.card ≤ (A.biUnion (fun i ↦ cand i.1)).card)
    (hpprime : ∀ i ∈ I, (p i).Prime)
    (hqprime : ∀ i ∈ I, ∀ k ∈ cand i, (qval k).Prime)
    (hpdiv : ∀ i ∈ I, p i ∣ n)
    (hqdiv : ∀ i ∈ I, ∀ k ∈ cand i, qval k ∣ n)
    (hpinj : Set.InjOn p (I : Set ι))
    (hqval_inj : Function.Injective qval)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ cand j, p i ≠ qval k)
    (hlower : ∀ i ∈ I, ∀ k ∈ cand i, B ≤ p i * qval k)
    (hupper : ∀ i ∈ I, ∀ k ∈ cand i, p i * qval k ≤ n) :
    I.card * B ≤ F n := by
  obtain ⟨qmatch, hqmatch_inj, hqmatch_mem⟩ :=
    exists_injective_matching_of_hall I cand hall
  let J : Finset {i // i ∈ I} := Finset.univ
  let pm : {i // i ∈ I} → ℕ := fun i ↦ p i.1
  let qm : {i // i ∈ I} → ℕ := fun i ↦ qval (qmatch i)
  have hpminj : Set.InjOn pm (J : Set {i // i ∈ I}) := by
    intro i hi j hj heq
    apply Subtype.ext
    apply hpinj (x₁ := i.1) (x₂ := j.1) i.property j.property
    exact heq
  have hqminj : Set.InjOn qm (J : Set {i // i ∈ I}) := by
    intro i hi j hj heq
    exact hqmatch_inj (hqval_inj heq)
  have hpmprime : ∀ i ∈ J, (pm i).Prime := by
    intro i hi
    exact hpprime i.1 i.property
  have hqmprime : ∀ i ∈ J, (qm i).Prime := by
    intro i hi
    exact hqprime i.1 i.property (qmatch i) (hqmatch_mem i)
  have hpmd : ∀ i ∈ J, pm i ∣ n := by
    intro i hi
    exact hpdiv i.1 i.property
  have hqmd : ∀ i ∈ J, qm i ∣ n := by
    intro i hi
    exact hqdiv i.1 i.property (qmatch i) (hqmatch_mem i)
  have hcrossm : ∀ i ∈ J, ∀ j ∈ J, pm i ≠ qm j := by
    intro i hi j hj hEq
    exact hcross i.1 i.property j.1 j.property (qmatch j) (hqmatch_mem j) hEq
  have hlowerm : ∀ i ∈ J, B ≤ pm i * qm i := by
    intro i hi
    exact hlower i.1 i.property (qmatch i) (hqmatch_mem i)
  have hupperm : ∀ i ∈ J, pm i * qm i ≤ n := by
    intro i hi
    exact hupper i.1 i.property (qmatch i) (hqmatch_mem i)
  have hJ := card_mul_le_F_of_injective_prime_pairing J pm qm
    hpmprime hqmprime hpmd hqmd hpminj hqminj hcrossm hlowerm hupperm
  simpa [J, Fintype.card_coe] using hJ

/- Sum-valued Hall output.  The preceding theorem only retains a common lower bound `B`; this
   companion exposes the actual products selected by Hall.  It is the finite endpoint needed when
   a variable-window analytic estimate supplies a non-uniform product size for each matched pair. -/
theorem exists_matching_sum_le_F_of_hall_prime_pairing
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {n : ℕ} (I : Finset ι)
    (p : ι → ℕ) (qval : κ → ℕ) (cand : ι → Finset κ)
    (hall : ∀ A : Finset {i // i ∈ I},
      A.card ≤ (A.biUnion (fun i ↦ cand i.1)).card)
    (hpprime : ∀ i ∈ I, (p i).Prime)
    (hqprime : ∀ i ∈ I, ∀ k ∈ cand i, (qval k).Prime)
    (hpdiv : ∀ i ∈ I, p i ∣ n)
    (hqdiv : ∀ i ∈ I, ∀ k ∈ cand i, qval k ∣ n)
    (hpinj : Set.InjOn p (I : Set ι))
    (hqval_inj : Function.Injective qval)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ cand j, p i ≠ qval k)
    (hupper : ∀ i ∈ I, ∀ k ∈ cand i, p i * qval k ≤ n) :
    ∃ qmatch : {i // i ∈ I} → κ,
      Function.Injective qmatch ∧
      (∀ i, qmatch i ∈ cand i.1) ∧
      (∑ i : {i // i ∈ I}, p i.1 * qval (qmatch i)) ≤ F n := by
  obtain ⟨qmatch, hqmatch_inj, hqmatch_mem⟩ :=
    exists_injective_matching_of_hall I cand hall
  let J : Finset {i // i ∈ I} := Finset.univ
  let pm : {i // i ∈ I} → ℕ := fun i ↦ p i.1
  let qm : {i // i ∈ I} → ℕ := fun i ↦ qval (qmatch i)
  have hpminj : Set.InjOn pm (J : Set {i // i ∈ I}) := by
    intro i hi j hj heq
    apply Subtype.ext
    apply hpinj (x₁ := i.1) (x₂ := j.1) i.property j.property
    exact heq
  have hqminj : Set.InjOn qm (J : Set {i // i ∈ I}) := by
    intro i hi j hj heq
    exact hqmatch_inj (hqval_inj heq)
  have hpmprime : ∀ i ∈ J, (pm i).Prime := by
    intro i hi
    exact hpprime i.1 i.property
  have hqmprime : ∀ i ∈ J, (qm i).Prime := by
    intro i hi
    exact hqprime i.1 i.property (qmatch i) (hqmatch_mem i)
  have hpmd : ∀ i ∈ J, pm i ∣ n := by
    intro i hi
    exact hpdiv i.1 i.property
  have hqmd : ∀ i ∈ J, qm i ∣ n := by
    intro i hi
    exact hqdiv i.1 i.property (qmatch i) (hqmatch_mem i)
  have hcrossm : ∀ i ∈ J, ∀ j ∈ J, pm i ≠ qm j := by
    intro i hi j hj hEq
    exact hcross i.1 i.property j.1 j.property (qmatch j) (hqmatch_mem j) hEq
  have hpositive : ∀ i ∈ J, 2 ≤ pm i * qm i := by
    intro i hi
    calc
      2 ≤ 2 * 2 := by norm_num
      _ ≤ pm i * qm i := Nat.mul_le_mul (hpmprime i hi).two_le (hqmprime i hi).two_le
  have hupperm : ∀ i ∈ J, pm i * qm i ≤ n := by
    intro i hi
    exact hupper i.1 i.property (qmatch i) (hqmatch_mem i)
  have hterm_inj : Set.InjOn (fun i ↦ pm i * qm i) (J : Set {i // i ∈ I}) := by
    intro i hi j hj heq
    by_contra hij
    have hpi : (pm i).Prime := hpmprime i hi
    have hpdivterm : pm i ∣ pm i * qm i := dvd_mul_of_dvd_left (dvd_refl _) _
    have hpdivprod : pm i ∣ pm j * qm j := by
      change pm i * qm i = pm j * qm j at heq
      rw [← heq]
      exact hpdivterm
    rcases hpi.dvd_mul.mp hpdivprod with hpmj | hqmj
    · have hpeq : pm i = pm j :=
        (Nat.prime_dvd_prime_iff_eq hpi (hpmprime j hj)).mp hpmj
      exact hij (hpminj hi hj hpeq)
    · have hqeq : pm i = qm j :=
        (Nat.prime_dvd_prime_iff_eq hpi (hqmprime j hj)).mp hqmj
      exact (hcrossm i hi j hj) hqeq
  have hsum := sum_pairwise_terms_le_F J (fun i ↦ pm i * qm i)
    hterm_inj hpositive hupperm (by
      intro i hi j hj hij
      have hpi : Nat.Coprime (pm i) (pm j) := by
        exact (Nat.coprime_primes (hpmprime i hi) (hpmprime j hj)).2
          (fun heq => hij (hpminj hi hj heq))
      have hqi : Nat.Coprime (qm i) (qm j) := by
        exact (Nat.coprime_primes (hqmprime i hi) (hqmprime j hj)).2
          (fun heq => hij (hqminj hi hj heq))
      have hpq : Nat.Coprime (pm i) (qm j) := by
        exact (Nat.coprime_primes (hpmprime i hi) (hqmprime j hj)).2
          (fun heq => hcross i.1 i.property j.1 j.property (qmatch j)
            (hqmatch_mem j) heq)
      have hqp : Nat.Coprime (qm i) (pm j) := by
        exact (Nat.coprime_primes (hqmprime i hi) (hpmprime j hj)).2
          (fun heq => hcross j.1 j.property i.1 i.property (qmatch i)
            (hqmatch_mem i) heq.symm)
      apply (Nat.coprime_mul_iff_right).2
      constructor
      · exact (Nat.coprime_mul_iff_left).2 ⟨hpi, hqp⟩
      · exact (Nat.coprime_mul_iff_left).2 ⟨hpq, hqi⟩)
    (by
      intro i hi s hs hst
      rcases hs.dvd_mul.mp hst with hsp | hsq
      · have hsi : s = pm i :=
          (Nat.prime_dvd_prime_iff_eq hs (hpmprime i hi)).mp hsp
        simpa [hsi] using hpmd i hi
      · have hsi : s = qm i :=
          (Nat.prime_dvd_prime_iff_eq hs (hqmprime i hi)).mp hsq
        simpa [hsi] using hqmd i hi)
  refine ⟨qmatch, hqmatch_inj, hqmatch_mem, ?_⟩
  simpa [J, pm, qm] using hsum

/-- Distinct prime divisors give distinct positive powers in `primePowerTerms`. -/
theorem primePowerMap_injOn (n : ℕ) (hn : n ≠ 0) :
    Set.InjOn (fun p ↦ p ^ Nat.log p n) (n.primeFactors : Set ℕ) := by
  intro p hp q hq hpqpow
  change p ^ Nat.log p n = q ^ Nat.log q n at hpqpow
  have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have pq : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_primeFactors hp)
  have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_primeFactors hq)
  have heP : Nat.log p n ≠ 0 := (Nat.log_pos pp.one_lt hple).ne'
  have heQ : Nat.log q n ≠ 0 := (Nat.log_pos pq.one_lt hqle).ne'
  have hpdiv : p ∣ p ^ Nat.log p n := dvd_pow_self p heP
  have hqdiv : q ∣ q ^ Nat.log q n := dvd_pow_self q heQ
  rw [hpqpow] at hpdiv
  rw [← hpqpow] at hqdiv
  have hpdvdq : p ∣ q := pp.dvd_of_dvd_pow hpdiv
  have hqdvdp : q ∣ p := pq.dvd_of_dvd_pow hqdiv
  exact Nat.dvd_antisymm hpdvdq hqdvdp

/-- The canonical prime-power family satisfies the official admissibility conditions. -/
theorem primePowerTerms_isAdmissible (n : ℕ) (hn : n ≠ 0) :
    IsAdmissible n (primePowerTerms n) := by
  have hinj := primePowerMap_injOn n hn
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [primePowerTerms, Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_primeFactors hp)
    have hlogpos : 0 < Nat.log p n := Nat.log_pos pp.one_lt hple
    exact Finset.mem_Icc.mpr
      ⟨by
        have hpow : 1 < p ^ Nat.log p n := Nat.one_lt_pow hlogpos.ne' pp.one_lt
        omega,
       Nat.pow_log_le_self p hn⟩
  · intro a ha b hb hab
    change a ∈ primePowerTerms n at ha
    change b ∈ primePowerTerms n at hb
    rw [primePowerTerms, Finset.mem_image] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have pq : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hab rfl
    exact Nat.coprime_pow_primes _ _ pp pq hpq
  · intro a ha p pp hpa
    rw [primePowerTerms, Finset.mem_image] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    have qp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hpq : p ∣ q := pp.dvd_of_dvd_pow hpa
    have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq pp qp).mp hpq
    simpa [hpqeq] using Nat.dvd_of_mem_primeFactors hq

/- The canonical family has exactly one term for each distinct prime divisor.  This equality is
   useful when an analytic argument is phrased in terms of `ω(n)` but the finite `F` witness is
   written as the image of prime powers. -/
theorem card_primePowerTerms_eq_omega (n : ℕ) (hn : n ≠ 0) :
    (primePowerTerms n).card = omega n := by
  unfold primePowerTerms omega
  exact Finset.card_image_of_injOn (primePowerMap_injOn n hn)

/- The same image calculation identifies the sum of the canonical admissible family with the
   source function `f`; downstream proofs can therefore use the family without repeating the
   `Finset.sum_image` rewrite. -/
theorem sum_primePowerTerms_eq_f (n : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ primePowerTerms n, a) = f n := by
  unfold primePowerTerms f
  rw [Finset.sum_image (primePowerMap_injOn n hn)]

/-- The source-page functions satisfy `f(n) ≤ F(n)` for every positive `n`. -/
theorem f_le_F (n : ℕ) (hn : n ≠ 0) : f n ≤ F n := by
  have hsum := sum_le_F_of_admissible (primePowerTerms_isAdmissible n hn)
  rw [primePowerTerms, Finset.sum_image (primePowerMap_injOn n hn)] at hsum
  exact hsum

/-- An admissible family contains at most one term per prime divisor.  Since admissible terms are
at least two, sending each term to its least prime factor is an injection into the prime divisors
of `n`. -/
theorem card_admissible_le_omega {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) : A.card ≤ omega n := by
  have hminFac_inj : Set.InjOn Nat.minFac ((A.erase 1 : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hmin
    by_contra hab
    have haA : a ∈ A := Finset.mem_of_mem_erase ha
    have hbA : b ∈ A := Finset.mem_of_mem_erase hb
    have ha1 : a ≠ 1 := Finset.ne_of_mem_erase ha
    have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
    have hcop : Nat.Coprime a b := hA.2.1 haA hbA hab
    have hmindvdB : Nat.minFac a ∣ b := by
      rw [hmin]
      exact Nat.minFac_dvd b
    have hmOne := Nat.eq_one_of_dvd_coprimes hcop (Nat.minFac_dvd a) hmindvdB
    exact (Nat.minFac_prime ha1).ne_one hmOne
  have himage : (A.erase 1).image Nat.minFac ⊆ n.primeFactors := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    have haA : a ∈ A := Finset.mem_of_mem_erase ha
    have ha1 : a ≠ 1 := Finset.ne_of_mem_erase ha
    have hpPrime : (Nat.minFac a).Prime := Nat.minFac_prime ha1
    have hpDvdN : Nat.minFac a ∣ n :=
      hA.2.2 a haA (Nat.minFac a) hpPrime (Nat.minFac_dvd a)
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvdN, hn⟩
  have hcardErase : (A.erase 1).card ≤ n.primeFactors.card := by
    calc
      (A.erase 1).card = ((A.erase 1).image Nat.minFac).card :=
        (Finset.card_image_of_injOn hminFac_inj).symm
      _ ≤ n.primeFactors.card := Finset.card_le_card himage
  have h1 : 1 ∉ A := by
    intro h1A
    have hlower := (Finset.mem_Icc.mp (hA.1 h1A)).1
    omega
  simpa [Finset.erase_eq_of_notMem h1, omega] using hcardErase

/-- Backwards-compatible weakened form of `card_admissible_le_omega`. -/
theorem card_admissible_le_omega_add_one {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) : A.card ≤ omega n + 1 :=
  (card_admissible_le_omega hn hA).trans (Nat.le_succ _)

/-- A definition-level upper bound for every admissible family. -/
theorem sum_admissible_le_mul_omega_add_one {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) : ∑ a ∈ A, a ≤ n * (omega n + 1) := by
  calc
    ∑ a ∈ A, a ≤ ∑ _a ∈ A, n := by
      gcongr with a ha
      exact (Finset.mem_Icc.mp (hA.1 ha)).2
    _ = A.card * n := by simp
    _ ≤ (omega n + 1) * n := Nat.mul_le_mul_right n (card_admissible_le_omega_add_one hn hA)
    _ = n * (omega n + 1) := Nat.mul_comm _ _

lemma multiPrimePart_card_two_mul_le {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) :
    2 * (multiPrimePart A).card ≤ omega n := by
  let M : Finset ℕ := multiPrimePart A
  let U : Finset ℕ := M.biUnion (fun a ↦ a.primeFactors)
  have hMsubset : M ⊆ A.erase 1 := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hnonzero : ∀ a ∈ M, a ≠ 0 := by
    intro a ha
    have haA : a ∈ A := Finset.mem_of_mem_erase (hMsubset ha)
    have haIcc : a ∈ Finset.Icc 2 n := hA.1 haA
    have haone : 1 ≤ a := (by
      exact le_trans (by decide : 1 ≤ 2) (Finset.mem_Icc.mp haIcc).1)
    omega
  have hdisj : (M : Set ℕ).PairwiseDisjoint (fun a ↦ a.primeFactors) := by
    intro a ha b hb hab
    have haA : a ∈ A := Finset.mem_of_mem_erase (hMsubset ha)
    have hbA : b ∈ A := Finset.mem_of_mem_erase (hMsubset hb)
    exact (hA.2.1 haA hbA hab).disjoint_primeFactors
  have hUsub : U ⊆ n.primeFactors := by
    intro p hp
    change p ∈ M.biUnion (fun a ↦ a.primeFactors) at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a, ha, hpa⟩ := hp
    have haA : a ∈ A := Finset.mem_of_mem_erase (hMsubset ha)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpa
    have hpdvd : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
    exact Nat.mem_primeFactors.mpr ⟨hpp, hA.2.2 a haA p hpp hpdvd, hn⟩
  have hsumcard : (∑ a ∈ M, a.primeFactors.card) ≤ omega n := by
    change (∑ a ∈ M, a.primeFactors.card) ≤ n.primeFactors.card
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hUsub
  have hmulti : ∀ a ∈ M, 2 ≤ a.primeFactors.card := by
    intro a ha
    have haA : a ∈ A := Finset.mem_of_mem_erase (hMsubset ha)
    have haIcc : a ∈ Finset.Icc 2 n := hA.1 haA
    have ha1 : a ≠ 1 := Finset.ne_of_mem_erase (hMsubset ha)
    have ha2 : 2 ≤ a := (Finset.mem_Icc.mp haIcc).1
    have hnot : ¬ IsPrimePow a := (Finset.mem_filter.mp ha).2
    have hnontriv : a.primeFactors.Nontrivial :=
      (Nat.not_isPrimePow_iff_nontrivial_of_two_le ha2).mp hnot
    have hone : 1 < a.primeFactors.card :=
      (Finset.one_lt_card_iff_nontrivial).2 hnontriv
    omega
  calc
    2 * M.card = ∑ _a ∈ M, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ M, a.primeFactors.card := by
      gcongr with a ha
      exact hmulti a ha
    _ ≤ omega n := hsumcard

lemma primePowerPart_sum_le_f {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) :
    ∑ a ∈ primePowerPart A, a ≤ f n := by
  let P : Finset ℕ := primePowerPart A
  let Q : Finset ℕ := P.image Nat.minFac
  have hPsubset : P ⊆ A.erase 1 := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hPneone : ∀ a ∈ P, a ≠ 1 := by
    intro a ha
    exact Finset.ne_of_mem_erase (hPsubset ha)
  have hmin_inj : Set.InjOn Nat.minFac (P : Set ℕ) := by
    intro a ha b hb hab
    by_contra habne
    have haA : a ∈ A := Finset.mem_of_mem_erase (hPsubset ha)
    have hbA : b ∈ A := Finset.mem_of_mem_erase (hPsubset hb)
    have hcop : Nat.Coprime a b := hA.2.1 haA hbA habne
    have hmindvdB : Nat.minFac a ∣ b := by
      rw [hab]
      exact Nat.minFac_dvd b
    have hmOne := Nat.eq_one_of_dvd_coprimes hcop (Nat.minFac_dvd a) hmindvdB
    exact (Nat.minFac_prime (hPneone a ha)).ne_one hmOne
  have hQsub : Q ⊆ n.primeFactors := by
    intro p hp
    change p ∈ P.image Nat.minFac at hp
    rw [Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    have haA : a ∈ A := Finset.mem_of_mem_erase (hPsubset ha)
    have ha1 : a ≠ 1 := hPneone a ha
    have hpPrime : (Nat.minFac a).Prime := Nat.minFac_prime ha1
    have hpDvdN : Nat.minFac a ∣ n :=
      hA.2.2 a haA (Nat.minFac a) hpPrime (Nat.minFac_dvd a)
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvdN, hn⟩
  have hterm : ∀ a ∈ P,
      a ≤ Nat.minFac a ^ Nat.log (Nat.minFac a) n := by
    intro a ha
    have haA : a ∈ A := Finset.mem_of_mem_erase (hPsubset ha)
    have haIcc := hA.1 haA
    have ha1 : a ≠ 1 := hPneone a ha
    have haPP : IsPrimePow a := (Finset.mem_filter.mp ha).2
    obtain ⟨p, k, hp, hk, hpa⟩ := (isPrimePow_nat_iff a).mp haPP
    have hminPrime : (Nat.minFac a).Prime := Nat.minFac_prime ha1
    have hminDvdP : Nat.minFac a ∣ p := by
      apply hminPrime.dvd_of_dvd_pow
      rw [hpa]
      exact Nat.minFac_dvd a
    have hminEq : Nat.minFac a = p :=
      (Nat.prime_dvd_prime_iff_eq hminPrime hp).mp hminDvdP
    have hklog : k ≤ Nat.log (Nat.minFac a) n := by
      rw [hminEq]
      apply Nat.le_log_of_pow_le hp.one_lt
      rw [hpa]
      exact (Finset.mem_Icc.mp haIcc).2
    calc
      a = p ^ k := hpa.symm
      _ = Nat.minFac a ^ k := by rw [hminEq]
      _ ≤ Nat.minFac a ^ Nat.log (Nat.minFac a) n :=
        Nat.pow_le_pow_right (Nat.minFac_prime ha1).one_lt.le hklog
  have hQsum :
      (∑ a ∈ P, Nat.minFac a ^ Nat.log (Nat.minFac a) n) =
        ∑ p ∈ Q, p ^ Nat.log p n := by
    change (∑ a ∈ P, Nat.minFac a ^ Nat.log (Nat.minFac a) n) =
      ∑ p ∈ P.image Nat.minFac, p ^ Nat.log p n
    rw [Finset.sum_image]
    exact hmin_inj
  calc
    ∑ a ∈ primePowerPart A, a = ∑ a ∈ P, a := rfl
    _ ≤ ∑ a ∈ P, Nat.minFac a ^ Nat.log (Nat.minFac a) n := by
      gcongr with a ha
      exact hterm a ha
    _ = ∑ p ∈ Q, p ^ Nat.log p n := hQsum
    _ ≤ ∑ p ∈ n.primeFactors, p ^ Nat.log p n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hQsub (by simp)
    _ = f n := by rfl

lemma multiPrimePart_sum_le {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) :
    ∑ a ∈ multiPrimePart A, a ≤ n * (omega n / 2) := by
  let M : Finset ℕ := multiPrimePart A
  have hcard : M.card ≤ omega n / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    simpa [Nat.mul_comm] using (multiPrimePart_card_two_mul_le hn hA)
  calc
    ∑ a ∈ multiPrimePart A, a = ∑ a ∈ M, a := rfl
    _ ≤ ∑ _a ∈ M, n := by
      gcongr with a ha
      have haA : a ∈ A := by
        exact Finset.mem_of_mem_erase ((multiPrimePart_subset_erase A) ha)
      exact (Finset.mem_Icc.mp (hA.1 haA)).2
    _ = M.card * n := by simp
    _ ≤ (omega n / 2) * n := Nat.mul_le_mul_right n hcard
    _ = n * (omega n / 2) := Nat.mul_comm _ _

lemma sum_admissible_le_f_add_half {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : IsAdmissible n A) :
    ∑ a ∈ A, a ≤ f n + n * (omega n / 2) + 1 := by
  by_cases h1 : 1 ∈ A
  · have hsumErase := primePowerPart_sum_add_multiPrimePart_sum A
    have hsingle := primePowerPart_sum_le_f hn hA
    have hmulti := multiPrimePart_sum_le hn hA
    rw [← Finset.add_sum_erase A (fun a ↦ a) h1]
    calc
      1 + ∑ a ∈ A.erase 1, a =
          1 + ((∑ a ∈ primePowerPart A, a) + (∑ a ∈ multiPrimePart A, a)) := by rw [hsumErase]
      _ ≤ 1 + (f n + n * (omega n / 2)) := by gcongr
      _ = f n + n * (omega n / 2) + 1 := by omega
  · have hsumErase := primePowerPart_sum_add_multiPrimePart_sum A
    have hsingle := primePowerPart_sum_le_f hn hA
    have hmulti := multiPrimePart_sum_le hn hA
    calc
      (∑ a ∈ A, a) = ∑ a ∈ A.erase 1, a := by rw [Finset.erase_eq_of_notMem h1]
      _ = (∑ a ∈ primePowerPart A, a) + (∑ a ∈ multiPrimePart A, a) := hsumErase
      _ ≤ f n + n * (omega n / 2) := by gcongr
      _ ≤ f n + n * (omega n / 2) + 1 := Nat.le_add_right _ _

/-- A coefficient-`1/2` combinatorial upper bound, up to the permitted term `1`. -/
theorem F_le_f_add_half (n : ℕ) (hn : n ≠ 0) :
    F n ≤ f n + n * (omega n / 2) + 1 := by
  unfold F
  apply Finset.sup_le
  intro A hA
  exact sum_admissible_le_f_add_half hn (Finset.mem_filter.mp hA).2

/-- Real-valued form of `F_le_f_add_half`, with the floor removed at the cost of an inequality. -/
theorem F_le_f_add_half_real (n : ℕ) (hn : n ≠ 0) :
    (F n : ℝ) ≤ (f n : ℝ) + (n : ℝ) * (omega n : ℝ) / 2 + 1 := by
  have hnat := F_le_f_add_half n hn
  have hcast : (F n : ℝ) ≤ ((f n + n * (omega n / 2) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (F n : ℝ) ≤ ((f n + n * (omega n / 2) + 1 : ℕ) : ℝ) := hcast
    _ = (f n : ℝ) + (n : ℝ) * ((omega n / 2 : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ (f n : ℝ) + (n : ℝ) * (omega n : ℝ) / 2 + 1 := by
      gcongr
      have hdiv : ((omega n / 2 : ℕ) : ℝ) ≤ (omega n : ℝ) / 2 :=
        Nat.cast_div_le
      have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (n : ℝ))
      simpa [div_eq_mul_inv, mul_assoc] using hmul

/-- Finite sandwich for the extremal sum.  This is the basic local interface shared by all
    three asymptotic targets: the canonical prime-power family gives the lower bound, while
    the prime-power/multi-prime decomposition gives the coefficient-`1/2` upper bound. -/
theorem f_le_F_le_f_add_half (n : ℕ) (hn : n ≠ 0) :
    f n ≤ F n ∧ F n ≤ f n + n * (omega n / 2) + 1 := by
  exact ⟨f_le_F n hn, F_le_f_add_half n hn⟩

/-- Real-valued version of `f_le_F_le_f_add_half`, convenient for normalized limits. -/
theorem f_le_F_le_f_add_half_real (n : ℕ) (hn : n ≠ 0) :
    (f n : ℝ) ≤ (F n : ℝ) ∧
      (F n : ℝ) ≤ (f n : ℝ) + (n : ℝ) * (omega n : ℝ) / 2 + 1 := by
  constructor
  · exact_mod_cast f_le_F n hn
  · exact F_le_f_add_half_real n hn

/-- Normalized form of the coefficient-`1/2` upper interface.  Once the two analytic inputs
`f(n)=o(n log log n)` and normal order for `omega` are supplied on a density-one set, this is the
algebraic inequality used in the squeeze to `1/2`. -/
theorem F_div_scale_le
    {n : ℕ} (hn : 1 < n)
    (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    (F n : ℝ) / scale n ≤
      (f n : ℝ) / scale n +
        ((omega n : ℝ) / Real.log (Real.log (n : ℝ))) / 2 +
        1 / scale n := by
  have hn0 : n ≠ 0 := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hscale : 0 < scale n := by
    unfold scale
    exact mul_pos hnreal hloglog
  have hmain := F_le_f_add_half_real n hn0
  have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hscale)
  calc
    (F n : ℝ) / scale n ≤
        ((f n : ℝ) + (n : ℝ) * (omega n : ℝ) / 2 + 1) / scale n := hdiv
    _ = (f n : ℝ) / scale n +
        ((omega n : ℝ) / Real.log (Real.log (n : ℝ))) / 2 +
        1 / scale n := by
      unfold scale
      field_simp [hloglog.ne']

/-- Generic order-theoretic squeeze used by the density-one candidate.  The analytic work only has
to provide the lower bound and the three component limits; this lemma performs the final
coefficient-`1/2` passage without any number-theoretic assumptions. -/
theorem tendsto_of_half_le_of_le_add_half_add
    {ι : Type*} [Preorder ι] {l : Filter ι} {g u v e : ι → ℝ}
    (hlower : ∀ᶠ n : ι in l, (1 / 2 : ℝ) ≤ g n)
    (hupper : ∀ᶠ n : ι in l, g n ≤ u n + v n / 2 + e n)
    (hu : Tendsto u l (𝓝 0))
    (hv : Tendsto v l (𝓝 1))
    (he : Tendsto e l (𝓝 0)) :
    Tendsto g l (𝓝 (1 / 2 : ℝ)) := by
  have hvhalf : Tendsto (fun n ↦ v n / 2) l (𝓝 (1 / 2 : ℝ)) := by
    simpa using hv.div_const 2
  have hsum : Tendsto (fun n ↦ u n + v n / 2 + e n) l (𝓝 (1 / 2 : ℝ)) := by
    simpa [add_assoc] using (hu.add hvhalf).add he
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hlower] with n hn
    exact lt_of_lt_of_le ha hn
  · intro b hb
    filter_upwards [hupper, hsum.eventually (eventually_lt_nhds hb)] with n hng hsum
    exact lt_of_le_of_lt hng hsum

/- A global-filter specialization of the preceding squeeze.  It packages the purely formal upper
   transfer from `F_le_f_add_half`: all number-theoretic content is exposed as the three component
   limits and the eventual lower bound. -/
theorem tendsto_F_div_scale_of_eventual_components
    (hlower : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (F n : ℝ) / scale n)
    (hf : Tendsto (fun n : ℕ ↦ (f n : ℝ) / scale n) atTop (𝓝 0))
    (homega : Tendsto (fun n : ℕ ↦
      (omega n : ℝ) / Real.log (Real.log (n : ℝ))) atTop (𝓝 1))
    (hscale : Tendsto (fun n : ℕ ↦ 1 / scale n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (F n : ℝ) / scale n) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hupper : ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) / scale n ≤
        (f n : ℝ) / scale n +
          ((omega n : ℝ) / Real.log (Real.log (n : ℝ))) / 2 +
          1 / scale n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ),
      hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hll
    exact F_div_scale_le (n := n) (by omega) hll
  exact tendsto_of_half_le_of_le_add_half_add hlower hupper hf homega hscale

/- The same transfer on a density-one subtype.  The cofinality/positivity facts for the subtype
   are deliberately explicit: a density theorem can supply them, while this lemma only performs
   the finite combinatorial and order-theoretic passage to the coefficient `1/2`. -/
theorem tendsto_F_div_scale_on_set
    {A : Set ℕ}
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hlower : ∀ᶠ n : A in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hupper : ∀ᶠ n : A in atTop,
      (F (n : ℕ) : ℝ) / scale (n : ℕ) ≤
        (f (n : ℕ) : ℝ) / scale (n : ℕ) +
          ((omega (n : ℕ) : ℝ) /
            Real.log (Real.log ((n : ℕ) : ℝ))) / 2 +
          1 / scale (n : ℕ) := by
    filter_upwards [hlarge, hloglog] with n hn hll
    exact F_div_scale_le (n := (n : ℕ)) (by exact hn) hll
  exact tendsto_of_half_le_of_le_add_half_add hlower hupper hf homega hscale

/-- Consequently, the official source-page maximum is at most `n * (ω(n) + 1)`. The `+1`
accounts exactly for the permitted term `1`, which has no prime divisor. -/
theorem F_le_mul_omega_add_one (n : ℕ) (hn : n ≠ 0) :
    F n ≤ n * (omega n + 1) := by
  unfold F
  apply Finset.sup_le
  intro A hA
  exact sum_admissible_le_mul_omega_add_one hn (Finset.mem_filter.mp hA).2

/-- The elementary pointwise estimate used in the upper-bound half of the maximal-order
problem. Every summand in `f n` is at most `n`. -/
theorem f_le_mul_omega (n : ℕ) (hn : n ≠ 0) : f n ≤ n * omega n := by
  unfold f omega
  calc
    ∑ p ∈ n.primeFactors, p ^ Nat.log p n ≤ ∑ _p ∈ n.primeFactors, n := by
      gcongr with p hp
      exact Nat.pow_log_le_self p hn
    _ = n * n.primeFactors.card := by simp [Nat.mul_comm]

/- The endpoint deficit has an exact finite decomposition.  This turns the remaining Track-C
   problem into a lower bound for the sum of the individual prime-power deficits. -/
theorem endpoint_surplus_eq_sum {n : ℕ} (hn : n ≠ 0) :
    n * omega n - f n =
      ∑ p ∈ n.primeFactors, (n - p ^ Nat.log p n) := by
  unfold f omega
  calc
    n * n.primeFactors.card -
        ∑ p ∈ n.primeFactors, p ^ Nat.log p n =
        (∑ _p ∈ n.primeFactors, n) -
          ∑ p ∈ n.primeFactors, p ^ Nat.log p n := by
      simp [Nat.mul_comm]
    _ = ∑ p ∈ n.primeFactors, (n - p ^ Nat.log p n) := by
      symm
      apply Finset.sum_tsub_distrib
      intro p hp
      exact Nat.pow_log_le_self p hn

/- If n is not a prime power, every largest prime power below n is strictly below n.  Thus
   the endpoint surplus contains at least one unit for each distinct prime divisor. -/
theorem endpoint_surplus_ge_omega_of_not_primePower
    {n : ℕ} (hn : n ≠ 0) (hnot : ¬ IsPrimePow n) :
    omega n ≤ n * omega n - f n := by
  have hdef : ∀ p ∈ n.primeFactors, 1 ≤ n - p ^ Nat.log p n := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (Nat.dvd_of_mem_primeFactors hp)
    have hlogpos : 0 < Nat.log p n := Nat.log_pos hpp.one_lt hple
    have hpowle : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hn
    have hpowlt : p ^ Nat.log p n < n := by
      apply lt_of_le_of_ne hpowle
      intro heq
      apply hnot
      have hppow : IsPrimePow (p ^ Nat.log p n) :=
        hpp.isPrimePow.pow hlogpos.ne'
      simpa [heq] using hppow
    exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hpowlt)
  calc
    omega n = ∑ _p ∈ n.primeFactors, 1 := by simp [omega]
    _ ≤ ∑ p ∈ n.primeFactors, (n - p ^ Nat.log p n) := by
      gcongr with p hp
      exact hdef p hp
    _ = n * omega n - f n := (endpoint_surplus_eq_sum hn).symm

theorem endpoint_surplus_ge_omega_of_omega_ge_two
    {n : ℕ} (hn : n ≠ 0) (hω : 2 ≤ omega n) :
    omega n ≤ n * omega n - f n := by
  apply endpoint_surplus_ge_omega_of_not_primePower hn
  intro hprimepow
  have hone : omega n = 1 :=
    (isPrimePow_iff_card_primeFactors_eq_one.mp hprimepow)
  omega

/- Thresholded form of the endpoint decomposition.  Any family of prime factors whose individual
   deficits are at least `B` contributes at least `B` per member; this is the finite counting API
   to which an eventual endpoint-band cardinality estimate can be plugged. -/
theorem card_filter_endpoint_surplus_le {n B : ℕ} (hn : n ≠ 0) :
    ((n.primeFactors.filter
      (fun p ↦ B ≤ n - p ^ Nat.log p n)).card * B) ≤ n * omega n - f n := by
  let s := n.primeFactors.filter (fun p ↦ B ≤ n - p ^ Nat.log p n)
  have hpoint : ∀ p ∈ s, B ≤ n - p ^ Nat.log p n := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsum₁ : s.card * B ≤ ∑ p ∈ s, (n - p ^ Nat.log p n) := by
    calc
      s.card * B = ∑ _p ∈ s, B := by simp [Nat.mul_comm]
      _ ≤ ∑ p ∈ s, (n - p ^ Nat.log p n) := by
        gcongr with p hp
        exact hpoint p hp
  have hsum₂ : (∑ p ∈ s, (n - p ^ Nat.log p n)) ≤
      ∑ p ∈ n.primeFactors, (n - p ^ Nat.log p n) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp _
    exact Nat.zero_le _
  rw [endpoint_surplus_eq_sum hn]
  exact hsum₁.trans hsum₂

/-- Taking maxima preserves the elementary estimate `f(n) ≤ n ω(n)`. This isolates the
remaining analytic input for the upper bound: the maximal order of `ω`. -/
theorem maxUpTo_f_le_mul_maxUpTo_omega (x : ℕ) :
    maxUpTo f x ≤ x * maxUpTo omega x := by
  unfold maxUpTo
  apply Finset.sup_le
  intro n hn
  have hnx : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hn0 : n = 0
  · simp [hn0, f]
  · exact (f_le_mul_omega n hn0).trans
      (Nat.mul_le_mul hnx (Finset.le_sup (f := omega) hn))

/-- In the notation of the original paper, `m(x) ≤ x h(x)`, so the gap is genuine natural
subtraction rather than a truncated sign error. -/
theorem m_le_mul_h (x : ℕ) : m x ≤ x * h x := by
  simpa [m, h] using maxUpTo_f_le_mul_maxUpTo_omega x

/- The finite maximum `m(x)` is attained on the range `0 ≤ n ≤ x`; this packages the witness
   needed by the dichotomy below without adding any analytic assumption. -/
theorem exists_m_attainer (x : ℕ) :
    ∃ n ≤ x, m x = f n := by
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (x + 1))
    ⟨0, by simp⟩ f
  refine ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), ?_⟩
  simpa [m, maxUpTo] using heq

/- A finite dichotomy for the exact formula-(17) gap.  If `n ≤ x` attains `m(x)`, then the
   elementary bound `f(n) ≤ n*ω(n)` separates a deficit in the number of prime factors from a
   deficit in the endpoint: either `ω(n) < h(x)`, or the maximizing `n` must lie close to `x`.
   This is the first reduction used by the endpoint-band strategy. -/
theorem maximalOrderGap_ge_of_attainer
    {x n : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n) :
    x * h x - m x ≥
      x * (h x - omega n) + omega n * (x - n) := by
  have hkn : omega n ≤ h x := by
    unfold h
    apply Finset.le_sup
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hnx)
  have hf : f n ≤ n * omega n := f_le_mul_omega n hn0
  have hleft : x * omega n ≤ x * h x := Nat.mul_le_mul_left x hkn
  have hright : omega n * n ≤ x * omega n := by
    calc
      omega n * n = n * omega n := Nat.mul_comm _ _
      _ ≤ x * omega n := Nat.mul_le_mul_right (omega n) hnx
  have hsub : x * h x - n * omega n =
      x * (h x - omega n) + omega n * (x - n) := by
    calc
      x * h x - n * omega n = x * h x - omega n * n := by
        rw [Nat.mul_comm n (omega n)]
      _ = (x * h x - x * omega n) +
          (x * omega n - omega n * n) := by
        exact (Nat.sub_add_sub_cancel hleft hright).symm
      _ = x * (h x - omega n) +
          (x * omega n - omega n * n) := by
        rw [Nat.mul_sub_left_distrib]
      _ = x * (h x - omega n) +
          (omega n * x - omega n * n) := by
        congr 1
        exact congrArg (fun z => z - omega n * n) (Nat.mul_comm x (omega n))
      _ = x * (h x - omega n) + omega n * (x - n) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  rw [hattain]
  exact hsub ▸ Nat.sub_le_sub_left hf (x * h x)

/- In the strict `ω(n)<h(x)` branch, the preceding dichotomy already gives a full `x`-sized
   gap. This corollary is convenient when the endpoint-band argument is applied only to the
   equality case `ω(n)=h(x)`. -/
theorem maximalOrderGap_ge_x_of_attainer_of_omega_lt
    {x n : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n)
    (hstrict : omega n < h x) :
    x ≤ x * h x - m x := by
  have hgap := maximalOrderGap_ge_of_attainer hnx hn0 hattain
  have hone : 1 ≤ h x - omega n := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hstrict)
  have hxterm : x ≤ x * (h x - omega n) := by
    simpa using Nat.mul_le_mul_left x hone
  exact hxterm.trans ((Nat.le_add_right _ _).trans hgap)

/- Quantitative version of the strict branch.  Any eventual lower bound on the divisor-count
   deficit `h(x)-ω(n)` can be passed to the formula-(17) gap without reopening the subtraction
   bookkeeping. -/
theorem maximalOrderGap_ge_mul_of_attainer_of_omega_gap
    {x n K : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n)
    (hgap : K ≤ h x - omega n) :
    x * K ≤ x * h x - m x := by
  have hmain := maximalOrderGap_ge_of_attainer hnx hn0 hattain
  have hK : x * K ≤ x * (h x - omega n) := Nat.mul_le_mul_left x hgap
  exact hK.trans ((Nat.le_add_right _ _).trans hmain)

/- Exact endpoint-band decomposition in the equality branch.  When the attainer has the maximal
   divisor count `ω(n)=h(x)`, the gap is the sum of the endpoint distance and the finite prime-power
   surplus.  Combined with `endpoint_surplus_eq_sum`, this is the canonical Track-C reduction. -/
theorem maximalOrderGap_eq_of_attainer_of_omega_eq
    {x n : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n)
    (heq : omega n = h x) :
    x * h x - m x = h x * (x - n) + (n * omega n - f n) := by
  have hf : f n ≤ n * omega n := f_le_mul_omega n hn0
  have hf' : f n ≤ n * h x := by simpa [heq] using hf
  have hnh : n * h x ≤ x * h x := Nat.mul_le_mul_right (h x) hnx
  rw [hattain]
  calc
    x * h x - f n = (x * h x - n * h x) + (n * h x - f n) := by
      exact (Nat.sub_add_sub_cancel hnh hf').symm
    _ = h x * (x - n) + (n * omega n - f n) := by
      rw [Nat.mul_sub_left_distrib, ← heq]
      simp [Nat.mul_comm]

/- Endpoint-distance corollary for the equality branch.  Once `ω(n)=h(x)`, any lower bound on
   the distance `x-n` already gives a proportional gap; the prime-power surplus is nonnegative and
   may be discarded. -/
theorem maximalOrderGap_ge_mul_of_attainer_of_omega_eq_endpoint_gap
    {x n D : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n)
    (heq : omega n = h x) (hD : D ≤ x - n) :
    h x * D ≤ x * h x - m x := by
  have hdecomp := maximalOrderGap_eq_of_attainer_of_omega_eq hnx hn0 hattain heq
  have hdist : h x * D ≤ h x * (x - n) := Nat.mul_le_mul_left (h x) hD
  have hadd : h x * (x - n) ≤
      h x * (x - n) + (n * omega n - f n) := Nat.le_add_right _ _
  exact hdist.trans (hadd.trans_eq hdecomp.symm)

/- Endpoint-surplus counting form of the equality branch.  If at least `K` prime factors of the
   maximizing integer lose `B` or more from their endpoint powers, then the maximal-order gap is
   at least `K * B`.  This is the finite certificate naturally paired with a prime-power window
   estimate for formula (17). -/
theorem maximalOrderGap_ge_mul_of_attainer_of_endpoint_surplus_count
    {x n B K : ℕ} (hnx : n ≤ x) (hn0 : n ≠ 0) (hattain : m x = f n)
    (heq : omega n = h x)
    (hcount : K ≤ (n.primeFactors.filter
      (fun p ↦ B ≤ n - p ^ Nat.log p n)).card) :
    K * B ≤ x * h x - m x := by
  have hsurplus := card_filter_endpoint_surplus_le (n := n) (B := B) hn0
  have hcountMul : K * B ≤
      (n.primeFactors.filter
        (fun p ↦ B ≤ n - p ^ Nat.log p n)).card * B := by
    exact Nat.mul_le_mul_right B hcount
  have hsurplus' : K * B ≤ n * omega n - f n := hcountMul.trans hsurplus
  have hdecomp := maximalOrderGap_eq_of_attainer_of_omega_eq hnx hn0 hattain heq
  have hnonneg : n * omega n - f n ≤
      h x * (x - n) + (n * omega n - f n) := Nat.le_add_left _ _
  have hsum : K * B ≤ h x * (x - n) + (n * omega n - f n) :=
    hsurplus'.trans hnonneg
  simpa [maximalOrderGap] using hsum.trans_eq hdecomp.symm

/- Once `h(x)` has at least two prime factors, the elementary endpoint decomposition already
   gives a gap of at least `h(x)`.  This is weaker than formula (17), but it is a genuine
   unconditional Track-C consequence and records the exact role of the prime-power exception. -/
theorem maximalOrderGap_ge_h_of_h_ge_two {x : ℕ} (hh : 2 ≤ h x) :
    h x ≤ maximalOrderGap x := by
  obtain ⟨n, hnx, hattain⟩ := exists_m_attainer x
  by_cases hn0 : n = 0
  · have hxone : 1 ≤ x := by
      by_contra hx
      have hxzero : x = 0 := by omega
      subst x
      simp [h, maxUpTo, omega] at hh
    have hmul : h x ≤ x * h x := by
      calc
        h x = 1 * h x := by simp
        _ ≤ x * h x := Nat.mul_le_mul_right (h x) hxone
    simpa [maximalOrderGap, hattain, hn0, f] using hmul
  have hωle : omega n ≤ h x := by
    unfold h
    exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hnx))
  by_cases hstrict : omega n < h x
  · have hgapx := maximalOrderGap_ge_x_of_attainer_of_omega_lt hnx hn0 hattain hstrict
    have hxbound : h x ≤ x := by
      simpa [h] using maxUpTo_omega_le_self x
    exact hxbound.trans hgapx
  have heq : omega n = h x := Nat.le_antisymm hωle (Nat.le_of_not_gt hstrict)
  have hωtwo : 2 ≤ omega n := by simpa [heq] using hh
  have hsurplus := endpoint_surplus_ge_omega_of_omega_ge_two hn0 hωtwo
  have hsum : h x ≤ h x * (x - n) + (n * omega n - f n) := by
    have hsum' : omega n ≤ h x * (x - n) + (n * omega n - f n) :=
      hsurplus.trans (Nat.le_add_left _ _)
    simpa [heq] using hsum'
  exact hsum.trans_eq (maximalOrderGap_eq_of_attainer_of_omega_eq hnx hn0 hattain heq).symm

theorem eventually_h_ge_two : ∀ᶠ x : ℕ in atTop, 2 ≤ h x :=
  tendsto_h_atTop.eventually (eventually_ge_atTop 2)

/- The preceding finite estimate and `h(x) → ∞` imply that the unnormalised gap itself tends to
   infinity.  Formula (17) asks for the stronger gap divided by `x`; that normalization remains
   the genuinely unresolved endpoint-surplus step. -/
theorem tendsto_maximalOrderGap_atTop :
    Tendsto (fun x : ℕ ↦ maximalOrderGap x) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_h_atTop
  filter_upwards [eventually_h_ge_two] with x hx
  exact maximalOrderGap_ge_h_of_h_ge_two hx

theorem maximalOrderGap_add_m (x : ℕ) : maximalOrderGap x + m x = x * h x := by
  exact Nat.sub_add_cancel (m_le_mul_h x)

/-- The complete upper-bound half of the maximal-order problem. For every fixed positive
`ε`, the finite maximum of `f` is eventually at most `1 + ε` times the conjectured scale. -/
theorem eventually_maxUpTo_f_le_one_add_mul_scale (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (maxUpTo f x : ℝ) ≤ (1 + ε) * maximalOrderScale x := by
  filter_upwards [eventually_max_card_primeFactors_le_log_div_loglog ε hε] with x homega
  have hfinite := maxUpTo_f_le_mul_maxUpTo_omega x
  have homega' :
      (maxUpTo omega x : ℝ) ≤
        (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
    change (((Finset.range (x + 1)).sup fun n ↦ n.primeFactors.card : ℕ) : ℝ) ≤
      (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))
    exact homega
  calc
    (maxUpTo f x : ℝ) ≤ (x * maxUpTo omega x : ℕ) := by exact_mod_cast hfinite
    _ = (x : ℝ) * (maxUpTo omega x : ℝ) := by norm_cast
    _ ≤ (x : ℝ) *
        ((1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))) := by
      exact mul_le_mul_of_nonneg_left homega' (by positivity)
    _ = (1 + ε) * maximalOrderScale x := by
      unfold maximalOrderScale
      ring

/-- Normalized form of the sharp maximal-order upper bound. -/
theorem eventually_maxUpTo_f_ratio_le_one_add (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (maxUpTo f x : ℝ) / maximalOrderScale x ≤ 1 + ε := by
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_maxUpTo_f_le_one_add_mul_scale ε hε,
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with x hupper hlogx
  have hx : 1 < (x : ℝ) :=
    (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlogx)
  have hscale : 0 < maximalOrderScale x := by
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlogx))
      (Real.log_pos hlogx)
  exact (div_le_iff₀ hscale).mpr (by simpa [mul_comm] using hupper)

/- The proved eventual upper estimate has an intrinsic limsup formulation.  This is an
unconditional half of the ordinary maximal-order question and is the form most convenient for
combining with a selected-endpoint lower sequence. -/
theorem limsup_maxUpTo_f_ratio_le_one :
    Filter.limsup (fun x : ℕ ↦
      (maxUpTo f x : ℝ) / maximalOrderScale x) atTop ≤ 1 := by
  let u : ℕ → ℝ := fun x ↦
    (maxUpTo f x : ℝ) / maximalOrderScale x
  have hnonneg : ∀ᶠ x : ℕ in atTop, 0 ≤ u x := by
    filter_upwards [eventually_maximalOrderScale_pos] with x hx
    dsimp [u]
    exact div_nonneg (by positivity) hx.le
  have hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop u := by
    refine ⟨2, ?_⟩
    apply Filter.mem_map.mpr
    filter_upwards [eventually_maxUpTo_f_ratio_le_one_add (1 : ℝ) one_pos] with x hx
    dsimp [u]
    norm_num at hx ⊢
    exact hx
  have hcobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop u := by
    refine ⟨0, ?_⟩
    intro a ha
    have ha' : ∀ᶠ x : ℕ in atTop, u x ≤ a := Filter.mem_map.mp ha
    obtain ⟨x, hx⟩ := (hnonneg.and ha').exists
    exact hx.1.trans hx.2
  apply (Filter.limsup_le_iff hcobounded hbounded).2
  intro y hy
  let ε : ℝ := (y - 1) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  filter_upwards [eventually_maxUpTo_f_ratio_le_one_add ε hε] with x hx
  dsimp [u, ε] at hx ⊢
  linarith

/-- The exact analytic interface still missing from the lower-bound half of Track B.
Once prime selection gives the normalized lower estimate with every fixed positive error,
the already formalized upper estimate squeezes the ratio to `1`. -/
theorem tendsto_maximalOrder_of_eventually_one_sub_le
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        1 - ε ≤ (maxUpTo f x : ℝ) / maximalOrderScale x) :
    Tendsto (fun x : ℕ ↦
      (maxUpTo f x : ℝ) / maximalOrderScale x) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ := (1 - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hlower ε hε] with x hx
    dsimp [ε] at hx
    linarith
  · intro b hb
    let ε : ℝ := (b - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [eventually_maxUpTo_f_ratio_le_one_add ε hε] with x hx
    dsimp [ε] at hx
    linarith

/-- Any finite family of distinct prime divisors whose largest powers are all at least `B`
contributes at least `S.card * B` to `f`. This is the finite combinatorial output expected from
the prime-selection step in the lower-bound proof. -/
theorem card_mul_le_f_of_prime_family
    {n B : ℕ} {S : Finset ℕ} (hn : n ≠ 0)
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n)
    (hlower : ∀ p ∈ S, B ≤ p ^ Nat.log p n) :
    S.card * B ≤ f n := by
  have hsubset : S ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, hn⟩
  unfold f
  calc
    S.card * B = ∑ _p ∈ S, B := by simp
    _ ≤ ∑ p ∈ S, p ^ Nat.log p n := by
      gcongr with p hp
      exact hlower p hp
    _ ≤ ∑ p ∈ n.primeFactors, p ^ Nat.log p n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)

/- If the canonical prime powers all clear a common threshold, their exact cardinality gives a
   compact lower bound for `F`.  This is the direct `ω`-to-`F` route; Track A's two-prime method is
   needed precisely because its desired threshold is not available uniformly. -/
theorem omega_mul_le_F_of_primePower_lower
    {n B : ℕ} (hn : n ≠ 0)
    (hB : ∀ p ∈ n.primeFactors, B ≤ p ^ Nat.log p n) :
    omega n * B ≤ F n := by
  have h := card_mul_le_f_of_prime_family hn
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
    (fun p hp ↦ Nat.dvd_of_mem_primeFactors hp) hB
  exact h.trans (f_le_F n hn)

/- Weighted prime-power bridge.  A nonnegative real weight below the canonical prime-power term
   can be summed over any finite prime family dividing `n`; the result is bounded by `f(n)` and
   hence by the admissible optimum `F(n)`.  This is the pointwise companion to the weighted
   first/second-moment identities in `Erdos878.UnionBound`. -/
theorem weightedDivisorCount_le_F_of_prime_power_weights
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ) (w : ℕ → ℝ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hweight : ∀ p ∈ R, p ∣ n → 0 ≤ w p ∧
      w p ≤ (p ^ Nat.log p n : ℕ)) :
    weightedDivisorCount R w n ≤ (F n : ℝ) := by
  let S : Finset ℕ := R.filter (fun p ↦ p ∣ n)
  have hsubset : S ⊆ n.primeFactors := by
    intro p hp
    have hpR := (Finset.mem_filter.mp hp).1
    have hpd := (Finset.mem_filter.mp hp).2
    exact Nat.mem_primeFactors.mpr ⟨hprime p hpR, hpd, hn⟩
  have hsum : weightedDivisorCount R w n = ∑ p ∈ S, w p := by
    unfold weightedDivisorCount
    dsimp [S]
    rw [Finset.sum_filter]
  have hweighted : (∑ p ∈ S, w p) ≤
      ∑ p ∈ S, ((p ^ Nat.log p n : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact (hweight p (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hp).2).2
  have hsubsetSum : (∑ p ∈ S, ((p ^ Nat.log p n : ℕ) : ℝ)) ≤
      ∑ p ∈ n.primeFactors, ((p ^ Nat.log p n : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hnot
    positivity
  have hf : (∑ p ∈ n.primeFactors, ((p ^ Nat.log p n : ℕ) : ℝ)) =
      (f n : ℝ) := by
    simp [f]
  have hfF : (f n : ℝ) ≤ (F n : ℝ) := by
    exact_mod_cast f_le_F n hn
  calc
    weightedDivisorCount R w n = ∑ p ∈ S, w p := hsum
    _ ≤ ∑ p ∈ S, ((p ^ Nat.log p n : ℕ) : ℝ) := hweighted
    _ ≤ ∑ p ∈ n.primeFactors, ((p ^ Nat.log p n : ℕ) : ℝ) := hsubsetSum
    _ = (f n : ℝ) := hf
    _ ≤ (F n : ℝ) := hfF

/- Lower-endpoint variant for dyadic blocks.  It is enough to check the weight against
   `p^⌊log_p X⌋` at the left endpoint: monotonicity of `Nat.log` transports the bound to every
   `n ≥ X`. -/
theorem weightedDivisorCount_le_F_of_lower_endpoint
    {X n : ℕ} (hXn : X ≤ n) (hn : n ≠ 0) (R : Finset ℕ) (w : ℕ → ℝ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hweight : ∀ p ∈ R, 0 ≤ w p ∧
      w p ≤ (p ^ Nat.log p X : ℕ)) :
    weightedDivisorCount R w n ≤ (F n : ℝ) := by
  apply weightedDivisorCount_le_F_of_prime_power_weights hn R w hprime
  intro p hp hpd
  have hpdata := hweight p hp
  refine ⟨hpdata.1, hpdata.2.trans ?_⟩
  have hpprime := hprime p hp
  have hlog : Nat.log p X ≤ Nat.log p n := Nat.log_mono_right hXn
  have hpow : p ^ Nat.log p X ≤ p ^ Nat.log p n :=
    Nat.pow_le_pow_right hpprime.pos hlog
  exact_mod_cast hpow

/- A sharper weighted version keeps the individual prime-dependent power instead of replacing all
selected powers by one common minimum.  The elementary estimate
`n / p < p ^ log_p n` follows from the defining ceiling inequality for `Nat.log`. -/
theorem reciprocalPrimeMass_mul_le_f_of_prime_family
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n) :
    (n : ℝ) * ∑ p ∈ S, ((p : ℝ)⁻¹) ≤ (f n : ℝ) := by
  have hterm : ∀ p ∈ S, (n : ℝ) * ((p : ℝ)⁻¹) ≤
      (p ^ Nat.log p n : ℝ) := by
    intro p hpS
    have hdiv : (n : ℝ) / (p : ℝ) < (p ^ Nat.log p n : ℝ) := by
      apply (div_lt_iff₀ (by exact_mod_cast (hprime p hpS).pos)).2
      have hltNat : n < p ^ (Nat.log p n + 1) :=
        Nat.lt_pow_succ_log_self (hprime p hpS).one_lt n
      have hlt' : n < p ^ Nat.log p n * p := by
        simpa [pow_succ] using hltNat
      exact_mod_cast hlt'
    simpa [div_eq_mul_inv] using hdiv.le
  have hsubset : S ⊆ n.primeFactors := by
    intro p hpS
    exact Nat.mem_primeFactors.mpr ⟨hprime p hpS, hdvd p hpS, hn⟩
  calc
    (n : ℝ) * ∑ p ∈ S, ((p : ℝ)⁻¹) =
        ∑ p ∈ S, (n : ℝ) * ((p : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ S, (p ^ Nat.log p n : ℝ) := by
      exact Finset.sum_le_sum (fun p hpS ↦ hterm p hpS)
    _ ≤ ∑ p ∈ n.primeFactors, (p ^ Nat.log p n : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hpT hnot ↦ by positivity)
    _ = (f n : ℝ) := by
      simp [f]

theorem reciprocalPrimeMass_mul_le_F_of_prime_family
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n) :
    (n : ℝ) * ∑ p ∈ S, ((p : ℝ)⁻¹) ≤ (F n : ℝ) := by
  exact (reciprocalPrimeMass_mul_le_f_of_prime_family hn S hprime hdvd).trans
    (by exact_mod_cast f_le_F n hn)

/- Window form of the weighted bridge.  The analytic normal-order argument can state a lower
   bound for the reciprocal mass of the primes in `R` which divide `n`; this wrapper performs the
   finite filtering and sends that bound directly to the official `F` value. -/
theorem reciprocalPrimeMass_mul_le_F_of_prime_window
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) :
    (n : ℝ) * ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) ≤ (F n : ℝ) := by
  let S : Finset ℕ := R.filter (fun p ↦ p ∣ n)
  have hprimeS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  have hdvdS : ∀ p ∈ S, p ∣ n := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  simpa [S] using reciprocalPrimeMass_mul_le_F_of_prime_family hn S hprimeS hdvdS

/- Lower-mass form used by a normal-order proof.  It separates the analytic estimate
   `μ ≤ Σ_{p∈R, p∣n} 1/p` from the finite admissibility argument above. -/
theorem real_mul_le_F_of_prime_window_mass_lower
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) {μ : ℝ}
    (hmass : μ ≤ ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) :
    (n : ℝ) * μ ≤ (F n : ℝ) := by
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmass hnreal
  exact hmul.trans (reciprocalPrimeMass_mul_le_F_of_prime_window hn R hprime)

/- Cardinality form of the filtered reciprocal-mass bridge.  If at least `K` members of a prime
   window divide `n`, and the window is bounded above by `U`, then those members already force a
   concrete lower bound for `F n`.  This is the finite interface used by the dyadic candidate-count
   route; the remaining normal-order input is precisely a lower bound on the filtered cardinality. -/
theorem real_mul_le_F_of_prime_window_card_lower
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) {U : ℕ} (hU : 0 < U)
    (hupper : ∀ p ∈ R, p ≤ U) {K : ℝ}
    (hcard : K ≤ ((R.filter (fun p ↦ p ∣ n)).card : ℝ)) :
    (n : ℝ) * (K / (U : ℝ)) ≤ (F n : ℝ) := by
  have hUreal : 0 < (U : ℝ) := by exact_mod_cast hU
  have hmassCard := reciprocal_mass_filter_ge_card_div_upper R U n hU hprime hupper
  have hmassK : K / (U : ℝ) ≤
      ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
    have hdiv : K / (U : ℝ) ≤
        ((R.filter (fun p ↦ p ∣ n)).card : ℝ) / (U : ℝ) := by
      exact (div_le_div_iff_of_pos_right hUreal).2 hcard
    exact hdiv.trans hmassCard
  exact real_mul_le_F_of_prime_window_mass_lower hn R hprime hmassK

/- Two disjoint windows can be aggregated before the reciprocal-mass bridge is applied.  This is
   the finite form of the two-window escape route: separate cardinality estimates contribute
   additively as `K₁/U₁ + K₂/U₂`, while disjointness prevents double counting. -/
theorem real_mul_le_F_of_two_prime_window_card_lower
    {n : ℕ} (hn : n ≠ 0)
    (R₁ R₂ : Finset ℕ) (hdisj : Disjoint R₁ R₂)
    (hprime₁ : ∀ p ∈ R₁, p.Prime) (hprime₂ : ∀ p ∈ R₂, p.Prime)
    {U₁ U₂ : ℕ} (hU₁ : 0 < U₁) (hU₂ : 0 < U₂)
    (hupper₁ : ∀ p ∈ R₁, p ≤ U₁) (hupper₂ : ∀ p ∈ R₂, p ≤ U₂)
    {K₁ K₂ : ℝ}
    (hcard₁ : K₁ ≤ ((R₁.filter (fun p ↦ p ∣ n)).card : ℝ))
    (hcard₂ : K₂ ≤ ((R₂.filter (fun p ↦ p ∣ n)).card : ℝ)) :
    (n : ℝ) * (K₁ / (U₁ : ℝ) + K₂ / (U₂ : ℝ)) ≤ (F n : ℝ) := by
  have hU₁real : 0 < (U₁ : ℝ) := by exact_mod_cast hU₁
  have hU₂real : 0 < (U₂ : ℝ) := by exact_mod_cast hU₂
  have hmass₁ : K₁ / (U₁ : ℝ) ≤
      ∑ p ∈ R₁.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
    have hcardDiv : K₁ / (U₁ : ℝ) ≤
        ((R₁.filter (fun p ↦ p ∣ n)).card : ℝ) / (U₁ : ℝ) :=
      (div_le_div_iff_of_pos_right hU₁real).2 hcard₁
    exact hcardDiv.trans
      (reciprocal_mass_filter_ge_card_div_upper R₁ U₁ n hU₁ hprime₁ hupper₁)
  have hmass₂ : K₂ / (U₂ : ℝ) ≤
      ∑ p ∈ R₂.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
    have hcardDiv : K₂ / (U₂ : ℝ) ≤
        ((R₂.filter (fun p ↦ p ∣ n)).card : ℝ) / (U₂ : ℝ) :=
      (div_le_div_iff_of_pos_right hU₂real).2 hcard₂
    exact hcardDiv.trans
      (reciprocal_mass_filter_ge_card_div_upper R₂ U₂ n hU₂ hprime₂ hupper₂)
  have hdisjFilter : Disjoint (R₁.filter (fun p ↦ p ∣ n))
      (R₂.filter (fun p ↦ p ∣ n)) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_filter.mp hp₁).1 (Finset.mem_filter.mp hp₂).1
  have hfilterUnion :
      (R₁.filter (fun p ↦ p ∣ n)) ∪ (R₂.filter (fun p ↦ p ∣ n)) =
        (R₁ ∪ R₂).filter (fun p ↦ p ∣ n) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · have hp' := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union.mpr (Or.inl hp'.1), hp'.2⟩
      · have hp' := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union.mpr (Or.inr hp'.1), hp'.2⟩
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      rcases Finset.mem_union.mp hp'.1 with hp | hp
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp, hp'.2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, hp'.2⟩))
  have hmassUnion : K₁ / (U₁ : ℝ) + K₂ / (U₂ : ℝ) ≤
      ∑ p ∈ (R₁ ∪ R₂).filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
    calc
      K₁ / (U₁ : ℝ) + K₂ / (U₂ : ℝ) ≤
          (∑ p ∈ R₁.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) +
            ∑ p ∈ R₂.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) :=
        add_le_add hmass₁ hmass₂
      _ = ∑ p ∈ (R₁.filter (fun p ↦ p ∣ n)) ∪
            (R₂.filter (fun p ↦ p ∣ n)), ((p : ℝ)⁻¹) := by
        rw [Finset.sum_union hdisjFilter]
      _ = ∑ p ∈ (R₁ ∪ R₂).filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹) := by
        rw [hfilterUnion]
  have hprimeUnion : ∀ p ∈ R₁ ∪ R₂, p.Prime := by
    intro p hp
    simp only [Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact hprime₁ p hp
    · exact hprime₂ p hp
  have hF := reciprocalPrimeMass_mul_le_F_of_prime_window hn (R₁ ∪ R₂) hprimeUnion
  exact (mul_le_mul_of_nonneg_left hmassUnion (by positivity : 0 ≤ (n : ℝ))).trans hF

/- The existing second-moment API uses `divisorCount R n` rather than an explicit filtered-card
   expression.  This wrapper is definitionally the same statement, so it lets a normal-order
   estimate from `UnionBound` feed the `F` bridge without manual unfolding at the call site. -/
theorem real_mul_le_F_of_prime_window_divisorCount_lower
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) {U : ℕ} (hU : 0 < U)
    (hupper : ∀ p ∈ R, p ≤ U) {K : ℝ}
    (hcount : K ≤ divisorCount R n) :
    (n : ℝ) * (K / (U : ℝ)) ≤ (F n : ℝ) := by
  apply real_mul_le_F_of_prime_window_card_lower hn R hprime hU hupper
  simpa [divisorCount] using hcount

/- Dyadic-tail specialization of the cardinality interface.  The tail's built-in endpoint lemma
   supplies the common upper bound, so an analytic lower bound on the number of dividing primes
   can be used without restating any endpoint arithmetic at the call site. -/
theorem real_mul_le_F_of_dyadicPrimeTail_card_lower
    {n k m : ℕ} (hn : n ≠ 0) {K : ℝ}
    (hcard : K ≤
      ((dyadicDisjointPrimeTail k m).filter (fun p ↦ p ∣ n)).card) :
    (n : ℝ) *
        (K / (dyadicDisjointUpperEndpoint (k + m) : ℝ)) ≤ (F n : ℝ) := by
  have hU : 0 < dyadicDisjointUpperEndpoint (k + m) := by
    unfold dyadicDisjointUpperEndpoint
    positivity
  have hupper : ∀ p ∈ dyadicDisjointPrimeTail k m,
      p ≤ dyadicDisjointUpperEndpoint (k + m) := by
    intro p hp
    exact (Finset.mem_Icc.mp
      (dyadicDisjointPrimeTail_subset_Icc k m hp)).2
  apply real_mul_le_F_of_prime_window_card_lower hn
    (dyadicDisjointPrimeTail k m) (fun p hp ↦ dyadicDisjointPrimeTail_prime k m hp) hU hupper
  exact hcard

/- General fixed-loss normalization.  The official question needs any positive constant, not the
   sharp coefficient `1/2`; this version lets the window analysis pass its own `κ` directly. -/
theorem kappa_le_F_div_scale_of_prime_window_mass_lower
    {n : ℕ} (hn1 : 1 < n) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) {κ : ℝ} (_hκ : 0 ≤ κ)
    (hscale : 0 < scale n)
    (hmass : κ * scale n / (n : ℝ) ≤
      ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) :
    κ ≤ (F n : ℝ) / scale n := by
  have hn0 : n ≠ 0 := by omega
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hF := reciprocalPrimeMass_mul_le_F_of_prime_window hn0 R hprime
  have hmul : κ * scale n ≤ (n : ℝ) *
      (∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) := by
    calc
      κ * scale n = (n : ℝ) * (κ * scale n / (n : ℝ)) := by
        field_simp [hnreal.ne']
      _ ≤ (n : ℝ) *
          (∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hmass (le_of_lt hnreal)
  have hκscale : κ * scale n ≤ (F n : ℝ) := hmul.trans hF
  exact (le_div_iff₀ hscale).2 hκscale

/- Normalized half-scale specialization.  This is the exact algebraic target for a prime-window
   normal-order lemma: it suffices to show that the dividing primes carry at least half of the
   normalized scale as reciprocal mass. -/
theorem half_le_F_div_scale_of_prime_window_mass_lower
    {n : ℕ} (hn1 : 1 < n) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) (hscale : 0 < scale n)
    (hmass : scale n / (2 * (n : ℝ)) ≤
      ∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) :
    (1 / 2 : ℝ) ≤ (F n : ℝ) / scale n := by
  have hn0 : n ≠ 0 := by omega
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hF := reciprocalPrimeMass_mul_le_F_of_prime_window hn0 R hprime
  have hhalf : scale n / 2 ≤ (F n : ℝ) := by
    calc
      scale n / 2 = (n : ℝ) * (scale n / (2 * (n : ℝ))) := by
        field_simp
      _ ≤ (n : ℝ) *
          (∑ p ∈ R.filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hmass (le_of_lt hnreal)
      _ ≤ (F n : ℝ) := hF
  apply (le_div_iff₀ hscale).2
  calc
    (1 / 2 : ℝ) * scale n = scale n / 2 := by ring
    _ ≤ (F n : ℝ) := hhalf

/- Normalized cardinality counterpart of the preceding half-mass theorem.  This is the exact
   endpoint needed when the second-moment argument is phrased as a lower bound for the number of
   dividing primes rather than for their reciprocal mass. -/
theorem half_le_F_div_scale_of_prime_window_card_lower
    {n : ℕ} (hn1 : 1 < n) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime) {U : ℕ} (hU : 0 < U)
    (hupper : ∀ p ∈ R, p ≤ U) (hscale : 0 < scale n)
    (hcard : scale n / (2 * (n : ℝ)) ≤
      ((R.filter (fun p ↦ p ∣ n)).card : ℝ) / (U : ℝ)) :
    (1 / 2 : ℝ) ≤ (F n : ℝ) / scale n := by
  have hmassCard := reciprocal_mass_filter_ge_card_div_upper R U n hU hprime hupper
  exact half_le_F_div_scale_of_prime_window_mass_lower hn1 R hprime hscale
    (hcard.trans hmassCard)

/- Concrete dyadic-family specialization.  The all-endpoint family from `PrimeMass` already
   carries primality and the upper-endpoint contract `p ≤ n`; therefore a normal-order estimate
   for just its filtered cardinality is enough to produce the exact half-scale lower bound.
   This is the competition-style entry point for the two-moment route: all finite bookkeeping is
   discharged here, leaving only the cardinality estimate on the chosen integers. -/
theorem half_le_F_div_scale_of_dyadicDisjointPrimeFamilyUpTo_card_lower
    {n : ℕ} (hn1 : 1 < n) (hscale : 0 < scale n)
    (hcard : scale n / (2 * (n : ℝ)) ≤
      ((dyadicDisjointPrimeFamilyUpTo n).filter (fun p ↦ p ∣ n)).card / (n : ℝ)) :
    (1 / 2 : ℝ) ≤ (F n : ℝ) / scale n := by
  have hn0 : n ≠ 0 := by omega
  have hU : 0 < n := by omega
  have hupper : ∀ p ∈ dyadicDisjointPrimeFamilyUpTo n, p ≤ n := by
    intro p hp
    exact (Finset.mem_Icc.mp
      (dyadicDisjointPrimeFamilyUpTo_subset_Icc n hp)).2
  exact half_le_F_div_scale_of_prime_window_card_lower hn1
    (dyadicDisjointPrimeFamilyUpTo n)
    (fun p hp ↦ dyadicDisjointPrimeFamilyUpTo_prime n hp)
    hU hupper hscale hcard

/- The lower-bound certificate can be stated directly in the language of a moving prime window.
   This wrapper consumes the reciprocal mass of the primes dividing each `n`, applies the finite
   admissible-family lemma, and then invokes the density-one squeeze above.  Thus a future analytic
   proof need only establish this mass estimate on the chosen density-one set. -/
theorem tendsto_F_div_scale_on_set_of_prime_window_mass_lower
    {A : Set ℕ} (R : A → Finset ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hmass : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ∑ p ∈ (R n).filter (fun p ↦ p ∣ (n : ℕ)), ((p : ℝ)⁻¹))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hscalePos : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ) := by
    filter_upwards [hlarge, hloglog] with n hn hll
    unfold scale
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))) hll
  have hlower : ∀ᶠ n : A in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    filter_upwards [hlarge, hmass, hscalePos] with n hn hmn hsn
    exact half_le_F_div_scale_of_prime_window_mass_lower
      (n := (n : ℕ)) hn (R n) (hprime n) hsn hmn
  exact tendsto_F_div_scale_on_set hlarge hloglog hlower hf homega hscale

/- Concrete reciprocal-mass version for the all-endpoint dyadic family.  Unlike the crude
   cardinality specialization, this preserves the `1/p` weights and is therefore compatible with
   the expected `log log n` mass scale.  An analytic normal-order argument may target this theorem
   directly, with no artificial common upper-endpoint loss. -/
theorem tendsto_F_div_scale_on_set_of_dyadicDisjointPrimeFamilyUpTo_mass_lower
    {A : Set ℕ}
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hmass : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ∑ p ∈ (dyadicDisjointPrimeFamilyUpTo (n : ℕ)).filter
          (fun p ↦ p ∣ (n : ℕ)), ((p : ℝ)⁻¹))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_F_div_scale_on_set_of_prime_window_mass_lower
    (R := fun n : A ↦ dyadicDisjointPrimeFamilyUpTo (n : ℕ))
  · exact hlarge
  · exact hloglog
  · intro n p hp
    exact dyadicDisjointPrimeFamilyUpTo_prime (n : ℕ) hp
  · exact hmass
  · exact hf
  · exact homega
  · exact hscale

/- Cardinality form of the same moving-window certificate.  It is the direct adapter for the
   second-moment/Hall APIs, which naturally return a lower bound for `divisorCount` rather than
   for the reciprocal mass itself. -/
theorem tendsto_F_div_scale_on_set_of_prime_window_card_lower
    {A : Set ℕ} (R : A → Finset ℕ) (U : A → ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hU : ∀ᶠ n : A in atTop, 0 < U n)
    (hupper : ∀ᶠ n : A in atTop, ∀ p ∈ R n, p ≤ U n)
    (hcard : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ((R n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U n : ℝ))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_F_div_scale_on_set_of_prime_window_mass_lower R hlarge hloglog hprime
  · filter_upwards [hU, hupper, hcard] with n hn hpn hcn
    have hmass := reciprocal_mass_filter_ge_card_div_upper
      (R n) (U n) (n : ℕ) hn (hprime n) (hpn)
    exact hcn.trans hmass
  · exact hf
  · exact homega
  · exact hscale

/- Two-window density-one adapter.  The disjoint finite bridge above lets the analytic caller
   prove a single additive estimate `card₁/U₁ + card₂/U₂ ≥ scale/(2n)`, which is often easier
   than forcing one window to carry the whole mass. -/
theorem tendsto_F_div_scale_on_set_of_two_prime_window_card_lower
    {A : Set ℕ} (R₁ R₂ : A → Finset ℕ) (U₁ U₂ : A → ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hdisj : ∀ n : A, Disjoint (R₁ n) (R₂ n))
    (hprime₁ : ∀ n : A, ∀ p ∈ R₁ n, p.Prime)
    (hprime₂ : ∀ n : A, ∀ p ∈ R₂ n, p.Prime)
    (hU₁ : ∀ᶠ n : A in atTop, 0 < U₁ n)
    (hU₂ : ∀ᶠ n : A in atTop, 0 < U₂ n)
    (hupper₁ : ∀ᶠ n : A in atTop, ∀ p ∈ R₁ n, p ≤ U₁ n)
    (hupper₂ : ∀ᶠ n : A in atTop, ∀ p ∈ R₂ n, p ≤ U₂ n)
    (hcard : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ((R₁ n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U₁ n : ℝ) +
          ((R₂ n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U₂ n : ℝ))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hscalePos : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ) := by
    filter_upwards [hlarge, hloglog] with n hn hll
    unfold scale
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))) hll
  have hlower : ∀ᶠ n : A in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    filter_upwards [hlarge, hU₁, hU₂, hupper₁, hupper₂, hcard, hscalePos]
      with n hn hU₁n hU₂n hup₁ hup₂ hcn hsn
    have hn0 : (n : ℕ) ≠ 0 := by omega
    have hF := real_mul_le_F_of_two_prime_window_card_lower
      hn0 (R₁ n) (R₂ n) (hdisj n) (hprime₁ n) (hprime₂ n)
        hU₁n hU₂n (hup₁) (hup₂)
        (K₁ := ((R₁ n).filter (fun p ↦ p ∣ (n : ℕ))).card)
        (K₂ := ((R₂ n).filter (fun p ↦ p ∣ (n : ℕ))).card)
        (le_refl _) (le_refl _)
    have hprod : (n : ℝ) * (scale (n : ℕ) /
        (2 * ((n : ℕ) : ℝ))) ≤ (F (n : ℕ) : ℝ) := by
      exact (mul_le_mul_of_nonneg_left hcn (by positivity : 0 ≤ (n : ℝ))).trans hF
    have hhalf : scale (n : ℕ) / 2 ≤ (F (n : ℕ) : ℝ) := by
      calc
        scale (n : ℕ) / 2 = (n : ℝ) *
            (scale (n : ℕ) / (2 * ((n : ℕ) : ℝ))) := by
          field_simp
        _ ≤ (F (n : ℕ) : ℝ) := hprod
    apply (le_div_iff₀ hsn).2
    simpa [div_eq_mul_inv, mul_comm] using hhalf
  exact tendsto_F_div_scale_on_set hlarge hloglog hlower hf homega hscale

/- Moving-window version of the concrete dyadic specialization.  It packages the standard
   density-one hypotheses once and for all, so a future second-moment proof only has to provide
   the eventual lower bound for the number of members of the all-endpoint family dividing `n`.
   The family itself is independent of the density set, which keeps the analytic certificate
   easy to state and avoids an extra subtype-level definition. -/
theorem tendsto_F_div_scale_on_set_of_dyadicDisjointPrimeFamilyUpTo_card_lower
    {A : Set ℕ}
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hcard : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ((dyadicDisjointPrimeFamilyUpTo (n : ℕ)).filter
          (fun p ↦ p ∣ (n : ℕ))).card / ((n : ℕ) : ℝ))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_F_div_scale_on_set_of_prime_window_card_lower
    (R := fun n : A ↦ dyadicDisjointPrimeFamilyUpTo (n : ℕ))
    (U := fun n : A ↦ (n : ℕ)) hlarge hloglog
  · intro n p hp
    exact dyadicDisjointPrimeFamilyUpTo_prime (n : ℕ) hp
  · filter_upwards [hlarge] with n hn
    exact Nat.zero_lt_of_lt hn
  · filter_upwards [] with n p hp
    exact (Finset.mem_Icc.mp
      (dyadicDisjointPrimeFamilyUpTo_subset_Icc (n : ℕ) hp)).2
  · exact hcard
  · exact hf
  · exact homega
  · exact hscale

/- The same adapter in the `divisorCount` notation used by the second-moment library.  This is
   definitionally the filtered-cardinality hypothesis above, but exposing it as a named theorem
   lets a variance/Halász estimate plug in without any unfolding at the call site. -/
theorem tendsto_F_div_scale_on_set_of_dyadicDisjointPrimeFamilyUpTo_divisorCount_lower
    {A : Set ℕ}
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hcount : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        divisorCount (dyadicDisjointPrimeFamilyUpTo (n : ℕ)) (n : ℕ) /
          ((n : ℕ) : ℝ))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_F_div_scale_on_set_of_dyadicDisjointPrimeFamilyUpTo_card_lower
    hlarge hloglog
  · simpa [divisorCount] using hcount
  · exact hf
  · exact homega
  · exact hscale

/- The PrimeMass second-moment theorem is naturally a moving-endpoint statement.  This adapter
   extracts the corresponding eventual good-count estimate: for every fixed positive loss `η`,
   all but an `η`-fraction of `1 ≤ n ≤ X` have at least half the reciprocal-prime mean many
   divisors from the all-endpoint dyadic family.  It is an actual density-one input, although it
   still does not by itself provide the reciprocal mass needed by the sharp `F` construction. -/
theorem eventually_dyadicDisjointPrimeFamilyUpTo_good_count_ge_fraction
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (1 - η) * (X : ℝ) ≤
        (((Finset.Icc 1 X).filter
          (fun n ↦
            (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2 ≤
              divisorCount (dyadicDisjointPrimeFamilyUpTo X) n)).card : ℝ) := by
  let B : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦ divisorCount (dyadicDisjointPrimeFamilyUpTo X) n <
        (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2)
  let G : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦ (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2 ≤
        divisorCount (dyadicDisjointPrimeFamilyUpTo X) n)
  have hbad : Tendsto (fun X : ℕ ↦ ((B X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    simpa [B] using tendsto_dyadicDisjointPrimeFamilyUpTo_exceptionalRatio_zero
  have hpartition : ∀ X : ℕ, B X ∪ G X = Finset.Icc 1 X := by
    intro X
    ext n
    by_cases hn : n ∈ Finset.Icc 1 X
    · simp only [B, G, Finset.mem_union, Finset.mem_filter]
      by_cases hlt : divisorCount (dyadicDisjointPrimeFamilyUpTo X) n <
          (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2
      · exact iff_of_true (Or.inl ⟨hn, hlt⟩) hn
      · exact iff_of_true (Or.inr ⟨hn, le_of_not_gt hlt⟩) hn
    · simp [B, G, hn]
  have hdisj : ∀ X : ℕ, Disjoint (B X) (G X) := by
    intro X
    rw [Finset.disjoint_left]
    intro n hnB hnG
    exact (not_lt_of_ge (Finset.mem_filter.mp hnG).2)
      (Finset.mem_filter.mp hnB).2
  have hcard : ∀ X : ℕ, ((B X).card : ℝ) + ((G X).card : ℝ) = (X : ℝ) := by
    intro X
    have hnat : (B X).card + (G X).card = X := by
      calc
        (B X).card + (G X).card = (B X ∪ G X).card :=
          (Finset.card_union_of_disjoint (hdisj X)).symm
        _ = (Finset.Icc 1 X).card := by rw [hpartition X]
        _ = X := by
          rw [Nat.card_Icc]
          omega
    exact_mod_cast hnat
  have hbadη : ∀ᶠ X : ℕ in atTop,
      ((B X).card : ℝ) / (X : ℝ) < η :=
    hbad.eventually (eventually_lt_nhds hη)
  filter_upwards [hbadη, eventually_gt_atTop (0 : ℕ)] with X hBX hX
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hBbound : ((B X).card : ℝ) ≤ η * (X : ℝ) := by
    apply (div_le_iff₀ hXreal).mp
    exact hBX.le
  have hGbound : (1 - η) * (X : ℝ) ≤ ((G X).card : ℝ) := by
    have hc := hcard X
    linarith
  simpa [G] using hGbound

/- Pointwise companion for the preceding count estimate.  It is deliberately normalized by the
   ambient endpoint `X`: the finite cardinality-to-reciprocal conversion costs exactly `1/X`,
   making the remaining loss visible instead of silently claiming the sharp `F` scale. -/
theorem real_mul_le_F_of_dyadicDisjointPrimeFamilyUpTo_good_count
    {X n : ℕ} (hn : n ≠ 0) (hX : 0 < X) {μ : ℝ}
    (hgood : μ / 2 ≤ divisorCount (dyadicDisjointPrimeFamilyUpTo X) n) :
    (n : ℝ) * ((μ / 2) / (X : ℝ)) ≤ (F n : ℝ) := by
  have hupper : ∀ p ∈ dyadicDisjointPrimeFamilyUpTo X, p ≤ X := by
    intro p hp
    exact (Finset.mem_Icc.mp
      (dyadicDisjointPrimeFamilyUpTo_subset_Icc X hp)).2
  have hcount : μ / 2 ≤
      ((dyadicDisjointPrimeFamilyUpTo X).filter (fun p ↦ p ∣ n)).card := by
    simpa [divisorCount] using hgood
  exact real_mul_le_F_of_prime_window_card_lower hn
    (dyadicDisjointPrimeFamilyUpTo X)
    (fun p hp ↦ dyadicDisjointPrimeFamilyUpTo_prime X hp)
    hX hupper hcount

/- The preceding density-count statement can be transported through the finite `F` bridge.
   At a fixed endpoint `X`, every good integer `n` satisfies the explicit lower bound
   `n * (μ_X/2)/X ≤ F(n)`, so the set of integers meeting that `F` threshold has at least the
   same cardinality.  This is the finite block statement needed before any diagonal or dyadic
   density argument; no asymptotic claim about the moving threshold is hidden here. -/
theorem eventually_dyadicDisjointPrimeFamilyUpTo_good_F_count_ge_fraction
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (1 - η) * (X : ℝ) ≤
        (((Finset.Icc 1 X).filter
          (fun n : ℕ ↦
            (n : ℝ) *
                (((∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2) /
                  (X : ℝ)) ≤ (F n : ℝ))).card : ℝ) := by
  let G : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦
        (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2 ≤
          divisorCount (dyadicDisjointPrimeFamilyUpTo X) n)
  let H : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦
        (n : ℝ) *
            (((∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2) /
              (X : ℝ)) ≤ (F n : ℝ))
  have hGcard := eventually_dyadicDisjointPrimeFamilyUpTo_good_count_ge_fraction hη
  filter_upwards [hGcard, eventually_gt_atTop (0 : ℕ)] with X hG hX
  have hsub : G X ⊆ H X := by
    intro n hn
    have hnG := Finset.mem_filter.mp hn
    have hnIcc := hnG.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
    have hn0 : n ≠ 0 := by omega
    have hF := real_mul_le_F_of_dyadicDisjointPrimeFamilyUpTo_good_count
      (X := X) (n := n) hn0 hX hnG.2
    exact Finset.mem_filter.mpr ⟨hnIcc, hF⟩
  have hcard : ((G X).card : ℝ) ≤ ((H X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hlower : (1 - η) * (X : ℝ) ≤ ((G X).card : ℝ) := by
    simpa [G] using hG
  simpa [H] using hlower.trans hcard

/- The little-o hypothesis used by the official first question already contains the ratio limit
   needed by the squeeze: Mathlib's `IsLittleO.tendsto_div_nhds_zero` supplies it directly. -/
theorem tendsto_F_div_scale_on_set_of_prime_window_mass_lower_littleO
    {A : Set ℕ} (R : A → Finset ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hmass : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ∑ p ∈ (R n).filter (fun p ↦ p ∣ (n : ℕ)), ((p : ℝ)⁻¹))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  exact tendsto_F_div_scale_on_set_of_prime_window_mass_lower R hlarge hloglog hprime hmass
    hfSmall.tendsto_div_nhds_zero homega hscale

/- Weighted Track-A adapter.  This is the exact form consumed by a weighted moment argument:
   once the chosen weights are nonnegative, lie below the canonical prime powers, and have
   weighted divisor sum at least `scale/2` on a density-one set, the same squeeze gives the sharp
   `F/scale → 1/2` limit. -/
theorem tendsto_F_div_scale_on_set_of_weightedDivisorCount_lower
    {A : Set ℕ} (R : A → Finset ℕ) (w : A → ℕ → ℝ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hweight : ∀ᶠ n : A in atTop,
      ∀ p ∈ R n, p ∣ (n : ℕ) → 0 ≤ w n p ∧
        w n p ≤ (p ^ Nat.log p (n : ℕ) : ℕ))
    (hcount : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / 2 ≤ weightedDivisorCount (R n) (w n) (n : ℕ))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hscalePos : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ) := by
    filter_upwards [hlarge, hloglog] with n hn hll
    unfold scale
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))) hll
  have hlower : ∀ᶠ n : A in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    filter_upwards [hlarge, hweight, hcount, hscalePos]
      with n hn hnweight hncount hsn
    have hn0 : (n : ℕ) ≠ 0 := by omega
    have hF := weightedDivisorCount_le_F_of_prime_power_weights
      hn0 (R n) (w n) (hprime n) (hnweight)
    have hhalf : scale (n : ℕ) / 2 ≤ (F (n : ℕ) : ℝ) := hncount.trans hF
    apply (le_div_iff₀ hsn).2
    simpa [div_eq_mul_inv, mul_comm] using hhalf
  exact tendsto_F_div_scale_on_set hlarge hloglog hlower
    hfSmall.tendsto_div_nhds_zero homega hscale

/- Finite density bridge for the weighted Track-A interface.  The weighted Chebyshev theorem
   supplies a density-one set of integers whose weighted divisor sum is at least `μ/2`; the
   prime-power bridge then transports that set to an equally large set on which `F` itself is at
   least `μ/2`.  This is intentionally parameterized by the analytic moment hypotheses: it is a
   genuine finite consequence of them, not a replacement for the missing prime-power estimate. -/
theorem eventually_weightedDivisorCount_good_F_count_ge_fraction_of_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (μ V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hμ : ∀ᶠ X : ℕ in atTop, 0 < μ X)
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - μ X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X / (μ X ^ 2 * (X : ℝ)))
      atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (1 - η) * (X : ℝ) ≤
        (((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ μ X / 2 ≤ (F n : ℝ))).card : ℝ) := by
  let B : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦ weightedDivisorCount (R X) (w X) n < μ X / 2)
  let G : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter
      (fun n ↦ μ X / 2 ≤ weightedDivisorCount (R X) (w X) n)
  let H : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter (fun n ↦ μ X / 2 ≤ (F n : ℝ))
  have hbad : Tendsto (fun X : ℕ ↦ ((B X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    simpa [B] using
      (tendsto_weightedDivisorCount_exceptionalRatio_zero_of_moment_bounds
        R w μ V hμ hvar hvanish)
  have hbadη : ∀ᶠ X : ℕ in atTop,
      ((B X).card : ℝ) / (X : ℝ) < η :=
    hbad.eventually (eventually_lt_nhds hη)
  have hpartition : ∀ X : ℕ, B X ∪ G X = Finset.Icc 1 X := by
    intro X
    ext n
    by_cases hn : n ∈ Finset.Icc 1 X
    · simp only [B, G, Finset.mem_union, Finset.mem_filter]
      by_cases hlt : weightedDivisorCount (R X) (w X) n < μ X / 2
      · exact iff_of_true (Or.inl ⟨hn, hlt⟩) hn
      · exact iff_of_true (Or.inr ⟨hn, le_of_not_gt hlt⟩) hn
    · simp [B, G, hn]
  have hdisj : ∀ X : ℕ, Disjoint (B X) (G X) := by
    intro X
    rw [Finset.disjoint_left]
    intro n hnB hnG
    exact (not_lt_of_ge (Finset.mem_filter.mp hnG).2)
      (Finset.mem_filter.mp hnB).2
  have hcard : ∀ X : ℕ, ((B X).card : ℝ) + ((G X).card : ℝ) = (X : ℝ) := by
    intro X
    have hnat : (B X).card + (G X).card = X := by
      calc
        (B X).card + (G X).card = (B X ∪ G X).card :=
          (Finset.card_union_of_disjoint (hdisj X)).symm
        _ = (Finset.Icc 1 X).card := by rw [hpartition X]
        _ = X := by
          rw [Nat.card_Icc]
          omega
    exact_mod_cast hnat
  filter_upwards [hbadη, eventually_gt_atTop (0 : ℕ), hweight]
    with X hBX hX hwt
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hBbound : ((B X).card : ℝ) ≤ η * (X : ℝ) := by
    apply (div_le_iff₀ hXreal).mp
    exact hBX.le
  have hGsub : G X ⊆ H X := by
    intro n hn
    have hnG := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnG.1).1
      omega
    have hF := weightedDivisorCount_le_F_of_prime_power_weights
      hn0 (R X) (w X) (hprime X) (by
        intro p hp hpd
        exact hwt n hnG.1 p hp hpd)
    exact Finset.mem_filter.mpr ⟨hnG.1, hnG.2.trans hF⟩
  have hcard_sub : ((G X).card : ℝ) ≤ ((H X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hGsub
  have hGbound : (1 - η) * (X : ℝ) ≤ ((G X).card : ℝ) := by
    have hc := hcard X
    linarith
  exact hGbound.trans hcard_sub

/- Historical standard-scale specialization. Its prefix-uniform weight bound and vanishing
   scale-centered variance cannot hold together; see `not_prefix_prime_power_moment_certificate`
   in `Erdos878.CertificateAudit`. This conditional theorem is not a viable Track-A target. -/
theorem eventually_weightedScale_good_F_count_ge_fraction_of_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (1 - η) * (X : ℝ) ≤
        (((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℝ) := by
  exact eventually_weightedDivisorCount_good_F_count_ge_fraction_of_moment_bounds
    R w scale V hprime hweight eventually_scale_pos hvar hvanish hη

/- The preceding finite estimate is equivalent to convergence of the endpoint good-set ratio to
   one.  The upper bound is purely cardinality-theoretic; the lower bound is the weighted
   Chebyshev estimate with an arbitrary positive loss. -/
theorem tendsto_weightedScale_good_F_ratio_one_of_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let η : ℝ := (1 - a) / 2
    have hη : 0 < η := by
      dsimp [η]
      linarith
    have hgood :=
      eventually_weightedScale_good_F_count_ge_fraction_of_moment_bounds
        R w V hprime hweight hvar hvanish hη
    filter_upwards [hgood, eventually_gt_atTop (0 : ℕ)] with X hXgood hX
    have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
    have hratio : 1 - η ≤
        ((((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℕ) : ℝ) /
          (X : ℝ) := by
      apply (le_div_iff₀ hXreal).2
      simpa [mul_comm] using hXgood
    dsimp [η] at hratio
    linarith
  · intro b hb
    have hupper : ∀ᶠ X : ℕ in atTop,
        ((((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℕ) : ℝ) /
          (X : ℝ) ≤ 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
      have hsub : (Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ)) ⊆ Finset.Icc 1 X :=
        Finset.filter_subset _ _
      have hcardNat : ((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card ≤ X := by
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Icc] at hcard
        omega
      have hcardReal :
          ((((Finset.Icc 1 X).filter
            (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℕ) : ℝ) ≤
            (X : ℝ) := by
        exact_mod_cast hcardNat
      have hdiv := (div_le_iff₀ (by exact_mod_cast hX)).2
        (show ((((Finset.Icc 1 X).filter
          (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))).card : ℕ) : ℝ) ≤
            1 * (X : ℝ) by simpa using hcardReal)
      simpa using hdiv
    filter_upwards [hupper] with X hX
    exact hX.trans_lt hb

/- The pointwise lower-bound failure set associated with the standard Track-A scale. -/
noncomputable def weightedScaleFLowerBadSet : Set ℕ :=
  {n | (F n : ℝ) < scale n / 2}

/- Dyadic-tail specialization of the reciprocal-mass bridge.  Once an analytic normal-order
estimate supplies a lower bound for the dividing mass of a dyadic tail, this theorem sends it
directly to the official `F n` value. -/
theorem real_mul_le_F_of_dyadicPrimeTail_mass_lower
    {n k m : ℕ} (hn : n ≠ 0) {μ : ℝ}
    (hmass : μ ≤
      ∑ p ∈ (dyadicDisjointPrimeTail k m).filter (fun p ↦ p ∣ n), ((p : ℝ)⁻¹)) :
    (n : ℝ) * μ ≤ (F n : ℝ) := by
  apply real_mul_le_F_of_prime_window_mass_lower hn
    (dyadicDisjointPrimeTail k m)
  · intro p hp
    exact dyadicDisjointPrimeTail_prime k m hp
  · exact hmass

/- Finite Track-A bridge: a window `R` contributes one admissible prime-power term for every
   member which divides `n`.  The divisor count from `UnionBound` therefore gives a real-valued
   lower bound for `F`; the only analytic input still needed is a normal-order lower bound for
   `divisorCount R n` and a common lower bound for the selected powers. -/
theorem divisorCount_mul_le_F_of_prime_window
    {n B : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hpower : ∀ p ∈ R, p ∣ n → B ≤ p ^ Nat.log p n) :
    divisorCount R n * (B : ℝ) ≤ (F n : ℝ) := by
  let S : Finset ℕ := R.filter (fun p ↦ p ∣ n)
  have hprimeS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  have hdvdS : ∀ p ∈ S, p ∣ n := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hpowerS : ∀ p ∈ S, B ≤ p ^ Nat.log p n := by
    intro p hp
    exact hpower p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hnat : S.card * B ≤ F n :=
    (card_mul_le_f_of_prime_family hn hprimeS hdvdS hpowerS).trans (f_le_F n hn)
  have hreal : (S.card : ℝ) * (B : ℝ) ≤ (F n : ℝ) := by
    exact_mod_cast hnat
  simpa [S, divisorCount] using hreal

theorem real_mul_le_F_of_divisorCount_lower
    {n B : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hpower : ∀ p ∈ R, p ∣ n → B ≤ p ^ Nat.log p n)
    {C : ℝ} (hC : C ≤ divisorCount R n) :
    C * (B : ℝ) ≤ (F n : ℝ) := by
  have hnonneg : 0 ≤ (B : ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_right hC hnonneg).trans
    (divisorCount_mul_le_F_of_prime_window hn R hprime hpower)

/- The half-mean form is the pointwise output consumed after removing the Chebyshev exceptional
set.  It exposes the exact lower bound that a normal prime window gives to `F(n)`. -/
theorem half_mean_mul_le_F_of_divisorCount_good
    {n B : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hpower : ∀ p ∈ R, p ∣ n → B ≤ p ^ Nat.log p n)
    {μ : ℝ}
    (hgood : μ / 2 ≤ divisorCount R n) :
    (μ / 2) * (B : ℝ) ≤ (F n : ℝ) := by
  exact real_mul_le_F_of_divisorCount_lower hn R hprime hpower hgood

/- The official first question only asks for a positive constant in
   `F(n) ≫ n log log n`; it does not require the sharp coefficient `1/2`.
   Keeping the multiplier `κ` abstract lets the analytic window argument use a
   deliberately wider approximation tolerance (and hence a larger fixed loss)
   without changing any finite `F` bookkeeping. -/
theorem scaled_mean_mul_le_F_of_divisorCount_good
    {n B : ℕ} (hn : n ≠ 0) (R : Finset ℕ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hpower : ∀ p ∈ R, p ∣ n → B ≤ p ^ Nat.log p n)
    {μ κ : ℝ} (hgood : κ * μ ≤ divisorCount R n) :
    (κ * μ) * (B : ℝ) ≤ (F n : ℝ) := by
  exact real_mul_le_F_of_divisorCount_lower hn R hprime hpower hgood

/- The two-window complement is the intersection of the two good sets.  This small wrapper keeps
   the density bookkeeping separate from the pointwise `F` bridge: once both Chebyshev inequalities
   hold, each window's half-mean lower bound is available simultaneously. -/
theorem half_mean_mul_le_F_of_two_divisorCount_good
    {n B₁ B₂ : ℕ} (hn : n ≠ 0)
    (R₁ R₂ : Finset ℕ)
    (hprime₁ : ∀ p ∈ R₁, p.Prime)
    (hprime₂ : ∀ p ∈ R₂, p.Prime)
    (hpower₁ : ∀ p ∈ R₁, p ∣ n → B₁ ≤ p ^ Nat.log p n)
    (hpower₂ : ∀ p ∈ R₂, p ∣ n → B₂ ≤ p ^ Nat.log p n)
    {μ₁ μ₂ : ℝ}
    (hgood₁ : μ₁ / 2 ≤ divisorCount R₁ n)
    (hgood₂ : μ₂ / 2 ≤ divisorCount R₂ n) :
    ((μ₁ / 2) * (B₁ : ℝ) ≤ (F n : ℝ)) ∧
      ((μ₂ / 2) * (B₂ : ℝ) ≤ (F n : ℝ)) := by
  exact ⟨half_mean_mul_le_F_of_divisorCount_good hn R₁ hprime₁ hpower₁ hgood₁,
    half_mean_mul_le_F_of_divisorCount_good hn R₂ hprime₂ hpower₂ hgood₂⟩

/-- Every value below `x` is bounded by the corresponding finite maximum. -/
theorem f_le_maxUpTo {n x : ℕ} (hnx : n ≤ x) : f n ≤ maxUpTo f x := by
  exact Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_of_le hnx))

/- A real-valued maximum adapter.  Pointwise estimates for `g n` often arise naturally after
normalizing by `n`; this lemma lets those estimates be applied to the finite natural maximum
without introducing a floor or an artificial integer rounding constant. -/
theorem maxUpTo_le_of_pointwise_real
    (g : ℕ → ℕ) (X : ℕ) (B : ℝ)
    (hpoint : ∀ n ≤ X, (g n : ℝ) ≤ B) :
    (maxUpTo g X : ℝ) ≤ B := by
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (X + 1))
    ⟨0, by simp⟩ g
  have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hcast : (maxUpTo g X : ℝ) = (g n : ℝ) := by
    simpa [maxUpTo] using congrArg (fun z : ℕ ↦ (z : ℝ)) heq
  rw [hcast]
  exact hpoint n hnX

/- Ratio-normalized variant used by Track C.  It keeps the pointwise estimate in the natural
`f(n)/n` form, and adds only the monotonicity needed to pass from varying endpoints to `X`. -/
theorem maxUpTo_f_le_of_pointwise_ratio
    (X : ℕ) (φ : ℕ → ℝ) (hφX : 0 ≤ φ X)
    (hφmono : ∀ n ≤ X, φ n ≤ φ X)
    (hpoint : ∀ n ≤ X, n ≠ 0 →
      (f n : ℝ) / (n : ℝ) ≤ φ n) :
    (maxUpTo f X : ℝ) ≤ (X : ℝ) * φ X := by
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (X + 1))
    ⟨0, by simp⟩ f
  have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hcast : (maxUpTo f X : ℝ) = (f n : ℝ) := by
    simpa [maxUpTo] using congrArg (fun z : ℕ ↦ (z : ℝ)) heq
  rw [hcast]
  by_cases hn0 : n = 0
  · subst n
    simp [f]
    exact mul_nonneg (by positivity) hφX
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hratio := hpoint n hnX hn0
    have hfn : (f n : ℝ) ≤ (n : ℝ) * φ n := by
      simpa [mul_comm] using (div_le_iff₀ hnR).mp hratio
    have hφn := hφmono n hnX
    calc
      (f n : ℝ) ≤ (n : ℝ) * φ n := hfn
      _ ≤ (n : ℝ) * φ X :=
        mul_le_mul_of_nonneg_left hφn (by positivity)
      _ ≤ (X : ℝ) * φ X := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnX) hφX

/-- The lower-bound construction packaged in the form needed for the maximal-order target. -/
theorem card_mul_le_maxUpTo_of_prime_family
    {n x B : ℕ} {S : Finset ℕ} (hn : n ≠ 0) (hnx : n ≤ x)
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n)
    (hlower : ∀ p ∈ S, B ≤ p ^ Nat.log p n) :
    S.card * B ≤ maxUpTo f x :=
  (card_mul_le_f_of_prime_family hn hprime hdvd hlower).trans (f_le_maxUpTo hnx)

/- Sum-valued companion for Track B.  It preserves the individual prime-power sizes instead of
   replacing them by a common minimum, which is the natural interface for a rotation argument
   producing slightly different approximation errors for different primes. -/
theorem sum_primePower_le_maxUpTo_f_of_prime_family
    {n x : ℕ} (hn : n ≠ 0) (hnx : n ≤ x) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ n) :
    (∑ p ∈ S, p ^ Nat.log p n) ≤ maxUpTo f x := by
  have hsubset : S ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, hn⟩
  have hsum : (∑ p ∈ S, p ^ Nat.log p n) ≤ f n := by
    unfold f
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
  exact hsum.trans (f_le_maxUpTo hnx)

/-- Product of a finite set of candidate prime divisors. -/
noncomputable def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- The largest multiple of `primeProduct S` not exceeding `X`. -/
noncomputable def multipleBelow (X : ℕ) (S : Finset ℕ) : ℕ :=
  primeProduct S * (X / primeProduct S)

theorem primeProduct_pos {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) :
    0 < primeProduct S := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos

theorem primeProduct_le_pow_card {S : Finset ℕ} {P : ℕ}
    (hP : ∀ p ∈ S, p ≤ P) : primeProduct S ≤ P ^ S.card := by
  unfold primeProduct
  exact Finset.prod_le_pow_card S id P hP

theorem multipleBelow_le (X : ℕ) (S : Finset ℕ) : multipleBelow X S ≤ X := by
  unfold multipleBelow
  simpa [Nat.mul_comm] using Nat.div_mul_le_self X (primeProduct S)

/-- The chosen multiple misses `X` by strictly less than one copy of the prime product. -/
theorem multipleBelow_add_primeProduct_gt (X : ℕ) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    X < multipleBelow X S + primeProduct S := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hmod : X % primeProduct S < primeProduct S := Nat.mod_lt X hprodPos
  have hdecomp := Nat.mod_add_div X (primeProduct S)
  unfold multipleBelow
  omega

/-- Complete elementary lower-bound construction for Track B. Once the analytic prime-selection
lemma supplies a prime set with product at most `X` and large powers below `multipleBelow X S`,
this theorem places all contributions into one `n ≤ X` and hence into the finite maximum. -/
theorem card_mul_le_maxUpTo_of_selected_primes
    {X B : ℕ} {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime)
    (hprod : primeProduct S ≤ X)
    (hlower : ∀ p ∈ S, B ≤ p ^ Nat.log p (multipleBelow X S)) :
    S.card * B ≤ maxUpTo f X := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hquotPos : 0 < X / primeProduct S := Nat.div_pos hprod hprodPos
  apply card_mul_le_maxUpTo_of_prime_family
      (Nat.mul_ne_zero hprodPos.ne' hquotPos.ne') (multipleBelow_le X S) hprime
  · intro p hp
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hp) _
  · exact hlower

/- Sum-valued packed-multiple specialization. -/
theorem sum_primePower_le_maxUpTo_f_of_selected_primes
    {X : ℕ} (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hprod : primeProduct S ≤ X) :
    (∑ p ∈ S, p ^ Nat.log p (multipleBelow X S)) ≤ maxUpTo f X := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hquotPos : 0 < X / primeProduct S := Nat.div_pos hprod hprodPos
  have hn : multipleBelow X S ≠ 0 := by
    unfold multipleBelow
    exact Nat.mul_ne_zero hprodPos.ne' hquotPos.ne'
  have hdvd : ∀ p ∈ S, p ∣ multipleBelow X S := by
    intro p hp
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hp) _
  exact sum_primePower_le_maxUpTo_f_of_prime_family hn
    (multipleBelow_le X S) hprime hdvd

/- Weighted companion for the same packed multiple.  It keeps the reciprocal mass of the selected
prime set and therefore gives a stronger analytic interface than `S.card * B`. -/
theorem reciprocalPrimeMass_mul_le_maxUpTo_f_of_selected_primes
    {X : ℕ} (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hprod : primeProduct S ≤ X) :
    (multipleBelow X S : ℝ) * ∑ p ∈ S, ((p : ℝ)⁻¹) ≤
      (maxUpTo f X : ℝ) := by
  have hprodPos : 0 < primeProduct S := primeProduct_pos hprime
  have hquotPos : 0 < X / primeProduct S := Nat.div_pos hprod hprodPos
  have hn : multipleBelow X S ≠ 0 := by
    unfold multipleBelow
    exact Nat.mul_ne_zero hprodPos.ne' hquotPos.ne'
  have hdvd : ∀ p ∈ S, p ∣ multipleBelow X S := by
    intro p hp
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hp) _
  have hF := reciprocalPrimeMass_mul_le_f_of_prime_family
    hn S hprime hdvd
  have hmax := f_le_maxUpTo (n := multipleBelow X S) (x := X)
    (multipleBelow_le X S)
  have hreal : (f (multipleBelow X S) : ℝ) ≤ (maxUpTo f X : ℝ) := by
    exact_mod_cast hmax
  exact hF.trans hreal

/- The remaining analytic input can be stated directly in terms of a finite prime family.
For each large `X`, the family `S` is packed into `multipleBelow X S`; the hypotheses below
are exactly the primality/product/power checks consumed by `card_mul_le_maxUpTo_of_selected_primes`,
plus the numerical estimate that its cardinality times the common power already has the desired
normalized size.  This theorem is fully formalized and leaves only the number-theoretic selection
lemma to be supplied by the proof of the second question. -/
theorem eventually_maxUpTo_f_ratio_ge_one_sub_of_selected_primes
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ) (B : ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        (∀ p ∈ S, B ≤ p ^ Nat.log p (multipleBelow X S)) ∧
        1 - ε ≤ ((S.card : ℝ) * (B : ℝ)) / maximalOrderScale X) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop,
        1 - ε ≤ (maxUpTo f X : ℝ) / maximalOrderScale X := by
  intro ε hε
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscalePos : ∀ᶠ X : ℕ in atTop, 0 < maximalOrderScale X := by
    filter_upwards [hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with X hlog
    have hx : 1 < (X : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlog)
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlog))
      (Real.log_pos hlog)
  filter_upwards [hselect ε hε, hscalePos] with X hdata hscale
  rcases hdata with ⟨S, B, hprime, hprod, hpower, hnormalized⟩
  have hnat : S.card * B ≤ maxUpTo f X :=
    card_mul_le_maxUpTo_of_selected_primes hprime hprod hpower
  have hreal : (S.card : ℝ) * (B : ℝ) ≤ (maxUpTo f X : ℝ) := by
    exact_mod_cast hnat
  have hquot :
      ((S.card : ℝ) * (B : ℝ)) / maximalOrderScale X ≤
        (maxUpTo f X : ℝ) / maximalOrderScale X :=
    div_le_div_of_nonneg_right hreal (le_of_lt hscale)
  exact hnormalized.trans hquot

/- More flexible Track-B lower interface using the full prime-power sum.  It is strictly weaker
   than the common-threshold hypothesis above and is the form directly suggested by the rotation
   construction, where different primes can land at different points in the product band. -/
theorem eventually_maxUpTo_f_ratio_ge_one_sub_of_selected_prime_power_sums
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
            maximalOrderScale X) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop,
        1 - ε ≤ (maxUpTo f X : ℝ) / maximalOrderScale X := by
  intro ε hε
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscalePos : ∀ᶠ X : ℕ in atTop, 0 < maximalOrderScale X := by
    filter_upwards [hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with X hlog
    have hx : 1 < (X : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlog)
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlog))
      (Real.log_pos hlog)
  filter_upwards [hselect ε hε, hscalePos] with X hdata hscale
  rcases hdata with ⟨S, hprime, hprod, hnormalized⟩
  have hnat :
      (∑ p ∈ S, p ^ Nat.log p (multipleBelow X S)) ≤ maxUpTo f X :=
    sum_primePower_le_maxUpTo_f_of_selected_primes S hprime hprod
  have hreal :
      (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) ≤
        (maxUpTo f X : ℝ) := by
    exact_mod_cast hnat
  have hquot :
      (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
          maximalOrderScale X ≤
        (maxUpTo f X : ℝ) / maximalOrderScale X :=
    div_le_div_of_nonneg_right hreal (le_of_lt hscale)
  exact hnormalized.trans hquot

/- Ordinary maximal-order squeeze using the sum-valued selection data. -/
theorem tendsto_maximalOrder_of_selected_prime_power_sums
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
            maximalOrderScale X) :
    Tendsto (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) atTop (𝓝 1) := by
  apply tendsto_maximalOrder_of_eventually_one_sub_le
  exact eventually_maxUpTo_f_ratio_ge_one_sub_of_selected_prime_power_sums hselect

/- The source paper also records a weaker, sequence-level maximal-order statement.  The same
   finite interface proves it once the prime-selection certificate is supplied only along a
   sequence `Xseq k` tending to infinity.  This keeps the distinction between an ordinary
   all-`X` asymptotic and the easier subsequence result explicit in the Lean API. -/
theorem tendsto_maximalOrder_of_selected_prime_power_sums_along
    (Xseq : ℕ → ℕ) (hXseq : Tendsto Xseq atTop atTop)
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ Xseq k ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow (Xseq k) S) : ℕ) : ℝ)) /
            maximalOrderScale (Xseq k)) :
    Tendsto (fun k : ℕ ↦
      (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k)) atTop (𝓝 1) := by
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscalePosX : ∀ᶠ X : ℕ in atTop, 0 < maximalOrderScale X := by
    filter_upwards [hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with X hlog
    have hx : 1 < (X : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlog)
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlog))
      (Real.log_pos hlog)
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ := (1 - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hscaleSeq : ∀ᶠ k : ℕ in atTop, 0 < maximalOrderScale (Xseq k) :=
      hXseq.eventually hscalePosX
    filter_upwards [hselect ε hε, hscaleSeq] with k hdata hscale
    rcases hdata with ⟨S, hprime, hprod, hnormalized⟩
    have hnat :
        (∑ p ∈ S, p ^ Nat.log p (multipleBelow (Xseq k) S)) ≤
          maxUpTo f (Xseq k) :=
      sum_primePower_le_maxUpTo_f_of_selected_primes S hprime hprod
    have hreal :
        (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow (Xseq k) S) : ℕ) : ℝ)) ≤
          (maxUpTo f (Xseq k) : ℝ) := by
      exact_mod_cast hnat
    have hquot :
        (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow (Xseq k) S) : ℕ) : ℝ)) /
            maximalOrderScale (Xseq k) ≤
          (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k) :=
      div_le_div_of_nonneg_right hreal (le_of_lt hscale)
    have hratio :
        1 - ε ≤ (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k) :=
      hnormalized.trans hquot
    dsimp [ε] at hratio
    linarith
  · intro b hb
    let ε : ℝ := (b - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hupperX := eventually_maxUpTo_f_ratio_le_one_add ε hε
    have hupperSeq : ∀ᶠ k : ℕ in atTop,
        (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k) ≤ 1 + ε :=
      hXseq.eventually hupperX
    filter_upwards [hupperSeq] with k hk
    dsimp [ε] at hk
    linarith

/- The sequence-level theorem also gives a genuine global `limsup` lower bound.  This is the
   order-theoretic formulation closest to the source paper's known subsequence result: a sequence
   tending to infinity cannot have a limiting value above the full-endpoint limsup. -/
theorem le_limsup_maxUpTo_ratio_of_selected_prime_power_sums_along
    (Xseq : ℕ → ℕ) (hXseq : Tendsto Xseq atTop atTop)
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ Xseq k ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow (Xseq k) S) : ℕ) : ℝ)) /
            maximalOrderScale (Xseq k)) :
    1 ≤ limsup (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) atTop := by
  have hseqT := tendsto_maximalOrder_of_selected_prime_power_sums_along Xseq hXseq hselect
  have hfullBound : atTop.IsBoundedUnder (· ≤ ·) (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) := by
    refine ⟨2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [eventually_maxUpTo_f_ratio_le_one_add (1 : ℝ) one_pos] with X hX
    norm_num at hX ⊢
    exact hX
  have hcomp : limsup ((fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) ∘ Xseq) atTop ≤
      limsup (fun X : ℕ ↦
        (maxUpTo f X : ℝ) / maximalOrderScale X) atTop := by
    exact hXseq.limsup_comp_le_limsup
      (hvf := by
        simpa only [Filter.IsCoboundedUnder, Filter.map_map, Function.comp_def] using
          hseqT.isCoboundedUnder_le)
      (hg := hfullBound)
  have hseqLimsup : limsup ((fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) ∘ Xseq) atTop = 1 := by
    simpa [Function.comp_def] using hseqT.limsup_eq
  rw [← hseqLimsup]
  exact hcomp

/- A subsequence-to-all-endpoints interpolation lemma.  It isolates the exact extra input needed
   to upgrade Erdős's sequence-level maximal-order estimate: every sufficiently large endpoint must
   lie above a sufficiently late selected endpoint, while the normalizing scale changes by at most
   a prescribed multiplicative factor.  The proof uses only monotonicity of the finite maximum and
   positivity of the scale; all prime selection remains in the preceding theorem. -/
theorem tendsto_maxUpTo_ratio_of_mesh_subsequence
    {g : ℕ → ℕ} {s : ℕ → ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop, (maxUpTo g x : ℝ) / s x ≤ 1 + ε)
    (Xseq : ℕ → ℕ)
    (hseq : Tendsto (fun k : ℕ ↦
      (maxUpTo g (Xseq k) : ℝ) / s (Xseq k)) atTop (𝓝 1))
    (hseqpos : ∀ᶠ k : ℕ in atTop, 0 < s (Xseq k))
    (hspos : ∀ᶠ x : ℕ in atTop, 0 < s x)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
      ∃ k : ℕ, K ≤ k ∧ Xseq k ≤ x ∧ s x ≤ (1 + ε) * s (Xseq k)) :
    Tendsto (fun x : ℕ ↦ (maxUpTo g x : ℝ) / s x) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ := (1 - a) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let δ : ℝ := ε / (2 + ε)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδlt : δ < 1 := by
      dsimp [δ]
      have hden : 0 < 2 + ε := by linarith
      apply (div_lt_iff₀ hden).2
      linarith
    have hseqLower : ∀ᶠ k : ℕ in atTop,
        1 - δ ≤ (maxUpTo g (Xseq k) : ℝ) / s (Xseq k) := by
      have hlt : 1 - δ < (1 : ℝ) := by linarith
      have hraw := (tendsto_order.1 hseq).1 (1 - δ) hlt
      filter_upwards [hraw] with k hk
      exact hk.le
    have hseqGood : ∀ᶠ k : ℕ in atTop,
        (1 - δ ≤ (maxUpTo g (Xseq k) : ℝ) / s (Xseq k)) ∧
          0 < s (Xseq k) := hseqLower.and hseqpos
    rcases (eventually_atTop.1 hseqGood) with ⟨K, hK⟩
    have hmesh' := hmesh δ hδ K
    filter_upwards [hmesh', hspos] with x hx hxs
    rcases hx with ⟨k, hkK, hkx, hscale⟩
    have hkGood := hK k hkK
    have hkLower := hkGood.1
    have hkspos := hkGood.2
    have hmaxNat : maxUpTo g (Xseq k) ≤ maxUpTo g x :=
      maxUpTo_mono hkx
    have hmaxReal : (maxUpTo g (Xseq k) : ℝ) ≤ (maxUpTo g x : ℝ) := by
      exact_mod_cast hmaxNat
    have hmulLower : (1 - δ) * s (Xseq k) ≤ (maxUpTo g (Xseq k) : ℝ) :=
      (le_div_iff₀ hkspos).mp hkLower
    have hmulMax : (1 - δ) * s (Xseq k) ≤ (maxUpTo g x : ℝ) :=
      hmulLower.trans hmaxReal
    by_cases hε1 : ε ≤ 1
    · have hcoef : (1 - ε) * (1 + δ) ≤ 1 - δ := by
        dsimp [δ]
        have hden : 0 < 2 + ε := by linarith
        field_simp
        nlinarith [sq_nonneg ε]
      have hscale' := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ 1 - ε)
      have hcoef' := mul_le_mul_of_nonneg_right hcoef
        (by positivity : 0 ≤ s (Xseq k))
      have htarget : (1 - ε) * s x ≤ (maxUpTo g x : ℝ) := by
        calc
          (1 - ε) * s x ≤ (1 - ε) * ((1 + δ) * s (Xseq k)) := hscale'
          _ = ((1 - ε) * (1 + δ)) * s (Xseq k) := by ring
          _ ≤ (1 - δ) * s (Xseq k) := hcoef'
          _ ≤ (maxUpTo g x : ℝ) := hmulMax
      have hratio : 1 - ε ≤ (maxUpTo g x : ℝ) / s x :=
        (le_div_iff₀ hxs).2 (by simpa [mul_comm] using htarget)
      have haε : a < 1 - ε := by
        dsimp [ε]
        linarith
      exact haε.trans_le hratio
    · have hratio_nonneg : 0 ≤ (maxUpTo g x : ℝ) / s x := by
        exact div_nonneg (by positivity) hxs.le
      have htarget : a < (1 : ℝ) - ε := by
        dsimp [ε]
        linarith
      exact htarget.trans_le ((by linarith : 1 - ε ≤ 0).trans hratio_nonneg)
  · intro b hb
    let ε : ℝ := (b - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    filter_upwards [hupper ε hε] with x hx
    dsimp [ε] at hx
    linarith

/- A more concrete adapter for the preceding interpolation lemma.  Instead of supplying the scale
   comparison as a separate existential, it is enough to give an eventual monotonicity certificate
   for `s`, a cover by consecutive selected endpoints, and the adjacent scale-ratio limit.  This is
   the form a dense prime-selection construction can target directly. -/
theorem tendsto_maxUpTo_ratio_of_subsequence_cover
    {g : ℕ → ℕ} {s : ℕ → ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop, (maxUpTo g x : ℝ) / s x ≤ 1 + ε)
    (Xseq : ℕ → ℕ)
    (hseq : Tendsto (fun k : ℕ ↦
      (maxUpTo g (Xseq k) : ℝ) / s (Xseq k)) atTop (𝓝 1))
    (hseqpos : ∀ᶠ k : ℕ in atTop, 0 < s (Xseq k))
    (hspos : ∀ᶠ x : ℕ in atTop, 0 < s x)
    (hscale_mono : ∀ᶠ x : ℕ in atTop,
      ∀ ⦃y z : ℕ⦄, x ≤ y → y ≤ z → s y ≤ s z)
    (hcover : ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
      ∃ k : ℕ, K ≤ k ∧ Xseq k ≤ x ∧ x ≤ Xseq (k + 1))
    (hscale_ratio : Tendsto (fun k : ℕ ↦
      s (Xseq (k + 1)) / s (Xseq k)) atTop (𝓝 1)) :
    Tendsto (fun x : ℕ ↦ (maxUpTo g x : ℝ) / s x) atTop (𝓝 1) := by
  apply tendsto_maxUpTo_ratio_of_mesh_subsequence hupper Xseq hseq hseqpos hspos
  intro ε hε K
  have hratioUpper : ∀ᶠ k : ℕ in atTop,
      s (Xseq (k + 1)) / s (Xseq k) ≤ 1 + ε := by
    have hlt : (1 : ℝ) < 1 + ε := by linarith
    have hraw := (tendsto_order.1 hscale_ratio).2 (1 + ε) hlt
    filter_upwards [hraw] with k hk
    exact hk.le
  have hgood : ∀ᶠ k : ℕ in atTop,
      (s (Xseq (k + 1)) / s (Xseq k) ≤ 1 + ε) ∧ 0 < s (Xseq k) :=
    hratioUpper.and hseqpos
  rcases (eventually_atTop.1 hgood) with ⟨K', hK'⟩
  let K'' := max K K'
  have hcover' := hcover K''
  filter_upwards [hcover', hspos, hscale_mono] with x hx hxs hmono
  rcases hx with ⟨k, hk, hkx, hxnext⟩
  have hkK : K' ≤ k := le_trans (le_max_right K K') hk
  have hkGood := hK' k hkK
  have hnext : s (Xseq (k + 1)) ≤ (1 + ε) * s (Xseq k) := by
    exact (div_le_iff₀ hkGood.2).mp hkGood.1
  have hbetween : s x ≤ s (Xseq (k + 1)) :=
    hmono (y := x) (z := Xseq (k + 1)) (le_refl _) hxnext
  have hkK0 : K ≤ k := by
    dsimp [K''] at hk
    exact le_trans (le_max_left K K') hk
  exact ⟨k, hkK0, hkx,
    hbetween.trans hnext⟩

/- The subsequence-cover mechanism also accepts the source's already-proved sequence asymptotic
   directly.  This is useful when importing Erdős's known sequence-level theorem: the only new
   analytic work needed for an all-endpoint limit is then the endpoint cover and the elementary
   endpoint-ratio condition. -/
theorem tendsto_maximalOrder_of_subsequence_limit_and_subsequence_cover
    (Xseq : ℕ → ℕ) (hXseq : Tendsto Xseq atTop atTop)
    (hseq : Tendsto (fun k : ℕ ↦
      (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k)) atTop (𝓝 1))
    (hcover : ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
      ∃ k : ℕ, K ≤ k ∧ Xseq k ≤ x ∧ x ≤ Xseq (k + 1))
    (hendpoint_ratio : Tendsto (fun k : ℕ ↦
      (Xseq (k + 1) : ℝ) / (Xseq k : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) atTop (𝓝 1) := by
  have hseqpos : ∀ᶠ k : ℕ in atTop, 0 < maximalOrderScale (Xseq k) :=
    hXseq.eventually eventually_maximalOrderScale_pos
  have hspos : ∀ᶠ X : ℕ in atTop, 0 < maximalOrderScale X :=
    eventually_maximalOrderScale_pos
  apply tendsto_maxUpTo_ratio_of_subsequence_cover
    (g := f) (s := maximalOrderScale) (Xseq := Xseq)
  · intro ε hε
    exact eventually_maxUpTo_f_ratio_le_one_add ε hε
  · exact hseq
  · exact hseqpos
  · exact hspos
  · exact eventually_maximalOrderScale_mono
  · exact hcover
  · exact tendsto_maximalOrderScale_ratio_of_tendsto_endpoint_ratio
      Xseq hXseq hendpoint_ratio

/- Public Track-B adapter: the sequence-level prime-power selection theorem and the generic
   endpoint-cover interpolation are composed in one call.  An analytic construction may therefore
   work only on selected endpoints; it must additionally supply only the endpoint cover and the
   adjacent endpoint-ratio comparison below, since scale monotonicity and the induced scale-ratio
   limit are proved unconditionally above. -/
theorem tendsto_maximalOrder_of_selected_prime_power_sums_and_subsequence_cover
    (Xseq : ℕ → ℕ) (hXseq : Tendsto Xseq atTop atTop)
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ Xseq k ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow (Xseq k) S) : ℕ) : ℝ)) /
            maximalOrderScale (Xseq k))
    (hcover : ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
      ∃ k : ℕ, K ≤ k ∧ Xseq k ≤ x ∧ x ≤ Xseq (k + 1))
    (hendpoint_ratio : Tendsto (fun k : ℕ ↦
      (Xseq (k + 1) : ℝ) / (Xseq k : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) atTop (𝓝 1) := by
  have hseq := tendsto_maximalOrder_of_selected_prime_power_sums_along
    Xseq hXseq hselect
  exact tendsto_maximalOrder_of_subsequence_limit_and_subsequence_cover
    Xseq hXseq hseq hcover hendpoint_ratio

/- Once the analytic prime-selection hypothesis is supplied, the ordinary maximal-order limit is
completely formal: the selected-prime lower interface above is fed into the already proved squeeze
against the uniform omega upper bound. -/
theorem tendsto_maximalOrder_of_selected_primes
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ) (B : ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        (∀ p ∈ S, B ≤ p ^ Nat.log p (multipleBelow X S)) ∧
        1 - ε ≤ ((S.card : ℝ) * (B : ℝ)) / maximalOrderScale X) :
    Tendsto (fun X : ℕ ↦
      (maxUpTo f X : ℝ) / maximalOrderScale X) atTop (𝓝 1) := by
  apply tendsto_maximalOrder_of_eventually_one_sub_le
  exact eventually_maxUpTo_f_ratio_ge_one_sub_of_selected_primes hselect

/- A finite sanity check from the official discussion: the equality of the two maxima
is reported to fail at `x = 210`.  We record the constructive `F`-side lower half here;
the exact finite upper computation for `max f` is deliberately kept separate because it
requires a verified finite evaluator rather than an asymptotic argument. -/
theorem F_210_ge_442 : 442 ≤ F 210 := by
  let A : Finset ℕ := {125, 128, 189}
  have hA : IsAdmissible 210 A := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> norm_num
    · intro a ha b hb hab
      simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl
      all_goals first | contradiction | norm_num [Nat.Coprime]
    · intro a ha p pp hpa
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · have hpow : p ∣ 5 ^ 3 := by
          norm_num
          exact hpa
        have hp5 : p ∣ 5 := pp.dvd_of_dvd_pow hpow
        have hpeq : p = 5 :=
          (Nat.prime_dvd_prime_iff_eq pp (by norm_num : Nat.Prime 5)).mp hp5
        subst p
        norm_num
      · have hpow : p ∣ 2 ^ 7 := by
          norm_num
          exact hpa
        have hp2 : p ∣ 2 := pp.dvd_of_dvd_pow hpow
        have hpeq : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq pp (by norm_num : Nat.Prime 2)).mp hp2
        subst p
        norm_num
      · have hprod : p ∣ 3 ^ 3 * 7 := by
          norm_num
          exact hpa
        rcases pp.dvd_mul.mp hprod with h3 | h7
        · have hp3 : p ∣ 3 := pp.dvd_of_dvd_pow h3
          have hpeq : p = 3 :=
            (Nat.prime_dvd_prime_iff_eq pp (by norm_num : Nat.Prime 3)).mp hp3
          subst p
          norm_num
        · have hpeq : p = 7 :=
            (Nat.prime_dvd_prime_iff_eq pp (by norm_num : Nat.Prime 7)).mp h7
          subst p
          norm_num
  have hsum : (∑ a ∈ A, a) = 442 := by
    norm_num [A]
  rw [← hsum]
  exact sum_le_F_of_admissible hA

/-- A finite evaluator confirms that the source function never reaches the displayed `F`-value
at the counterexample scale `210`.  Keeping this as a standalone theorem avoids using the
counterexample as an unverified comment in the FC-like file. -/
theorem maxUpTo_f_210_le_442 : maxUpTo f 210 ≤ 442 := by
  unfold maxUpTo
  apply Finset.sup_le
  intro b hb
  have hb'' : b < 211 := Finset.mem_range.mp hb
  have hb' : b ≤ 210 := by omega
  interval_cases b <;> norm_num [f, Nat.primeFactors, Nat.primeFactorsList]

/-- The exact finite value reported in the official discussion: `max_{n ≤ 210} f(n) = 383`.
This is a bounded computation, independent of the asymptotic proof targets. -/
theorem maxUpTo_f_210_eq_383 : maxUpTo f 210 = 383 := by
  apply Nat.le_antisymm
  · unfold maxUpTo
    apply Finset.sup_le
    intro b hb
    have hb'' : b < 211 := Finset.mem_range.mp hb
    have hb' : b ≤ 210 := by omega
    interval_cases b <;> norm_num [f, Nat.primeFactors, Nat.primeFactorsList]
  · have hvalue : f 210 = 383 := by
      norm_num [f, Nat.primeFactors, Nat.primeFactorsList]
    rw [← hvalue]
    unfold maxUpTo
    apply Finset.le_sup
    simp

/-- The universal equality of the two maxima is refuted by the explicit counterexample `x = 210`.
This is the fully proved answer to the first alternative in the source page's part (iii). -/
theorem maxUpTo_f_ne_maxUpTo_F_at_210 : maxUpTo f 210 ≠ maxUpTo F 210 := by
  intro heq
  have hF : 442 ≤ maxUpTo F 210 := by
    calc
      442 ≤ F 210 := F_210_ge_442
      _ ≤ maxUpTo F 210 := by
        unfold maxUpTo
        apply Finset.le_sup
        simp
  have hf := maxUpTo_f_210_eq_383.le
  omega

/- The same finite counterexample can be recorded with the useful strict order, not merely
   disequality: the source maximum is exactly 383 while the explicit admissible family already
   gives an `F`-value of 442. -/
theorem maxUpTo_f_lt_maxUpTo_F_at_210 : maxUpTo f 210 < maxUpTo F 210 := by
  have hf : maxUpTo f 210 ≤ 383 := maxUpTo_f_210_eq_383.le
  have hF : 442 ≤ maxUpTo F 210 := by
    calc
      442 ≤ F 210 := F_210_ge_442
      _ ≤ maxUpTo F 210 := by
        unfold maxUpTo
        apply Finset.le_sup
        simp
  omega

/- The density bookkeeping needed by Track A is independent of the number-theoretic estimates:
the complement of a natural-density-zero exceptional set has density one. -/
theorem compl_hasDensity_one_of_hasDensity_zero
    {S : Set ℕ} (hS : S.HasDensity 0) : Sᶜ.HasDensity 1 := by
  rw [Set.HasDensity] at hS ⊢
  simp only [Set.partialDensity]
  have hcard : ∀ᶠ n : ℕ in atTop,
      0 < (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp [hn]
  have hcomp : ∀ᶠ n : ℕ in atTop,
      (((Sᶜ ∩ Set.Iio n).ncard : ℕ) : ℝ) +
        (((S ∩ Set.Iio n).ncard : ℕ) : ℝ) =
      (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ) := by
    filter_upwards [] with n
    have hdisj : Disjoint (Sᶜ ∩ Set.Iio n) (S ∩ Set.Iio n) := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact hx.1 hy.1
    have hunion : (Sᶜ ∩ Set.Iio n) ∪ (S ∩ Set.Iio n) = Set.univ ∩ Set.Iio n := by
      ext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [← hunion, Set.ncard_union_eq hdisj]
    norm_num
  have hratio : Tendsto (fun n : ℕ ↦
      (((S ∩ Set.Iio n).ncard : ℕ) : ℝ) /
        (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Set.partialDensity] using hS
  have hcompRatio : ∀ᶠ n : ℕ in atTop,
      (((Sᶜ ∩ Set.Iio n).ncard : ℕ) : ℝ) /
        (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ) =
      1 - ((((S ∩ Set.Iio n).ncard : ℕ) : ℝ) /
        (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ)) := by
    filter_upwards [hcard, hcomp] with n hn hcn
    field_simp
    linarith
  have hsub : Tendsto (fun n : ℕ ↦
      1 - ((((S ∩ Set.Iio n).ncard : ℕ) : ℝ) /
        (((Set.univ ∩ Set.Iio n).ncard : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hratio)
  apply hsub.congr'
  filter_upwards [hcompRatio] with n hn
  simpa [Set.inter_univ, Set.inter_assoc] using hn.symm

/- The elementary density identities used when two independently constructed good sets have to
   be combined.  The density package supplies the complement direction (zero implies one); the
   converse and finite-union closure are proved here by explicit ncard bookkeeping. -/
theorem tendsto_Iio_ncard_div_nat_one : Tendsto (fun n : ℕ ↦
    (((Set.Iio n).ncard : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  refine (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [Nat.ncard_Iio]
  exact (div_self (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℝ) ≠ 0)).symm

theorem hasDensity_zero_of_hasDensity_one_compl
    {A : Set ℕ} (hA : A.HasDensity 1) : Aᶜ.HasDensity 0 := by
  rw [Set.HasDensity] at hA ⊢
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hA ⊢
  have hdiff : Tendsto (fun n : ℕ ↦
      (((Set.Iio n).ncard : ℕ) : ℝ) / (n : ℝ) -
        (((A ∩ Set.Iio n).ncard : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_Iio_ncard_div_nat_one.sub hA
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hdisj : Disjoint (Aᶜ ∩ Set.Iio n) (A ∩ Set.Iio n) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact hx.1 hy.1
  have hunion : (Aᶜ ∩ Set.Iio n) ∪ (A ∩ Set.Iio n) = Set.Iio n := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hcard : (Aᶜ ∩ Set.Iio n).ncard + (A ∩ Set.Iio n).ncard =
      (Set.Iio n).ncard := by
    calc
      (Aᶜ ∩ Set.Iio n).ncard + (A ∩ Set.Iio n).ncard =
          ((Aᶜ ∩ Set.Iio n) ∪ (A ∩ Set.Iio n)).ncard :=
        (Set.ncard_union_eq hdisj).symm
      _ = (Set.Iio n).ncard := by rw [hunion]
  have hcardR : (((Aᶜ ∩ Set.Iio n).ncard : ℕ) : ℝ) +
      (((A ∩ Set.Iio n).ncard : ℕ) : ℝ) =
        (((Set.Iio n).ncard : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]
  linarith

theorem hasDensity_zero_union
    {S T : Set ℕ} (hS : S.HasDensity 0) (hT : T.HasDensity 0) :
    (S ∪ T).HasDensity 0 := by
  rw [Set.HasDensity] at hS hT ⊢
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hS hT ⊢
  have hsum : Tendsto (fun n : ℕ ↦
      (((S ∩ Set.Iio n).ncard : ℕ) : ℝ) / (n : ℝ) +
        (((T ∩ Set.Iio n).ncard : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using hS.add hT
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hset : (S ∪ T) ∩ Set.Iio n =
        (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_Iio]
      tauto
    have hcard : ((S ∪ T) ∩ Set.Iio n).ncard ≤
        (S ∩ Set.Iio n).ncard + (T ∩ Set.Iio n).ncard := by
      rw [hset]
      exact Set.ncard_union_le _ _
    have hcardR : (((S ∪ T) ∩ Set.Iio n).ncard : ℝ) ≤
        (((S ∩ Set.Iio n).ncard : ℕ) : ℝ) +
          (((T ∩ Set.Iio n).ncard : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have hdiv := div_le_div_of_nonneg_right hcardR (by positivity : 0 ≤ (n : ℝ))
    simpa [add_div] using hdiv
  · exact hsum

theorem hasDensity_one_inter_of_hasDensity_one
    {A B : Set ℕ} (hA : A.HasDensity 1) (hB : B.HasDensity 1) :
    (A ∩ B).HasDensity 1 := by
  have hbad : (Aᶜ ∪ Bᶜ).HasDensity 0 :=
    hasDensity_zero_union
      (hasDensity_zero_of_hasDensity_one_compl hA)
      (hasDensity_zero_of_hasDensity_one_compl hB)
  have hgood : (Aᶜ ∪ Bᶜ)ᶜ.HasDensity 1 :=
    compl_hasDensity_one_of_hasDensity_zero hbad
  simpa [Set.compl_union] using hgood

/- A conversion useful for finite Chebyshev outputs: a vanishing exceptional ratio on
`S ∩ Icc 1 X` implies natural density zero.  The only discrepancy from `partialDensity` is the
possible element `0`, which costs at most one point. -/
theorem hasDensity_zero_of_Icc_ratio_zero
    (S : Set ℕ)
    (h : Tendsto (fun X : ℕ ↦
      (((S ∩ Set.Icc 1 X).ncard : ℕ) : ℝ) / (X : ℝ)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  rw [Set.HasDensity]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ ↦
      (1 + (((S ∩ Set.Icc 1 n).ncard : ℕ) : ℝ)) * (n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    convert h.add hinv using 1
    · ext n
      ring
    · norm_num
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hsub : S ∩ Set.Iio n ⊆ (S ∩ Set.Icc 1 n) ∪ {0} := by
      intro x hx
      by_cases hx0 : x = 0
      · exact Set.mem_union_right _ (by simp [hx0])
      · left
        refine ⟨hx.1, ?_⟩
        exact ⟨Nat.one_le_iff_ne_zero.mpr hx0, Nat.le_of_lt hx.2⟩
    have hfin : ((S ∩ Set.Icc 1 n) ∪ {0}).Finite := by
      apply Set.Finite.union
      · exact (Set.finite_Icc 1 n).subset (by intro x hx; exact hx.2)
      · exact Set.finite_singleton 0
    have hncard := Set.ncard_le_ncard hsub hfin
    have hcard : (S ∩ Set.Iio n).ncard ≤ (S ∩ Set.Icc 1 n).ncard + 1 := by
      exact hncard.trans (by simpa using Set.ncard_union_le (S ∩ Set.Icc 1 n) ({0} : Set ℕ))
    have hcardR : (((S ∩ Set.Iio n).ncard : ℕ) : ℝ) ≤
        (((S ∩ Set.Icc 1 n).ncard : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcard
    have hdiv := div_le_div_of_nonneg_right hcardR (by positivity : 0 ≤ (n : ℝ))
    simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using hdiv
  · exact hsum

/- A block-cover variant: it suffices to dominate the exceptional set inside every initial
interval by a finite endpoint filter whose normalized cardinality tends to zero. -/
theorem hasDensity_zero_of_Icc_filter_cover
    (S : Set ℕ) (E : ℕ → Finset ℕ)
    (hcover : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆ (E X : Set ℕ))
    (hbound : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  have hratio : Tendsto (fun X : ℕ ↦
      (((S ∩ Set.Icc 1 X).ncard : ℕ) : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
      have hcard := Set.ncard_le_ncard (hcover X) (Finset.finite_toSet (E X))
      have hcardR : (((S ∩ Set.Icc 1 X).ncard : ℕ) : ℝ) ≤ (E X).card := by
        rw [Set.ncard_coe_finset] at hcard
        exact_mod_cast hcard
      exact div_le_div_of_nonneg_right hcardR (by positivity : 0 ≤ (X : ℝ))
    · exact hbound
  exact hasDensity_zero_of_Icc_ratio_zero S hratio

/- A fixed exceptional set generated by a scale-dependent pair family.  The set records the
   actual integer being divisible by one of its own candidate pairs; the block cover below lets
   the endpoint `X` replace that moving family by a single finite family for the density estimate. -/
def variablePairExceptionalSet
    (pairs : ℕ → Finset (ℕ × ℕ)) : Set ℕ :=
  {n | ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n}

/- This is the direct density version of
   `tendsto_variableExceptionalRatio_zero_of_blockWeight` from `UnionBound`.  It is the reusable
   final bridge for the report's bad-pair weight: no monotonicity of `pairs` is required, only that
   every pair used at `n≤X` is included in the endpoint block `block X`. -/
theorem variablePairExceptionalSet_hasDensity_zero_of_blockWeight
    (pairs block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃X n : ℕ⦄, n ≤ X → pairs n ⊆ block X)
    (hweight : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (block X))
      atTop (𝓝 0)) :
    (variablePairExceptionalSet pairs).HasDensity 0 := by
  let E : ℕ → Finset ℕ := fun X ↦ divisibleBySomePairUpTo X (block X)
  have hcoverE : ∀ X : ℕ,
      variablePairExceptionalSet pairs ∩ Set.Icc 1 X ⊆ (E X : Set ℕ) := by
    intro X n hn
    have hdata : ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n := by
      have hmemS : n ∈ variablePairExceptionalSet pairs := hn.1
      change ∃ pq ∈ pairs n, n ≠ 0 ∧ pq.1 * pq.2 ∣ n at hmemS
      exact hmemS
    rcases hdata with ⟨pq, hpq, hn0, hdiv⟩
    have hnle : n ≤ X := hn.2.2
    have hpqX : pq ∈ block X := hcover hnle hpq
    have hnlt : n < X + 1 := Nat.lt_succ_of_le hnle
    unfold E divisibleBySomePairUpTo
    change n ∈ (block X).biUnion (fun pq ↦ divisibleUpTo X (pq.1 * pq.2))
    rw [Finset.mem_biUnion]
    refine ⟨pq, hpqX, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnlt, hn0, hdiv⟩
  have hbound : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    simpa [E] using tendsto_exceptionalRatio_zero_of_reciprocalWeight block hweight
  exact hasDensity_zero_of_Icc_filter_cover
    (variablePairExceptionalSet pairs) E hcoverE hbound

/- Report-scale specialization of the preceding fixed-set bridge.  The pair family may depend on
   the logarithmic endpoint `N`; an arbitrary endpoint block is accepted so the theorem remains
   honest about the floor/ceiling monotonicity still needed by a concrete report instantiation. -/
theorem variableLogReportPairExceptionalSet_hasDensity_zero_of_blockWeight
    {α β γ δ rho : ℝ} (block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃X N : ℕ⦄, N ≤ X →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆ block X)
    (hweight : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (block X))
      atTop (𝓝 0)) :
    (variablePairExceptionalSet
      (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)).HasDensity 0 := by
  apply variablePairExceptionalSet_hasDensity_zero_of_blockWeight
    (pairs := fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)
    block
  · exact hcover
  · exact hweight

/- If the logarithmic report families are eventually monotone at every endpoint, the report's
   own reciprocal-weight theorem supplies the block limit automatically.  This is the strongest
   report-specific density statement available without proving the remaining floor/ceiling
   monotonicity; it also gives a named target for that future arithmetic check. -/
theorem variableLogReportPairExceptionalSet_hasDensity_zero_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmono : ∀ ⦃N M : ℕ⦄, N ≤ M →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆
        badPairsAtReportScale (Real.log (M : ℝ)) α β γ δ rho) :
    (variablePairExceptionalSet
      (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)).HasDensity 0 := by
  let block : ℕ → Finset (ℕ × ℕ) := fun X ↦
    badPairsAtReportScale (Real.log (X : ℝ)) α β γ δ rho
  have hcover : ∀ ⦃X N : ℕ⦄, N ≤ X →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆ block X := by
    intro X N hNX
    exact hmono hNX
  have hweight : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (block X))
      atTop (𝓝 0) := by
    simpa [block] using
      (tendsto_badPairWeight_zero_of_log_report_scale_default
        hα hβ hβγ hδ0 hδ1 hβδ hrho)
  simpa [block] using
    (variableLogReportPairExceptionalSet_hasDensity_zero_of_blockWeight
      (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
      block hcover hweight)

/- The usable Track-A form: under the same report-scale hypotheses, the complement of the
   variable bad-pair set has natural density one.  Keeping this as a separate named theorem
   avoids repeating the complement bookkeeping at every later analytic application. -/
theorem variableLogReportPairGoodSet_hasDensity_one_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmono : ∀ ⦃N M : ℕ⦄, N ≤ M →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆
        badPairsAtReportScale (Real.log (M : ℝ)) α β γ δ rho) :
    (variablePairExceptionalSet
      (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho))ᶜ.HasDensity 1 := by
  exact compl_hasDensity_one_of_hasDensity_zero
    (variableLogReportPairExceptionalSet_hasDensity_zero_of_report_scale_default
      hα hβ hβγ hδ0 hδ1 hβδ hrho hmono)

/- A moving-tail variant of the preceding cover lemma.  It is useful when an exceptional set is
   controlled only on `[K X, X]`: the omitted initial segment contributes at most `K X` points,
   so a separate `K X / X → 0` check suffices.  No monotonicity of the moving tail is required. -/
theorem hasDensity_zero_of_Icc_tail_cover
    (S : Set ℕ) (K : ℕ → ℕ) (tail : ℕ → Finset ℕ)
    (hcover : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆
      (Finset.Icc 1 (K X - 1) ∪ tail X : Set ℕ))
    (hKratio : Tendsto (fun X : ℕ ↦ (K X : ℝ) / (X : ℝ)) atTop (𝓝 0))
    (htail : Tendsto (fun X : ℕ ↦ ((tail X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0)) :
    S.HasDensity 0 := by
  let E : ℕ → Finset ℕ := fun X ↦ Finset.Icc 1 (K X - 1) ∪ tail X
  have hcoverE : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆ (E X : Set ℕ) := by
    intro X
    simpa [E] using hcover X
  have hbound : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun X : ℕ ↦
        (K X : ℝ) / (X : ℝ) + ((tail X).card : ℝ) / (X : ℝ))
        atTop (𝓝 0) := by simpa using hKratio.add htail
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
      have hcardIcc : (Finset.Icc 1 (K X - 1)).card ≤ K X := by
        rw [Nat.card_Icc]
        omega
      have hcardUnion := Finset.card_union_le (Finset.Icc 1 (K X - 1)) (tail X)
      have hcardUnionR : ((E X).card : ℝ) ≤
          (K X : ℝ) + ((tail X).card : ℝ) := by
        have hcardUnionR' : ((E X).card : ℝ) ≤
            ((Finset.Icc 1 (K X - 1)).card : ℝ) + ((tail X).card : ℝ) := by
          exact_mod_cast hcardUnion
        have hcardIccR : ((Finset.Icc 1 (K X - 1)).card : ℝ) ≤ (K X : ℝ) := by
          exact_mod_cast hcardIcc
        exact hcardUnionR'.trans (add_le_add hcardIccR (le_refl _))
      have hdiv := div_le_div_of_nonneg_right hcardUnionR
        (by positivity : 0 ≤ (X : ℝ))
      have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
      have hrewrite :
          ((K X : ℝ) + ((tail X).card : ℝ)) / (X : ℝ) =
            (K X : ℝ) / (X : ℝ) + ((tail X).card : ℝ) / (X : ℝ) := by
        field_simp [hXreal.ne']
      simpa [E, hrewrite] using hdiv
    · exact hsum
  exact hasDensity_zero_of_Icc_filter_cover S E hcoverE hbound

/- Endpoint good-set ratios become a genuine density-zero pointwise exceptional set.  The only
   interpolation input is eventual monotonicity of `scale`; a fixed initial segment is absorbed by
   the general moving-tail density lemma. -/
theorem weightedScaleFLowerBadSet_hasDensity_zero_of_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    weightedScaleFLowerBadSet.HasDensity 0 := by
  let B : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter (fun n : ℕ ↦ (F n : ℝ) < scale X / 2)
  let G : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc 1 X).filter (fun n : ℕ ↦ scale X / 2 ≤ (F n : ℝ))
  have hgood := tendsto_weightedScale_good_F_ratio_one_of_moment_bounds
    R w V hprime hweight hvar hvanish
  have hpartition : ∀ X : ℕ, B X ∪ G X = Finset.Icc 1 X := by
    intro X
    ext n
    by_cases hn : n ∈ Finset.Icc 1 X
    · simp only [B, G, Finset.mem_union, Finset.mem_filter]
      by_cases hlt : (F n : ℝ) < scale X / 2
      · exact iff_of_true (Or.inl ⟨hn, hlt⟩) hn
      · exact iff_of_true (Or.inr ⟨hn, le_of_not_gt hlt⟩) hn
    · simp [B, G, hn]
  have hdisj : ∀ X : ℕ, Disjoint (B X) (G X) := by
    intro X
    rw [Finset.disjoint_left]
    intro n hnB hnG
    exact (not_lt_of_ge (Finset.mem_filter.mp hnG).2)
      (Finset.mem_filter.mp hnB).2
  have hcard : ∀ X : ℕ, ((B X).card : ℝ) + ((G X).card : ℝ) = (X : ℝ) := by
    intro X
    have hnat : (B X).card + (G X).card = X := by
      calc
        (B X).card + (G X).card = (B X ∪ G X).card :=
          (Finset.card_union_of_disjoint (hdisj X)).symm
        _ = (Finset.Icc 1 X).card := by rw [hpartition X]
        _ = X := by
          rw [Nat.card_Icc]
          omega
    exact_mod_cast hnat
  have hbad : Tendsto (fun X : ℕ ↦ ((B X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    have hgood' : Tendsto (fun X : ℕ ↦ ((G X).card : ℝ) / (X : ℝ))
        atTop (𝓝 1) := by
      simpa [G] using hgood
    have hdiff : Tendsto (fun X : ℕ ↦
        (1 : ℝ) - ((G X).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa using hconst.sub hgood'
    apply hdiff.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
    have hc := hcard X
    field_simp [hXreal.ne']
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_scale_mono
  have hcover : ∀ X : ℕ, weightedScaleFLowerBadSet ∩ Set.Icc 1 X ⊆
      (Finset.Icc 1 (N - 1) ∪ B X : Set ℕ) := by
    intro X n hn
    by_cases hnN : n < N
    · left
      apply Finset.mem_Icc.mpr
      exact ⟨hn.2.1, by omega⟩
    · right
      have hnN' : N ≤ n := Nat.le_of_not_gt hnN
      have hnIcc : n ∈ Finset.Icc 1 X := by
        exact Finset.mem_Icc.mpr ⟨hn.2.1, hn.2.2⟩
      have hmonoN := hN N (le_refl N)
      have hscale : scale n ≤ scale X := hmonoN hnN' hn.2.2
      have hbadX : (F n : ℝ) < scale X / 2 := by
        have hbadn : (F n : ℝ) < scale n / 2 := hn.1
        exact hbadn.trans_le (div_le_div_of_nonneg_right hscale (by norm_num))
      exact Finset.mem_filter.mpr ⟨hnIcc, hbadX⟩
  have hKratio : Tendsto (fun X : ℕ ↦ (N : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun X : ℕ ↦ (X : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hconst : Tendsto (fun _ : ℕ ↦ (N : ℝ)) atTop (𝓝 (N : ℝ)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  apply hasDensity_zero_of_Icc_tail_cover weightedScaleFLowerBadSet
    (fun _ : ℕ ↦ N) B hcover hKratio
  simpa [B] using hbad

/- Public density-one lower-bound package for `F`.  The theorem deliberately exposes the moment
   assumptions rather than hiding them: supplying the report's missing analytic variance estimate
   immediately yields `F n ≥ (1/2) n log log n` on a density-one subtype. -/
theorem exists_density_one_F_lower_of_weightedScale_moment_bounds
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  let S : Set ℕ := weightedScaleFLowerBadSet
  have hS0 : S.HasDensity 0 := by
    simpa [S] using
      weightedScaleFLowerBadSet_hasDensity_zero_of_moment_bounds
        R w V hprime hweight hvar hvanish
  let A : Set ℕ := Sᶜ
  have hA : A.HasDensity 1 := by
    simpa [A] using compl_hasDensity_one_of_hasDensity_zero hS0
  have hInf : A.Infinite :=
    Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, haA, hab⟩ := Set.Infinite.exists_gt hInf b
    filter_upwards [eventually_ge_atTop (⟨a, haA⟩ : A)] with n hn
    exact hab.le.trans (show a ≤ (n : ℕ) from hn)
  have hscaleA : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ) :=
    hcoe.eventually eventually_scale_pos
  refine ⟨A, hA, ?_⟩
  filter_upwards [hscaleA] with n hscale
  have hnot : ¬ ((F (n : ℕ) : ℝ) < scale (n : ℕ) / 2) := by
    simpa [A, S, weightedScaleFLowerBadSet] using n.property
  have hhalf : scale (n : ℕ) / 2 ≤ (F (n : ℕ) : ℝ) := le_of_not_gt hnot
  apply (le_div_iff₀ hscale).2
  simpa [div_eq_mul_inv, mul_comm] using hhalf

/- A finite Markov inequality for nonnegative real-valued data.  This is the exact counting
   kernel used in the elementary deduction from an upper bound for
   `H(X) = Σ_{n<X} f(n)/n`: the contribution of every filtered point is at least the chosen
   threshold, so its cardinality times that threshold is bounded by the ambient sum. -/
theorem card_filter_ge_mul_le_sum
    (s : Finset ℕ) (g : ℕ → ℝ) (b : ℝ)
    (_hb : 0 ≤ b) (hg : ∀ n ∈ s, 0 ≤ g n) :
    (((s.filter (fun n ↦ b ≤ g n)).card : ℕ) : ℝ) * b ≤
      ∑ n ∈ s, g n := by
  classical
  let t := s.filter (fun n ↦ b ≤ g n)
  have hpoint : ∀ n ∈ t, b ≤ g n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hsum₁ :
      (((t.card : ℕ) : ℝ) * b) ≤ ∑ n ∈ t, g n := by
    calc
      (((t.card : ℕ) : ℝ) * b) = ∑ _n ∈ t, b := by simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ n ∈ t, g n := by
        apply Finset.sum_le_sum
        intro n hn
        exact hpoint n hn
  have hsum₂ :
      (∑ n ∈ t, g n) ≤ ∑ n ∈ s, g n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hn _
    exact hg n hn
  simpa [t] using hsum₁.trans hsum₂

/- The same Markov kernel for the normalized source summand `f(n)/n`.  The denominator is
   harmless at `n = 0` because Lean's real division by zero is `0`; applications normally use
   `Icc 1 X`, matching the source problem. -/
theorem card_filter_f_div_ge_mul_le_sum
    (X : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    (((Finset.Icc 1 X).filter
      (fun n ↦ b ≤ (f n : ℝ) / (n : ℝ))).card : ℝ) * b ≤
      ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ) := by
  apply card_filter_ge_mul_le_sum (Finset.Icc 1 X) (fun n ↦ (f n : ℝ) / (n : ℝ)) b hb
  intro n hn
  exact div_nonneg (by positivity) (by positivity)

/- Weighted version of the same finite Markov step.  It is useful when the threshold varies with
   `n`, as in `ε * log (log n)`: the filtered weight is summed first, and only afterwards is an
   analytic lower bound used to turn that weighted estimate into a cardinality estimate. -/
theorem sum_filter_le_sum_of_nonneg_le
    (s : Finset ℕ) (g w : ℕ → ℝ)
    (hgw : ∀ n ∈ s.filter (fun n ↦ w n ≤ g n), w n ≤ g n)
    (_hw : ∀ n ∈ s.filter (fun n ↦ w n ≤ g n), 0 ≤ w n)
    (hg : ∀ n ∈ s, 0 ≤ g n) :
    ∑ n ∈ s.filter (fun n ↦ w n ≤ g n), w n ≤ ∑ n ∈ s, g n := by
  classical
  let t := s.filter (fun n ↦ w n ≤ g n)
  have hsum₁ : (∑ n ∈ t, w n) ≤ ∑ n ∈ t, g n := by
    apply Finset.sum_le_sum
    intro n hn
    exact hgw n hn
  have hsum₂ : (∑ n ∈ t, g n) ≤ ∑ n ∈ s, g n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hn _
    exact hg n hn
  simpa [t] using hsum₁.trans hsum₂

/- Finite form of the square-root cutoff argument used for the known `H`-upper-bound deduction.
   The analytic estimate is supplied as `hH`; all threshold monotonicity and cardinality
   bookkeeping are proved here.  Taking `K = ⌊√X⌋` and
   `L = ε * log (log K)` is the standard later specialization. -/
theorem exceptionalRatio_f_div_scale_le_of_summatory
    (X K : ℕ) {ε L H : ℝ}
    (hX : 0 < X) (hK : 1 ≤ K) (_hKX : K ≤ X)
    (hε : 0 < ε) (hL : 0 < L)
    (hscale : ∀ n ∈ Finset.Icc K X,
      L ≤ Real.log (Real.log (n : ℝ)))
    (hH : (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤ H) :
    (((Finset.Icc K X).filter
      (fun n : ℕ ↦ ε * Real.log (Real.log (n : ℝ)) ≤
        (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ) ≤
      H / (ε * L * (X : ℝ)) := by
  classical
  let s : Finset ℕ := Finset.Icc K X
  let E : Finset ℕ := s.filter (fun n ↦
    ε * Real.log (Real.log (n : ℝ)) ≤ (f n : ℝ) / (n : ℝ))
  let Cset : Finset ℕ := s.filter (fun n ↦
    ε * L ≤ (f n : ℝ) / (n : ℝ))
  have hEsub : E ⊆ Cset := by
    intro n hn
    have hnE := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hnE.1, ?_⟩
    calc
      ε * L ≤ ε * Real.log (Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hscale n hnE.1) hε.le
      _ ≤ (f n : ℝ) / (n : ℝ) := hnE.2
  have hcard : (E.card : ℝ) ≤ (Cset.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hEsub
  have hsI : s ⊆ Finset.Icc 1 X := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hK.trans hn'.1, hn'.2⟩
  have hsumS :
      (∑ n ∈ s, (f n : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsI
    intro n hn _
    exact div_nonneg (by positivity) (by positivity)
  have hmark :
      (Cset.card : ℝ) * (ε * L) ≤
        ∑ n ∈ s, (f n : ℝ) / (n : ℝ) := by
    simpa [Cset] using
      (card_filter_ge_mul_le_sum s (fun n : ℕ ↦ (f n : ℝ) / (n : ℝ))
        (ε * L) (mul_nonneg hε.le hL.le) (by
          intro n hn
          exact div_nonneg (by positivity) (by positivity)))
  have hmarkH : (Cset.card : ℝ) * (ε * L) ≤ H :=
    hmark.trans (hsumS.trans hH)
  have hEL : 0 < ε * L := mul_pos hε hL
  have hE : (E.card : ℝ) * (ε * L) ≤ H := by
    exact (mul_le_mul_of_nonneg_right hcard hEL.le).trans hmarkH
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  apply (div_le_iff₀ hXreal).2
  calc
    (E.card : ℝ) ≤ H / (ε * L) := (le_div_iff₀ hEL).2 hE
    _ = H / (ε * L * (X : ℝ)) * (X : ℝ) := by
      field_simp

/- Eventual wrapper for the preceding finite estimate.  It is the precise interface needed to
   turn a summatory upper bound into a fixed-`ε` zero-density exceptional set: callers provide
   the cutoff `K(X)`, its lower-log threshold `L(X)`, the summatory majorant `H(X)`, and the one
   normalized ratio limit. -/
theorem tendsto_exceptionalRatio_f_div_scale_zero_of_summatory
    (K : ℕ → ℕ) (L H : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε)
    (hK : ∀ᶠ X : ℕ in atTop, 1 ≤ K X)
    (hKX : ∀ᶠ X : ℕ in atTop, K X ≤ X)
    (hL : ∀ᶠ X : ℕ in atTop, 0 < L X)
    (hscale : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc (K X) X,
      L X ≤ Real.log (Real.log (n : ℝ)))
    (hH : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤ H X)
    (hvanish : Tendsto (fun X : ℕ ↦ H X / (ε * L X * (X : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      (((Finset.Icc (K X) X).filter
        (fun n : ℕ ↦ ε * Real.log (Real.log (n : ℝ)) ≤
          (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hK, hKX, hL, hscale, hH] with
      X hX hKX₀ hKX₁ hLX hscaleX hHX
    exact exceptionalRatio_f_div_scale_le_of_summatory X (K X)
      hX hKX₀ hKX₁ hε hLX hscaleX hHX
  · exact hvanish

/- A reusable analytic transfer for the preceding wrapper.  If the summatory majorant is bounded
   by `C * X * A(X)` and `A(X) / L(X) → 0`, then its normalization by `ε L(X) X` vanishes.
   This avoids baking any particular iterated-log estimate into the finite Markov theorem. -/
theorem tendsto_normalized_summatory_ratio_zero_of_upper_bound
    (Afun Lfun Hfun : ℕ → ℝ) {C ε : ℝ}
    (hε : 0 < ε)
    (hL : ∀ᶠ X : ℕ in atTop, 0 < Lfun X)
    (hH : ∀ᶠ X : ℕ in atTop, 0 ≤ Hfun X)
    (hupper : ∀ᶠ X : ℕ in atTop,
      Hfun X ≤ C * (X : ℝ) * Afun X)
    (hsmall : Tendsto (fun X : ℕ ↦ Afun X / Lfun X) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦ Hfun X / (ε * Lfun X * (X : ℝ))) atTop (𝓝 0) := by
  have hposX : ∀ᶠ X : ℕ in atTop, 0 < (X : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact_mod_cast hX
  have hden : ∀ᶠ X : ℕ in atTop, 0 < ε * Lfun X * (X : ℝ) := by
    filter_upwards [hL, hposX] with X hLX hX
    exact mul_pos (mul_pos hε hLX) hX
  have hratio : ∀ᶠ X : ℕ in atTop,
      0 ≤ Hfun X / (ε * Lfun X * (X : ℝ)) ∧
        Hfun X / (ε * Lfun X * (X : ℝ)) ≤
          (C / ε) * (Afun X / Lfun X) := by
    filter_upwards [hH, hupper, hden, hposX, hL] with
      X hHX hUX hdenX hX hLX
    constructor
    · exact div_nonneg hHX (le_of_lt hdenX)
    · calc
        Hfun X / (ε * Lfun X * (X : ℝ)) ≤
            (C * (X : ℝ) * Afun X) / (ε * Lfun X * (X : ℝ)) := by
          exact div_le_div_of_nonneg_right hUX (le_of_lt hdenX)
        _ = (C / ε) * (Afun X / Lfun X) := by
          field_simp [hε.ne', hLX.ne', hX.ne']
  apply squeeze_zero'
  · filter_upwards [hratio] with X hX
    exact hX.1
  · filter_upwards [hratio] with X hX
    exact hX.2
  · simpa [mul_comm] using hsmall.const_mul (C / ε)

/- Iterated-log asymptotic used by the source's `H(X)` estimate.  This is entirely available in
   Mathlib: `log = o(id)` composed with `log ∘ log` gives
   `log(log(log X)) / log(log X) → 0`, including the natural-number endpoint version. -/
theorem tendsto_logloglog_div_loglog_nat_zero :
    Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ))) /
        Real.log (Real.log (X : ℝ))) atTop (𝓝 0) := by
  have hll : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ho : (fun x : ℝ ↦ Real.log (Real.log (Real.log x))) =o[atTop]
      (fun x : ℝ ↦ Real.log (Real.log x)) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_log_id_atTop.comp_tendsto hll)
  simpa [Function.comp_def] using
    ho.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/- A slightly stronger iterated-log estimate for a square-root Markov threshold.  It follows by
   writing `log(log x) = 2 * log(sqrt(log(log x)))` and applying `log = o(id)` to the square-root
   variable. -/
theorem tendsto_logloglog_div_sqrt_loglog_nat_zero :
    Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ))) /
        Real.sqrt (Real.log (Real.log (X : ℝ)))) atTop (𝓝 0) := by
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun X : ℕ ↦
      Real.sqrt (Real.log (Real.log (X : ℝ)))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hll
  have ho : (fun y : ℝ ↦ Real.log y) =o[atTop] id :=
    Real.isLittleO_log_id_atTop
  have hratio : Tendsto (fun X : ℕ ↦
      Real.log (Real.sqrt (Real.log (Real.log (X : ℝ)))) /
        Real.sqrt (Real.log (Real.log (X : ℝ)))) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero.comp hu
  have hmul : Tendsto (fun X : ℕ ↦ 2 *
      (Real.log (Real.sqrt (Real.log (Real.log (X : ℝ)))) /
        Real.sqrt (Real.log (Real.log (X : ℝ))))) atTop (𝓝 0) := by
    simpa using hratio.const_mul 2
  have hpos : ∀ᶠ X : ℕ in atTop,
      0 ≤ Real.log (Real.log (X : ℝ)) :=
    hll.eventually (eventually_ge_atTop (0 : ℝ))
  apply hmul.congr'
  filter_upwards [hpos] with X hX
  rw [Real.log_sqrt hX]
  ring

/- The harmless constant `1/2` in the square-root Markov threshold does not change the
   iterated-log limit.  We record the exact rescaling because it is useful for a moving
   threshold argument: `√(L/2) = √L / √2` eventually, once `L = log log X` is positive. -/
theorem tendsto_logloglog_div_sqrt_half_loglog_nat_zero :
    Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ))) /
        Real.sqrt ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)))) atTop (𝓝 0) := by
  have hbase := tendsto_logloglog_div_sqrt_loglog_nat_zero
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmul := hbase.const_mul (Real.sqrt 2)
  have hmul0 : Tendsto (fun X : ℕ ↦ Real.sqrt 2 *
      (Real.log (Real.log (Real.log (X : ℝ))) /
        Real.sqrt (Real.log (Real.log (X : ℝ))))) atTop (𝓝 0) := by
    simpa using hmul
  apply hmul0.congr'
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (Real.log (X : ℝ)) :=
    hll.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hpos] with X hX
  have hs : Real.sqrt ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ))) =
      Real.sqrt (Real.log (Real.log (X : ℝ))) / Real.sqrt 2 := by
    rw [show (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) =
      Real.log (Real.log (X : ℝ)) / 2 by ring]
    rw [Real.sqrt_div (by positivity : 0 ≤ Real.log (Real.log (X : ℝ)))]
  rw [hs]
  have hroot : Real.sqrt (Real.log (Real.log (X : ℝ))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 hX
  field_simp [hsqrt2.ne', hroot]

/- The corresponding normalized H(X) bound with a square-root lower threshold.  This is the
   exact asymptotic ratio needed by a moving-threshold Markov argument; it still takes the source
   theorem-7 upper bound as an explicit input. -/
theorem tendsto_summatory_f_div_sqrt_loglog_mul_self_zero
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    Tendsto (fun X : ℕ ↦
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) /
        (Real.sqrt (Real.log (Real.log (X : ℝ))) * (X : ℝ))) atTop (𝓝 0) := by
  let Hfun : ℕ → ℝ := fun X ↦
    ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)
  let Lfun : ℕ → ℝ := fun X ↦ Real.sqrt (Real.log (Real.log (X : ℝ)))
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hL : ∀ᶠ X : ℕ in atTop, 0 < Lfun X := by
    filter_upwards [hll.eventually (eventually_gt_atTop (0 : ℝ))] with X hX
    exact Real.sqrt_pos.2 hX
  have hH : ∀ᶠ X : ℕ in atTop, 0 ≤ Hfun X := by
    filter_upwards [] with X
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (by positivity) (by positivity)
  have hnorm := tendsto_normalized_summatory_ratio_zero_of_upper_bound
    (Afun := fun X : ℕ ↦ Real.log (Real.log (Real.log (X : ℝ))))
    (Lfun := Lfun) (Hfun := Hfun) (C := C) (ε := (1 : ℝ))
    (by norm_num) hL hH (by simpa [Hfun] using hHupper)
    tendsto_logloglog_div_sqrt_loglog_nat_zero
  simpa [Hfun, Lfun] using hnorm

/- Specialization matching the upper bound recorded in the Erdős paper.  The cutoff lower bound
   is intentionally supplied as `hscale` (for example, a square-root cutoff gives half the outer
   iterated logarithm); the only analytic summatory input is `hHupper`. -/
theorem tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog
    (K : ℕ → ℕ) {C ε : ℝ}
    (hε : 0 < ε) (_hC : 0 ≤ C)
    (hK : ∀ᶠ X : ℕ in atTop, 1 ≤ K X)
    (hKX : ∀ᶠ X : ℕ in atTop, K X ≤ X)
    (hscale : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc (K X) X,
      (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log (n : ℝ)))
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    Tendsto (fun X : ℕ ↦
      (((Finset.Icc (K X) X).filter
        (fun n : ℕ ↦ ε * Real.log (Real.log (n : ℝ)) ≤
          (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  let Lfun : ℕ → ℝ := fun X ↦
    (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ))
  let Hfun : ℕ → ℝ := fun X ↦
    ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hLpos : ∀ᶠ X : ℕ in atTop, 0 < Lfun X := by
    filter_upwards [hll.eventually (eventually_gt_atTop (0 : ℝ))] with X hX
    exact mul_pos (by norm_num) hX
  have hHnonneg : ∀ᶠ X : ℕ in atTop, 0 ≤ Hfun X := by
    filter_upwards [] with X
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (by positivity) (by positivity)
  have hsmall : Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ))) / Lfun X) atTop (𝓝 0) := by
    have hbase := tendsto_logloglog_div_loglog_nat_zero
    have hpos := hll.eventually (eventually_gt_atTop (0 : ℝ))
    have hmul : Tendsto (fun X : ℕ ↦
        2 * (Real.log (Real.log (Real.log (X : ℝ))) /
          Real.log (Real.log (X : ℝ)))) atTop (𝓝 0) := by
      simpa using hbase.const_mul 2
    apply hmul.congr'
    filter_upwards [hpos] with X hX
    simp only [Lfun]
    field_simp
  have hnorm : Tendsto (fun X : ℕ ↦ Hfun X /
      (ε * Lfun X * (X : ℝ))) atTop (𝓝 0) := by
    apply tendsto_normalized_summatory_ratio_zero_of_upper_bound
      (Afun := fun X : ℕ ↦ Real.log (Real.log (Real.log (X : ℝ))))
      (Lfun := Lfun) (Hfun := Hfun) hε hLpos hHnonneg
    · simpa [Hfun] using hHupper
    · exact hsmall
  exact tendsto_exceptionalRatio_f_div_scale_zero_of_summatory
    K Lfun Hfun hε hK hKX hLpos (by simpa [Lfun] using hscale)
      (by
        filter_upwards [] with X
        rfl) hnorm

/- The canonical integer cutoff for the source argument.  The remaining lower-log comparison is
   still supplied by the analytic caller, but the elementary endpoint facts for
   `K(X) = ⌈√X⌉₊` are now discharged once and reused by the specialization below. -/
noncomputable def sqrtCutoff (X : ℕ) : ℕ := Nat.ceil (Real.sqrt (X : ℝ))

theorem eventually_sqrtCutoff_bounds :
    (∀ᶠ X : ℕ in atTop, 1 ≤ sqrtCutoff X) ∧
      (∀ᶠ X : ℕ in atTop, sqrtCutoff X ≤ X) := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    unfold sqrtCutoff
    apply (Nat.one_le_ceil_iff).2
    exact Real.sqrt_pos.2 (by exact_mod_cast hX)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    unfold sqrtCutoff
    apply Nat.ceil_le.mpr
    have hXreal : 0 ≤ (X : ℝ) := by positivity
    have hsq : (X : ℝ) ≤ (X : ℝ) ^ 2 := by
      have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hX)
      nlinarith
    exact (Real.sqrt_le_left hXreal).2 hsq

/- The canonical square-root cutoff is negligible compared with its endpoint.  This is the
   elementary initial-segment estimate needed by `hasDensity_zero_of_Icc_tail_cover`; the ceiling
   costs only one point after division by `X`. -/
theorem tendsto_sqrtCutoff_div_self_zero :
    Tendsto (fun X : ℕ ↦ (sqrtCutoff X : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun X : ℕ ↦ Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvsqrt : Tendsto (fun X : ℕ ↦ (Real.sqrt (X : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hinvX : Tendsto (fun X : ℕ ↦ (X : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ ↦
      (Real.sqrt (X : ℝ))⁻¹ + (X : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using hinvsqrt.add hinvX
  refine squeeze_zero'
    (f := fun X : ℕ ↦ (sqrtCutoff X : ℝ) / (X : ℝ))
    (g := fun X : ℕ ↦ (Real.sqrt (X : ℝ))⁻¹ + (X : ℝ)⁻¹) ?_ ?_ hupper
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
    have hceil : (sqrtCutoff X : ℝ) < Real.sqrt (X : ℝ) + 1 := by
      unfold sqrtCutoff
      exact Nat.ceil_lt_add_one (by positivity)
    have hbound : (sqrtCutoff X : ℝ) / (X : ℝ) ≤
        (Real.sqrt (X : ℝ) + 1) / (X : ℝ) :=
      div_le_div_of_nonneg_right hceil.le hXreal.le
    have hrewrite : (Real.sqrt (X : ℝ) + 1) / (X : ℝ) =
        (Real.sqrt (X : ℝ))⁻¹ + (X : ℝ)⁻¹ := by
      rw [add_div, Real.sqrt_div_self]
      simp [one_div]
    rw [hrewrite] at hbound
    exact hbound

/- The lower-log side condition used in the H(X) argument is automatic for the canonical
   square-root cutoff. Once `log X ≥ 4`, every `n ≥ ceil (sqrt X)` has
   `log log n ≥ (1/2) log log X`. -/
theorem eventually_sqrtCutoff_loglog_lower :
    ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc (sqrtCutoff X) X,
      (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log (n : ℝ)) := by
  have hXlarge : ∀ᶠ X : ℕ in atTop,
      (4 : ℝ) ≤ Real.log (X : ℝ) ∧ 0 < Real.log (X : ℝ) := by
    have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually (eventually_ge_atTop (4 : ℝ))] with X hX
    exact ⟨hX, by linarith⟩
  filter_upwards [hXlarge] with X hX n hn
  have hXpos : 0 < (X : ℝ) := by
    have hXone : (1 : ℝ) < (X : ℝ) :=
      (Real.log_pos_iff (by positivity : 0 ≤ (X : ℝ))).mp hX.2
    linarith
  have hXone : (1 : ℝ) < (X : ℝ) :=
    (Real.log_pos_iff (by positivity : 0 ≤ (X : ℝ))).mp hX.2
  have hnlow : sqrtCutoff X ≤ n := (Finset.mem_Icc.mp hn).1
  have hceil : Real.sqrt (X : ℝ) ≤ (sqrtCutoff X : ℝ) := by
    unfold sqrtCutoff
    exact_mod_cast (Nat.le_ceil (Real.sqrt (X : ℝ)))
  have hsqrt_le_n : Real.sqrt (X : ℝ) ≤ (n : ℝ) := by
    exact hceil.trans (by exact_mod_cast hnlow)
  have hlogsqrt : Real.log (Real.sqrt (X : ℝ)) = Real.log (X : ℝ) / 2 :=
    Real.log_sqrt (le_of_lt hXpos)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hsqrt_one : 1 < Real.sqrt (X : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) hXone
    exact lt_of_lt_of_le hsqrt_one hsqrt_le_n
  have hlog_lower : Real.log (X : ℝ) / 2 ≤ Real.log (n : ℝ) := by
    have hlogsqrt_le : Real.log (Real.sqrt (X : ℝ)) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Real.sqrt_pos.2 hXpos) hsqrt_le_n
    simpa [hlogsqrt] using hlogsqrt_le
  have hhalf_pos : 0 < Real.log (X : ℝ) / 2 := by linarith [hX.2]
  have hloglog_lower : Real.log (Real.log (X : ℝ) / 2) ≤
      Real.log (Real.log (n : ℝ)) := by
    exact Real.log_le_log hhalf_pos hlog_lower
  have hloglog4 : Real.log (4 : ℝ) ≤ Real.log (Real.log (X : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    exact hX.1
  have hlog2half : Real.log (2 : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) := by
    have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4eq] at hloglog4
    nlinarith
  have htarget : (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
      Real.log (Real.log (X : ℝ) / 2) := by
    rw [Real.log_div (by linarith [hX.2]) (by norm_num)] at hloglog_lower ⊢
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith [hlog2half]
  exact htarget.trans hloglog_lower

/- The fixed-threshold exceptional set for the `f`-side estimate.  The definition is kept
   separate from the eventual little-o statement so that the summatory `H(X)` argument can be
   reused with different thresholds in a later diagonalization. -/
noncomputable def fLargeSet (ε : ℝ) : Set ℕ :=
  {n | ε * Real.log (Real.log (n : ℝ)) ≤ (f n : ℝ) / (n : ℝ)}

/- The source's summatory estimate implies density zero for every fixed positive threshold, once
   the lower-log comparison on the moving tail is supplied.  The initial segment is handled by
   `hasDensity_zero_of_Icc_tail_cover`; no monotonicity of the tail family is assumed. -/
theorem fLargeSet_hasDensity_zero_of_H_logloglog
    (K : ℕ → ℕ) {C ε : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hK : ∀ᶠ X : ℕ in atTop, 1 ≤ K X)
    (hKX : ∀ᶠ X : ℕ in atTop, K X ≤ X)
    (hKratio : Tendsto (fun X : ℕ ↦ (K X : ℝ) / (X : ℝ)) atTop (𝓝 0))
    (hscale : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc (K X) X,
      (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log (n : ℝ)))
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    (fLargeSet ε).HasDensity 0 := by
  let tail : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc (K X) X).filter (fun n ↦
      ε * Real.log (Real.log (n : ℝ)) ≤ (f n : ℝ) / (n : ℝ))
  have hcover : ∀ X : ℕ, fLargeSet ε ∩ Set.Icc 1 X ⊆
      (Finset.Icc 1 (K X - 1) ∪ tail X : Set ℕ) := by
    intro X n hn
    rw [Set.mem_union]
    by_cases hnK : n < K X
    · left
      apply Finset.mem_Icc.mpr
      exact ⟨hn.2.1, by omega⟩
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt hnK, hn.2.2⟩, ?_⟩
      exact hn.1
  apply hasDensity_zero_of_Icc_tail_cover (fLargeSet ε) K tail hcover hKratio
  simpa [tail] using
    (tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog K hε hC hK hKX
      hscale hHupper)

/- Square-root-cutoff specialization of the `H(X) ≪ X log log log X` bridge with an explicit
   lower-log hypothesis retained for callers that already have one.  The preceding wrapper
   `fLargeSet_hasDensity_zero_of_H_logloglog_sqrtCutoff` discharges this hypothesis automatically
   for the fixed-threshold density statement. -/
/- With the preceding automatic square-root lower-log estimate, the fixed-threshold density-zero
   consequence needs only the summatory H(X) upper bound itself. -/
theorem fLargeSet_hasDensity_zero_of_H_logloglog_sqrtCutoff
    {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    (fLargeSet ε).HasDensity 0 := by
  exact fLargeSet_hasDensity_zero_of_H_logloglog sqrtCutoff hε hC
    eventually_sqrtCutoff_bounds.1 eventually_sqrtCutoff_bounds.2
    tendsto_sqrtCutoff_div_self_zero eventually_sqrtCutoff_loglog_lower hHupper

theorem tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog_sqrtCutoff
    {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hscale : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc (sqrtCutoff X) X,
      (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log (n : ℝ)))
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    Tendsto (fun X : ℕ ↦
      (((Finset.Icc (sqrtCutoff X) X).filter
        (fun n : ℕ ↦ ε * Real.log (Real.log (n : ℝ)) ≤
          (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  exact tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog
    sqrtCutoff hε hC eventually_sqrtCutoff_bounds.1
      eventually_sqrtCutoff_bounds.2 hscale hHupper

/- Automatic square-root version of the endpoint ratio wrapper.  The explicit-`hscale` theorem
   above remains available for callers with a sharper cutoff estimate. -/
theorem tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog_sqrtCutoff_auto
    {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    Tendsto (fun X : ℕ ↦
      (((Finset.Icc (sqrtCutoff X) X).filter
        (fun n : ℕ ↦ ε * Real.log (Real.log (n : ℝ)) ≤
          (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  exact tendsto_exceptionalRatio_f_div_scale_zero_of_H_logloglog_sqrtCutoff
    hε hC eventually_sqrtCutoff_loglog_lower hHupper

/- A single moving Markov threshold avoids a countable `ε`-diagonalization on the `f` side.  The
   exceptional set consists of those `n` for which `f(n)/n` is at least `√(log log n)`. -/
noncomputable def fSqrtBadSet : Set ℕ :=
  {n | 16 ≤ n ∧ Real.sqrt (Real.log (Real.log (n : ℝ))) ≤
    (f n : ℝ) / (n : ℝ)}

theorem tendsto_fSqrtBadRatio_zero_of_H_logloglog
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    Tendsto (fun X : ℕ ↦
      (((Finset.Icc (sqrtCutoff X) X).filter
        (fun n : ℕ ↦ Real.sqrt (Real.log (Real.log (n : ℝ))) ≤
          (f n : ℝ) / (n : ℝ))).card : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  let tail : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc (sqrtCutoff X) X).filter (fun n ↦
      Real.sqrt (Real.log (Real.log (n : ℝ))) ≤ (f n : ℝ) / (n : ℝ))
  have hbase : Tendsto (fun X : ℕ ↦
      Real.log (Real.log (Real.log (X : ℝ))) /
        Real.sqrt ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)))) atTop (𝓝 0) :=
    tendsto_logloglog_div_sqrt_half_loglog_nat_zero
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (Real.log (X : ℝ)) :=
    hll.eventually (eventually_gt_atTop (0 : ℝ))
  have hcut := eventually_sqrtCutoff_bounds
  have hscale := eventually_sqrtCutoff_loglog_lower
  have hbound : ∀ᶠ X : ℕ in atTop,
      ((tail X).card : ℝ) / (X : ℝ) ≤
        C * (Real.log (Real.log (Real.log (X : ℝ))) /
          Real.sqrt ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hpos, hcut.1, hcut.2,
      hscale, hHupper] with X hX hlog hK hKX hsc hH
    let b : ℝ := Real.sqrt ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)))
    let E : Finset ℕ := tail X
    let Cset : Finset ℕ := (Finset.Icc 1 X).filter (fun n ↦
      b ≤ (f n : ℝ) / (n : ℝ))
    have hb : 0 < b := by
      apply Real.sqrt_pos.2
      positivity
    have hsub : E ⊆ Cset := by
      intro n hn
      have hnE := Finset.mem_filter.mp hn
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hK.trans (Finset.mem_Icc.mp hnE.1).1,
          (Finset.mem_Icc.mp hnE.1).2⟩
      · exact (Real.sqrt_le_sqrt (hsc n hnE.1)).trans hnE.2
    have hcard : (E.card : ℝ) ≤ (Cset.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hmark : (Cset.card : ℝ) * b ≤
        ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ) := by
      simpa [Cset] using
        (card_filter_ge_mul_le_sum (Finset.Icc 1 X)
          (fun n : ℕ ↦ (f n : ℝ) / (n : ℝ)) b hb.le (by
            intro n hn
            exact div_nonneg (by positivity) (by positivity)))
    have hE : (E.card : ℝ) * b ≤
        ∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ) :=
      (mul_le_mul_of_nonneg_right hcard hb.le).trans hmark
    have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
    have hratio : (E.card : ℝ) / (X : ℝ) ≤
        (C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) /
          (b * (X : ℝ)) := by
      apply (div_le_iff₀ hXreal).2
      calc
        (E.card : ℝ) ≤
            (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) / b :=
          (le_div_iff₀ hb).2 hE
        _ ≤ (C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) / b := by
          exact div_le_div_of_nonneg_right hH (le_of_lt hb)
        _ = (C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) /
              (b * (X : ℝ)) * (X : ℝ) := by
          field_simp [hb.ne', hXreal.ne']
    calc
      (tail X).card / (X : ℝ) ≤
          (C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) /
            (b * (X : ℝ)) := by
        simpa [E] using hratio
      _ = C * (Real.log (Real.log (Real.log (X : ℝ))) / b) := by
        field_simp [hb.ne', hXreal.ne']
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · exact hbound
  · simpa [mul_comm] using hbase.const_mul C

theorem fSqrtBadSet_hasDensity_zero_of_H_logloglog
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    fSqrtBadSet.HasDensity 0 := by
  let tail : ℕ → Finset ℕ := fun X ↦
    (Finset.Icc (sqrtCutoff X) X).filter (fun n ↦
      Real.sqrt (Real.log (Real.log (n : ℝ))) ≤ (f n : ℝ) / (n : ℝ))
  have hcover : ∀ X : ℕ, fSqrtBadSet ∩ Set.Icc 1 X ⊆
      (Finset.Icc 1 (sqrtCutoff X - 1) ∪ tail X : Set ℕ) := by
    intro X n hn
    rw [Set.mem_union]
    by_cases hnK : n < sqrtCutoff X
    · left
      apply Finset.mem_Icc.mpr
      exact ⟨hn.2.1, by omega⟩
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt hnK, hn.2.2⟩, ?_⟩
      exact hn.1.2
  apply hasDensity_zero_of_Icc_tail_cover fSqrtBadSet sqrtCutoff tail hcover
    tendsto_sqrtCutoff_div_self_zero
  simpa [tail] using tendsto_fSqrtBadRatio_zero_of_H_logloglog hHupper

/- The moving square-root threshold also closes the `f` little-o statement on its complement.
   This is the direct density-one-side interface: no countable family of fixed thresholds is
   needed once the single moving exceptional set above has density zero. -/
theorem fSqrtBadSet_compl_f_div_scale_littleO_of_H_logloglog
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦ scale (n : ℕ)) := by
  let A : Set ℕ := fSqrtBadSetᶜ
  have hS0 : fSqrtBadSet.HasDensity 0 :=
    fSqrtBadSet_hasDensity_zero_of_H_logloglog hHupper
  have hA : A.HasDensity 1 := by
    simpa [A] using compl_hasDensity_one_of_hasDensity_zero hS0
  have hInf : A.Infinite :=
    Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, haA, hab⟩ := Set.Infinite.exists_gt hInf b
    filter_upwards [eventually_ge_atTop (⟨a, haA⟩ : A)] with n hn
    exact hab.le.trans (show a ≤ (n : ℕ) from hn)
  have hlarge : ∀ᶠ n : A in atTop, 16 ≤ (n : ℕ) := by
    exact hcoe.eventually (eventually_ge_atTop (16 : ℕ))
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (Real.log (n : ℝ))))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hll
  have hinv : Tendsto (fun n : ℕ ↦
      (Real.sqrt (Real.log (Real.log (n : ℝ))))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hinvA : Tendsto (fun n : A ↦
      (Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))))⁻¹) atTop (𝓝 0) :=
    hinv.comp hcoe
  rw [isLittleO_iff]
  intro c hc
  have hsmall := hinvA.eventually (eventually_lt_nhds hc)
  have hlogA : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)) := by
    exact (hll.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))
  have hscaleA : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ) := by
    filter_upwards [hlarge, hlogA] with n hn hlln
    unfold scale
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))) hlln
  filter_upwards [hsmall, hlarge, hlogA, hscaleA] with n hinvN hnlarge hlogN hscaleN
  change (Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))))⁻¹ < c at hinvN
  change 16 ≤ (n : ℕ) at hnlarge
  change 0 < Real.log (Real.log ((n : ℕ) : ℝ)) at hlogN
  change 0 < scale (n : ℕ) at hscaleN
  have hnot : ¬ (16 ≤ (n : ℕ) ∧
      Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) ≤
        (f (n : ℕ) : ℝ) / ((n : ℕ) : ℝ)) := by
    exact n.property
  have hbad : (f (n : ℕ) : ℝ) / ((n : ℕ) : ℝ) <
      Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) := by
    exact lt_of_not_ge (fun hge ↦ hnot ⟨hnlarge, hge⟩)
  have hnpos : 0 < ((n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))
  have hsqrtpos : 0 < Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) :=
    Real.sqrt_pos.2 hlogN
  have hmul : (f (n : ℕ) : ℝ) <
      ((n : ℕ) : ℝ) * Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) := by
    simpa [mul_comm] using (div_lt_iff₀ hnpos).mp hbad
  have hrootbound : Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) ≤
      c * Real.log (Real.log ((n : ℕ) : ℝ)) := by
    have hrecip : (Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))))⁻¹ ≤ c := by
      exact hinvN.le
    have hrootne : Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) ≠ 0 :=
      hsqrtpos.ne'
    have hlogeq : Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) ^ 2 =
        Real.log (Real.log ((n : ℕ) : ℝ)) := by
      exact Real.sq_sqrt (le_of_lt hlogN)
    have hmulrec : (1 : ℝ) ≤
        Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) * c := by
      have := mul_le_mul_of_nonneg_left hrecip (le_of_lt hsqrtpos)
      rw [mul_inv_cancel₀ hrootne] at this
      exact this
    calc
      Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) =
          1 * Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) := by ring
      _ ≤ (Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) * c) *
          Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hmulrec (le_of_lt hsqrtpos)
      _ = c * Real.log (Real.log ((n : ℕ) : ℝ)) := by
        calc
          (Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) * c) *
              Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) =
              c * Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) ^ 2 := by ring
          _ = c * Real.log (Real.log ((n : ℕ) : ℝ)) := by rw [hlogeq]
  have hreal : (f (n : ℕ) : ℝ) ≤ c * scale (n : ℕ) := by
    unfold scale
    calc
      (f (n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) *
          Real.sqrt (Real.log (Real.log ((n : ℕ) : ℝ))) := hmul.le
      _ ≤ ((n : ℕ) : ℝ) *
          (c * Real.log (Real.log ((n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hrootbound (by positivity)
      _ = c * (((n : ℕ) : ℝ) * Real.log (Real.log ((n : ℕ) : ℝ))) := by
        ring
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (f (n : ℕ) : ℝ)),
    abs_of_pos hscaleN] using hreal


/- Public existential wrapper for the first half of the official almost-all question.  The
   exceptional set is the moving square-root set already controlled above; this theorem exposes
   exactly the density-one/little-o package without mentioning its internal cutoff definition.
   The remaining `F` lower bound is intentionally not smuggled into this result. -/
theorem exists_density_one_f_div_scale_littleO_of_H_logloglog
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ)))) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
        (fun n : A ↦ scale (n : ℕ)) := by
  refine ⟨(fSqrtBadSetᶜ : Set ℕ),
    compl_hasDensity_one_of_hasDensity_zero
      (fSqrtBadSet_hasDensity_zero_of_H_logloglog hHupper), ?_⟩
  exact fSqrtBadSet_compl_f_div_scale_littleO_of_H_logloglog hHupper

/- The preceding global dyadic summation supplies the source `H` hypothesis unconditionally from
   the proved local block estimate.  Thus the density-one little-o half of Track A is now a closed
   theorem; only the matching-based lower/asymptotic estimate for `F` remains. -/
theorem exists_density_one_f_div_scale_littleO_of_source_blocks :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
        (fun n : A ↦ scale (n : ℕ)) := by
  rcases exists_global_summatory_f_div_Icc_le_source_logloglog with
    ⟨C, hC, hHupper⟩
  exact exists_density_one_f_div_scale_littleO_of_H_logloglog hHupper


/- The first question in the FClike package. -/
@[category research open, AMS 11]
def erdos_878.parts.i : Prop :=
    answer(True) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop] (fun n : A ↦ scale n) ∧
      (fun n : A ↦ scale n) =O[atTop] (fun n : A ↦ (F n : ℝ))

/-- The second natural-language question in the FClike statement package. -/
@[category research open, AMS 11]
def erdos_878.parts.ii : Prop :=
    Tendsto (fun x : ℕ ↦
      (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
      atTop (𝓝 1)


namespace erdos_878.variants

@[category research solved, AMS 11]
def second_question_subsequence : Prop :=
    ∃ X : ℕ → ℕ, Tendsto X atTop atTop ∧
      Tendsto (fun k : ℕ ↦
        (maxUpTo f (X k) : ℝ) /
          ((X k : ℝ) * Real.log (X k) / Real.log (Real.log (X k))))
        atTop (𝓝 1)

end erdos_878.variants

/- The coefficient-`1/2` variant from the official Remarks. -/
@[category research solved, AMS 11]
def erdos_878.variants.proposed_first_question_sharp : Prop :=
    answer(True) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦
        (F n : ℝ) / ((n : ℝ) * Real.log (Real.log (n : ℝ))))
        atTop (𝓝 (1 / 2 : ℝ))

namespace erdos_878.variants

@[category research solved, AMS 11]
def H_div_self_limsup_infinite : Prop :=
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C ≤ H x / (x : ℝ)

@[category research solved, AMS 11]
def H_div_self_liminf_finite : Prop :=
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, H x / (x : ℝ) ≤ C

@[category research solved, AMS 11]
def H_upper_triple_log : Prop :=
    H =O[atTop] fun x : ℕ ↦
      (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ)))

@[category research solved, AMS 11]
def H_lower_quadruple_log_infinitely_often : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ H x

end erdos_878.variants

/-- Internal quantitative strengthening of formula (17). -/
@[category research open, AMS 11]
def erdos_878.variants.proposed_original_formula_17_sharp : Prop :=
    answer(True) ↔
      (1 : ℝ) ≤ atTop.liminf (fun x : ℕ ↦
        (maximalOrderGap x : ℝ) / maximalOrderGapScale x)

/- Original formula (17): the normalized gap tends to infinity. -/
@[category research open, AMS 11]
def erdos_878.variants.original_formula_17 : Prop :=
    answer(True) ↔
      Tendsto (fun x : ℕ ↦
        (maximalOrderGap x : ℝ) / (x : ℝ)) atTop atTop

/- Reduction lemmas for the statement definitions. -/
theorem proposed_first_question_sharp_iff :
    erdos_878.variants.proposed_first_question_sharp ↔
      (∃ A : Set ℕ, A.HasDensity 1 ∧
        Tendsto (fun n : A ↦ (F n : ℝ) / scale n) atTop (𝓝 (1 / 2 : ℝ))) := by
  simp [erdos_878.variants.proposed_first_question_sharp, scale]

theorem proposed_first_question_fixed_loss_iff :
    erdos_878.parts.i ↔
      (∃ A : Set ℕ, A.HasDensity 1 ∧
        (fun n : A ↦ (f n : ℝ)) =o[atTop] (fun n : A ↦ scale n) ∧
        (fun n : A ↦ scale n) =O[atTop] (fun n : A ↦ (F n : ℝ))) := by
  simp [erdos_878.parts.i]

/- A fixed positive lower bound for the normalized `F` value is exactly what the official
   first question needs.  This bridge uses `isBigOWith_inv` and keeps the scale positivity
   explicit, so no hidden division-by-zero convention enters the Big-O conclusion. -/
theorem proposed_first_question_fixed_loss_of_components
    (A : Set ℕ) (hA : A.HasDensity 1)
    (hf : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    {κ : ℝ} (hκ : 0 < κ)
    (hscale : ∀ᶠ n : A in atTop, 0 < scale (n : ℕ))
    (hF : ∀ᶠ n : A in atTop,
      κ ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ)) :
    erdos_878.parts.i := by
  apply proposed_first_question_fixed_loss_iff.mpr
  refine ⟨A, hA, hf, ?_⟩
  have hwith : IsBigOWith κ⁻¹ atTop
      (fun n : A ↦ scale (n : ℕ)) (fun n : A ↦ (F (n : ℕ) : ℝ)) := by
    apply (isBigOWith_inv hκ).2
    filter_upwards [hscale, hF] with n hn hFn
    have hmul : κ * scale (n : ℕ) ≤ (F (n : ℕ) : ℝ) :=
      (le_div_iff₀ hn).mp hFn
    simpa [Real.norm_eq_abs, abs_of_pos hn, abs_of_nonneg (by positivity :
      0 ≤ (F (n : ℕ) : ℝ))] using hmul
  exact hwith.isBigO

theorem second_question_iff :
    erdos_878.parts.ii ↔
      Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / maximalOrderScale x) atTop (𝓝 1) := by
  simp [erdos_878.parts.ii, maximalOrderScale]

theorem proposed_original_formula_17_sharp_iff :
    erdos_878.variants.proposed_original_formula_17_sharp ↔
      (1 : ℝ) ≤ atTop.liminf (fun x : ℕ ↦
        (maximalOrderGap x : ℝ) / maximalOrderGapScale x) := by
  simp [erdos_878.variants.proposed_original_formula_17_sharp]

theorem original_formula_17_iff :
    erdos_878.variants.original_formula_17 ↔
      Tendsto (fun x : ℕ ↦
        (maximalOrderGap x : ℝ) / (x : ℝ)) atTop atTop := by
  simp [erdos_878.variants.original_formula_17]

/- Exact constructor for the natural-language Remarks variant. -/
theorem proposed_first_question_sharp_of_F_witness
    (h : ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦ (F n : ℝ) / scale n) atTop (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp :=
  proposed_first_question_sharp_iff.mpr h

/- Backwards-compatible stronger constructor.  Some combined Track-A wrappers also carry the
   independent `f=o(scale)` certificate needed for `parts.i`; it is intentionally discarded when
   packaging the Remarks variant. -/
theorem proposed_first_question_sharp_of_witness
    (h : ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop] (fun n : A ↦ scale n) ∧
      Tendsto (fun n : A ↦ (F n : ℝ) / scale n) atTop (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp := by
  rcases h with ⟨A, hA, _hf, hF⟩
  exact proposed_first_question_sharp_of_F_witness ⟨A, hA, hF⟩

theorem proposed_first_question_sharp_of_component_inputs
    (A : Set ℕ) (hA : A.HasDensity 1)
    (hf : (fun n : A ↦ (f n : ℝ)) =o[atTop] (fun n : A ↦ scale n))
    (hF : Tendsto (fun n : A ↦ (F n : ℝ) / scale n) atTop (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp :=
  proposed_first_question_sharp_of_witness ⟨A, hA, hf, hF⟩

/- Fully assembled Track-A entry point on a density-one set.  The only inputs left for the
   number-theoretic proof are the four explicit component hypotheses consumed by
   `tendsto_F_div_scale_on_set`; this theorem performs the final target packaging. -/
theorem proposed_first_question_sharp_of_set_components
    (A : Set ℕ) (hA : A.HasDensity 1)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hlower : ∀ᶠ n : A in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (hf : Tendsto (fun n : A ↦ (f (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 0))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  apply proposed_first_question_sharp_of_component_inputs A hA hfSmall
  exact tendsto_F_div_scale_on_set hlarge hloglog hlower hf homega hscale

/- Public Track-A wrapper in the natural analytic language: instead of postulating the eventual
   lower bound for `F` itself, the caller supplies a moving prime window and proves that the
   reciprocal mass of its divisors is at least half the normalized scale. -/
theorem proposed_first_question_sharp_of_prime_window_mass_lower
    (A : Set ℕ) (hA : A.HasDensity 1) (R : A → Finset ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hmass : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ∑ p ∈ (R n).filter (fun p ↦ p ∣ (n : ℕ)), ((p : ℝ)⁻¹))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  apply proposed_first_question_sharp_of_component_inputs A hA hfSmall
  exact tendsto_F_div_scale_on_set_of_prime_window_mass_lower R hlarge hloglog hprime
    hmass hfSmall.tendsto_div_nhds_zero homega hscale

/- Public cardinality/Hall variant of the moving-window wrapper.  This is the form to use when
   the analytic proof returns `K/U` from a second-moment estimate instead of a reciprocal-mass
   inequality. -/
theorem proposed_first_question_sharp_of_prime_window_card_lower
    (A : Set ℕ) (hA : A.HasDensity 1) (R : A → Finset ℕ) (U : A → ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hprime : ∀ n : A, ∀ p ∈ R n, p.Prime)
    (hU : ∀ᶠ n : A in atTop, 0 < U n)
    (hupper : ∀ᶠ n : A in atTop, ∀ p ∈ R n, p ≤ U n)
    (hcard : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ((R n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U n : ℝ))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  apply proposed_first_question_sharp_of_component_inputs A hA hfSmall
  exact tendsto_F_div_scale_on_set_of_prime_window_card_lower R U hlarge hloglog hprime hU
    hupper hcard hfSmall.tendsto_div_nhds_zero homega hscale

/- Public two-window/Hall variant.  Use this when the reciprocal-mass certificate is split over
   two disjoint prime windows, so that the analytic input supplies an additive `K₁/U₁ + K₂/U₂`
   lower bound. -/
theorem proposed_first_question_sharp_of_two_prime_window_card_lower
    (A : Set ℕ) (hA : A.HasDensity 1)
    (R₁ R₂ : A → Finset ℕ) (U₁ U₂ : A → ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hdisj : ∀ n : A, Disjoint (R₁ n) (R₂ n))
    (hprime₁ : ∀ n : A, ∀ p ∈ R₁ n, p.Prime)
    (hprime₂ : ∀ n : A, ∀ p ∈ R₂ n, p.Prime)
    (hU₁ : ∀ᶠ n : A in atTop, 0 < U₁ n)
    (hU₂ : ∀ᶠ n : A in atTop, 0 < U₂ n)
    (hupper₁ : ∀ᶠ n : A in atTop, ∀ p ∈ R₁ n, p ≤ U₁ n)
    (hupper₂ : ∀ᶠ n : A in atTop, ∀ p ∈ R₂ n, p ≤ U₂ n)
    (hcard : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        ((R₁ n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U₁ n : ℝ) +
          ((R₂ n).filter (fun p ↦ p ∣ (n : ℕ))).card / (U₂ n : ℝ))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  apply proposed_first_question_sharp_of_component_inputs A hA hfSmall
  exact tendsto_F_div_scale_on_set_of_two_prime_window_card_lower R₁ R₂ U₁ U₂
    hlarge hloglog hdisj hprime₁ hprime₂ hU₁ hU₂ hupper₁ hupper₂ hcard
    hfSmall.tendsto_div_nhds_zero homega hscale

/- The same two-window wrapper in the `divisorCount` language used by the second-moment
   development.  The conversion is definitional, but keeping it here avoids forcing callers to
   unfold the filtered-cardinality implementation of `divisorCount`. -/
theorem proposed_first_question_sharp_of_two_prime_window_divisorCount_lower
    (A : Set ℕ) (hA : A.HasDensity 1)
    (R₁ R₂ : A → Finset ℕ) (U₁ U₂ : A → ℕ)
    (hlarge : ∀ᶠ n : A in atTop, 1 < (n : ℕ))
    (hloglog : ∀ᶠ n : A in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)))
    (hdisj : ∀ n : A, Disjoint (R₁ n) (R₂ n))
    (hprime₁ : ∀ n : A, ∀ p ∈ R₁ n, p.Prime)
    (hprime₂ : ∀ n : A, ∀ p ∈ R₂ n, p.Prime)
    (hU₁ : ∀ᶠ n : A in atTop, 0 < U₁ n)
    (hU₂ : ∀ᶠ n : A in atTop, 0 < U₂ n)
    (hupper₁ : ∀ᶠ n : A in atTop, ∀ p ∈ R₁ n, p ≤ U₁ n)
    (hupper₂ : ∀ᶠ n : A in atTop, ∀ p ∈ R₂ n, p ≤ U₂ n)
    (hcount : ∀ᶠ n : A in atTop,
      scale (n : ℕ) / (2 * ((n : ℕ) : ℝ)) ≤
        divisorCount (R₁ n) (n : ℕ) / (U₁ n : ℝ) +
          divisorCount (R₂ n) (n : ℕ) / (U₂ n : ℝ))
    (hfSmall : (fun n : A ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : A ↦ scale (n : ℕ)))
    (homega : Tendsto (fun n : A ↦
      (omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)))
      atTop (𝓝 1))
    (hscale : Tendsto (fun n : A ↦ 1 / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  apply proposed_first_question_sharp_of_component_inputs A hA hfSmall
  apply tendsto_F_div_scale_on_set_of_two_prime_window_card_lower
    R₁ R₂ U₁ U₂ hlarge hloglog hdisj hprime₁ hprime₂ hU₁ hU₂
    hupper₁ hupper₂
  · simpa [divisorCount] using hcount
  · exact hfSmall.tendsto_div_nhds_zero
  · exact homega
  · exact hscale

theorem proposed_first_question_sharp_of_exceptional_set
    (S : Set ℕ) (hS : S.HasDensity 0)
    (hf : (fun n : (Sᶜ : Set ℕ) ↦ (f n : ℝ)) =o[atTop]
      (fun n : (Sᶜ : Set ℕ) ↦ scale n))
    (hF : Tendsto (fun n : (Sᶜ : Set ℕ) ↦ (F n : ℝ) / scale n) atTop
      (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp :=
  proposed_first_question_sharp_of_component_inputs (Sᶜ : Set ℕ)
    (compl_hasDensity_one_of_hasDensity_zero hS) hf hF

/- Direct f-side completion wrappers.  Once the source-style H upper bound is supplied, the
   moving-threshold theorem above provides the density-one little-o component automatically; the
   only remaining input is the F-side lower/asymptotic estimate. -/
theorem proposed_first_question_sharp_of_H_and_F
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))))
    (hF : Tendsto (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp := by
  have hS0 : fSqrtBadSet.HasDensity 0 :=
    fSqrtBadSet_hasDensity_zero_of_H_logloglog hHupper
  have hA : (fSqrtBadSetᶜ : Set ℕ).HasDensity 1 :=
    compl_hasDensity_one_of_hasDensity_zero hS0
  have hfSmall := fSqrtBadSet_compl_f_div_scale_littleO_of_H_logloglog hHupper
  exact proposed_first_question_sharp_of_component_inputs
    (fSqrtBadSetᶜ : Set ℕ) hA hfSmall hF

/- Since the global source bound is now proved from the local blocks, the public first-question
   wrapper can expose only the genuinely missing `F`-side limit. -/
theorem proposed_first_question_sharp_of_source_blocks_and_F
    (hF : Tendsto (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp := by
  rcases exists_global_summatory_f_div_Icc_le_source_logloglog with
    ⟨C, hC, hHupper⟩
  exact proposed_first_question_sharp_of_H_and_F hHupper hF

theorem proposed_first_question_fixed_loss_of_H_and_F
    {C κ : ℝ} (hκ : 0 < κ)
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))))
    (hF : ∀ᶠ n : (fSqrtBadSetᶜ : Set ℕ) in atTop,
      κ ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ)) :
    erdos_878.parts.i := by
  have hS0 : fSqrtBadSet.HasDensity 0 :=
    fSqrtBadSet_hasDensity_zero_of_H_logloglog hHupper
  have hA : (fSqrtBadSetᶜ : Set ℕ).HasDensity 1 :=
    compl_hasDensity_one_of_hasDensity_zero hS0
  have hInf : (fSqrtBadSetᶜ : Set ℕ).Infinite :=
    Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, haA, hab⟩ := Set.Infinite.exists_gt hInf b
    filter_upwards [eventually_ge_atTop (⟨a, haA⟩ : (fSqrtBadSetᶜ : Set ℕ))] with n hn
    exact hab.le.trans (show a ≤ (n : ℕ) from hn)
  have hscale : ∀ᶠ n : (fSqrtBadSetᶜ : Set ℕ) in atTop, 0 < scale (n : ℕ) := by
    have hlarge : ∀ᶠ n : (fSqrtBadSetᶜ : Set ℕ) in atTop, 1 < (n : ℕ) :=
      hcoe.eventually (eventually_gt_atTop (1 : ℕ))
    have hlog : ∀ᶠ n : (fSqrtBadSetᶜ : Set ℕ) in atTop,
        0 < Real.log (Real.log ((n : ℕ) : ℝ)) := by
      have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
        (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
          tendsto_natCast_atTop_atTop
      exact (hll.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hlarge, hlog] with n hn hln
    unfold scale
    exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < (n : ℕ)))) hln
  have hf := fSqrtBadSet_compl_f_div_scale_littleO_of_H_logloglog hHupper
  exact proposed_first_question_fixed_loss_of_components
    (fSqrtBadSetᶜ : Set ℕ) hA hf hκ hscale hF

/- Cofinality of the natural maps from an intersection subtype to either factor.  This permits
   independently obtained density-one certificates to be restricted to their intersection. -/
theorem tendsto_inter_subtype_to_left
    {S T : Set ℕ} (hI : (S ∩ T).Infinite) :
    Tendsto (fun n : ↥(S ∩ T) ↦ (⟨(n : ℕ), n.property.1⟩ : S)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hI (b : ℕ)
  let aI : ↥(S ∩ T) := ⟨a, ha⟩
  filter_upwards [eventually_ge_atTop aI] with n hn
  have hbn : (b : ℕ) ≤ (n : ℕ) :=
    (Nat.le_of_lt hba).trans (show a ≤ (n : ℕ) from hn)
  exact hbn

theorem tendsto_inter_subtype_to_right
    {S T : Set ℕ} (hI : (S ∩ T).Infinite) :
    Tendsto (fun n : ↥(S ∩ T) ↦ (⟨(n : ℕ), n.property.2⟩ : T)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hI (b : ℕ)
  let aI : ↥(S ∩ T) := ⟨a, ha⟩
  filter_upwards [eventually_ge_atTop aI] with n hn
  have hbn : (b : ℕ) ≤ (n : ℕ) :=
    (Nat.le_of_lt hba).trans (show a ≤ (n : ℕ) from hn)
  exact hbn

/- Historical fixed-loss closure. The moment assumptions below have been proved inconsistent in
   `Erdos878.CertificateAudit`; they must not be treated as a remaining analytic obligation. -/
theorem proposed_first_question_fixed_loss_of_source_blocks_and_weighted_moments
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0)) :
    erdos_878.parts.i := by
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with
    ⟨S, hS, hfS⟩
  rcases exists_density_one_F_lower_of_weightedScale_moment_bounds
      R w V hprime hweight hvar hvanish with ⟨T, hT, hFT⟩
  let I : Set ℕ := S ∩ T
  have hI : I.HasDensity 1 := by
    simpa [I] using hasDensity_one_inter_of_hasDensity_one hS hT
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hcoe : Tendsto (fun n : ↥I ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hIinf b
    let aI : ↥I := ⟨a, ha⟩
    filter_upwards [eventually_ge_atTop aI] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hfI : (fun n : ↥I ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : ↥I ↦ scale (n : ℕ)) := by
    have hmap := tendsto_inter_subtype_to_left (S := S) (T := T) hIinf
    simpa [Function.comp_def] using hfS.comp_tendsto hmap
  have hFI : ∀ᶠ n : ↥I in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    have hmap := tendsto_inter_subtype_to_right (S := S) (T := T) hIinf
    filter_upwards [hmap.eventually hFT] with n hn
    change (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) at hn
    exact hn
  have hscaleI : ∀ᶠ n : ↥I in atTop, 0 < scale (n : ℕ) :=
    hcoe.eventually eventually_scale_pos
  exact proposed_first_question_fixed_loss_of_components I hI hfI
    (by norm_num) hscaleI hFI

/- Historical sharp closure with two infeasible inputs: the prefix moment package is inconsistent,
   and the all-natural-number `homega` limit is false. Classical normal order holds only after
   restricting to a density-one set. See `Erdos878.CertificateAudit` for the moment obstruction. -/
theorem proposed_first_question_sharp_of_source_blocks_and_weighted_moments_and_omega
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0))
    (homega : Tendsto (fun n : ℕ ↦
      (omega n : ℝ) / Real.log (Real.log (n : ℝ))) atTop (𝓝 1)) :
    erdos_878.variants.proposed_first_question_sharp := by
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with
    ⟨S, hS, hfS⟩
  rcases exists_density_one_F_lower_of_weightedScale_moment_bounds
      R w V hprime hweight hvar hvanish with ⟨T, hT, hFT⟩
  let I : Set ℕ := S ∩ T
  have hI : I.HasDensity 1 := by
    simpa [I] using hasDensity_one_inter_of_hasDensity_one hS hT
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hcoe : Tendsto (fun n : ↥I ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hIinf b
    let aI : ↥I := ⟨a, ha⟩
    filter_upwards [eventually_ge_atTop aI] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hfI : (fun n : ↥I ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : ↥I ↦ scale (n : ℕ)) := by
    have hmap := tendsto_inter_subtype_to_left (S := S) (T := T) hIinf
    simpa [Function.comp_def] using hfS.comp_tendsto hmap
  have hFI : ∀ᶠ n : ↥I in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    have hmap := tendsto_inter_subtype_to_right (S := S) (T := T) hIinf
    filter_upwards [hmap.eventually hFT] with n hn
    change (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) at hn
    exact hn
  have hlarge : ∀ᶠ n : ↥I in atTop, 1 < (n : ℕ) :=
    hcoe.eventually (eventually_gt_atTop (1 : ℕ))
  have hloglogNat : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ))) atTop atTop := by
    exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hloglogI : ∀ᶠ n : ↥I in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)) := by
    exact (hloglogNat.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))
  have hfRatio : Tendsto (fun n : ↥I ↦
      (f (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 0) :=
    hfI.tendsto_div_nhds_zero
  have homegaI : Tendsto (fun n : ↥I ↦
      (omega (n : ℕ) : ℝ) /
        Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using homega.comp hcoe
  have hscaleI : Tendsto (fun n : ↥I ↦ 1 / scale (n : ℕ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_scale_zero.comp hcoe
  have hF : Tendsto (fun n : ↥I ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    exact tendsto_F_div_scale_on_set hlarge hloglogI hFI hfRatio homegaI hscaleI
  exact proposed_first_question_sharp_of_component_inputs I hI hfI hF

/- Historical density-one normal-order variant. It fixes the domain of the normal-order limit,
   but the prefix-weighted moment assumptions remain inconsistent. See
   `proposed_first_question_sharp_of_matching_deficits` in module `Erdos878.MatchingAsymptotic`
   for the corrected construction using actual admissible product terms. -/
theorem proposed_first_question_sharp_of_source_blocks_and_weighted_moments_and_density_one_omega
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X : ℕ, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Icc 1 X,
        ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧
          w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Finset.Icc 1 X,
        (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X)
    (hvanish : Tendsto (fun X : ℕ ↦ 4 * V X /
      (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0))
    (U : Set ℕ) (hU : U.HasDensity 1)
    (hωU : Tendsto (fun n : U ↦
      (omega (n : ℕ) : ℝ) /
        Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1)) :
    erdos_878.variants.proposed_first_question_sharp := by
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with
    ⟨S, hS, hfS⟩
  rcases exists_density_one_F_lower_of_weightedScale_moment_bounds
      R w V hprime hweight hvar hvanish with ⟨T, hT, hFT⟩
  let I : Set ℕ := S ∩ T
  have hI : I.HasDensity 1 := by
    simpa [I] using hasDensity_one_inter_of_hasDensity_one hS hT
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  let J : Set ℕ := I ∩ U
  have hJ : J.HasDensity 1 := by
    simpa [J] using hasDensity_one_inter_of_hasDensity_one hI hU
  have hJinf : J.Infinite := Nat.infinite_of_hasDensity_pos hJ (by norm_num)
  have hcoe : Tendsto (fun n : ↥J ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hJinf b
    let aJ : ↥J := ⟨a, ha⟩
    filter_upwards [eventually_ge_atTop aJ] with n hn
    exact hba.le.trans (show a ≤ (n : ℕ) from hn)
  have hmapJI : Tendsto (fun n : ↥J ↦
      (⟨(n : ℕ), n.property.1⟩ : I)) atTop atTop :=
    tendsto_inter_subtype_to_left (S := I) (T := U) hJinf
  have hmapJU : Tendsto (fun n : ↥J ↦
      (⟨(n : ℕ), n.property.2⟩ : U)) atTop atTop :=
    tendsto_inter_subtype_to_right (S := I) (T := U) hJinf
  have hmapIS : Tendsto (fun n : ↥I ↦
      (⟨(n : ℕ), n.property.1⟩ : S)) atTop atTop :=
    tendsto_inter_subtype_to_left (S := S) (T := T) hIinf
  have hmapIT : Tendsto (fun n : ↥I ↦
      (⟨(n : ℕ), n.property.2⟩ : T)) atTop atTop :=
    tendsto_inter_subtype_to_right (S := S) (T := T) hIinf
  have hfJ : (fun n : ↥J ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : ↥J ↦ scale (n : ℕ)) := by
    have hmap : Tendsto (fun n : ↥J ↦
        (⟨(n : ℕ), n.property.1.1⟩ : S)) atTop atTop := by
      exact hmapIS.comp hmapJI
    simpa [Function.comp_def] using hfS.comp_tendsto hmap
  have hFJ : ∀ᶠ n : ↥J in atTop,
      (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    have hmap : Tendsto (fun n : ↥J ↦
        (⟨(n : ℕ), n.property.1.2⟩ : T)) atTop atTop := by
      exact hmapIT.comp hmapJI
    filter_upwards [hmap.eventually hFT] with n hn
    change (1 / 2 : ℝ) ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) at hn
    exact hn
  have hlarge : ∀ᶠ n : ↥J in atTop, 1 < (n : ℕ) :=
    hcoe.eventually (eventually_gt_atTop (1 : ℕ))
  have hloglogNat : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ))) atTop atTop := by
    exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hloglogJ : ∀ᶠ n : ↥J in atTop,
      0 < Real.log (Real.log ((n : ℕ) : ℝ)) := by
    exact (hloglogNat.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))
  have hfRatio : Tendsto (fun n : ↥J ↦
      (f (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 0) :=
    hfJ.tendsto_div_nhds_zero
  have hωJ : Tendsto (fun n : ↥J ↦
      (omega (n : ℕ) : ℝ) /
        Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1) := by
    have hmap : Tendsto (fun n : ↥J ↦
        (⟨(n : ℕ), n.property.2⟩ : U)) atTop atTop := hmapJU
    simpa [Function.comp_def] using hωU.comp hmap
  have hscaleJ : Tendsto (fun n : ↥J ↦ 1 / scale (n : ℕ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_scale_zero.comp hcoe
  have hF : Tendsto (fun n : ↥J ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    exact tendsto_F_div_scale_on_set hlarge hloglogJ hFJ hfRatio hωJ hscaleJ
  exact proposed_first_question_sharp_of_component_inputs J hJ hfJ hF

/- Final packaging when the exceptional set is controlled by endpoint finite filters.  This is
the form produced by a moving-window proof: the analytic work supplies `hcover` and `hbound`,
while the two component limits on the complement are passed unchanged to the existing squeeze. -/
theorem proposed_first_question_sharp_of_Icc_exceptional_cover
    (S : Set ℕ) (E : ℕ → Finset ℕ)
    (hcover : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆ (E X : Set ℕ))
    (hbound : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ)) atTop (𝓝 0))
    (hf : (fun n : (Sᶜ : Set ℕ) ↦ (f n : ℝ)) =o[atTop]
      (fun n : (Sᶜ : Set ℕ) ↦ scale n))
    (hF : Tendsto (fun n : (Sᶜ : Set ℕ) ↦ (F n : ℝ) / scale n) atTop
      (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp := by
 exact proposed_first_question_sharp_of_exceptional_set S
   (hasDensity_zero_of_Icc_filter_cover S E hcover hbound) hf hF

/- Fully assembled Track-A endpoint for two prime windows.  The density bookkeeping is now
   discharged by the sharp two-window reciprocal-mass wrapper; the remaining inputs are the
   window-cover construction, reciprocal-mass divergence, and the complement-side limits. -/
theorem proposed_first_question_sharp_of_two_prime_windows
    (S : Set ℕ) (R₁ R₂ : ℕ → Finset ℕ)
    (hcover : ∀ X : ℕ,
      S ∩ Set.Icc 1 X ⊆
        (↑(((Finset.Icc 1 X).filter
            (fun n ↦ divisorCount (R₁ X) n <
              (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
          (Finset.Icc 1 X).filter
            (fun n ↦ divisorCount (R₂ X) n <
              (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)) : Set ℕ))
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hsub₁ : ∀ X : ℕ, R₁ X ⊆ Finset.Icc 1 X)
    (hsub₂ : ∀ X : ℕ, R₂ X ⊆ Finset.Icc 1 X)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hinvμ₁ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₁ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hinvμ₂ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₂ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hf : (fun n : (Sᶜ : Set ℕ) ↦ (f n : ℝ)) =o[atTop]
      (fun n : (Sᶜ : Set ℕ) ↦ scale n))
    (hF : Tendsto (fun n : (Sᶜ : Set ℕ) ↦ (F n : ℝ) / scale n) atTop
      (𝓝 (1 / 2 : ℝ))) :
    erdos_878.variants.proposed_first_question_sharp := by
  let E : ℕ → Finset ℕ := fun X ↦
    ((Finset.Icc 1 X).filter
      (fun n ↦ divisorCount (R₁ X) n <
        (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
      (Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R₂ X) n <
          (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)
  have hcoverE : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆ (E X : Set ℕ) := by
    intro X
    simpa [E] using hcover X
  have hboundE : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    simpa [E] using
      (tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
        R₁ R₂ hprime₁ hprime₂ hsub₁ hsub₂ hμ₁ hμ₂ hinvμ₁ hinvμ₂)
  exact proposed_first_question_sharp_of_Icc_exceptional_cover
    S E hcoverE hboundE hf hF

/- Fixed-loss counterpart of the preceding two-window package.  The exceptional-set bookkeeping
   is identical, but the complement-side lower bound only needs one fixed positive `κ`; this is
   the exact official first-question target and deliberately does not demand the coefficient `1/2`
   limit. -/
theorem proposed_first_question_fixed_loss_of_two_prime_windows
    (S : Set ℕ) (R₁ R₂ : ℕ → Finset ℕ)
    (hcover : ∀ X : ℕ,
      S ∩ Set.Icc 1 X ⊆
        (↑(((Finset.Icc 1 X).filter
            (fun n ↦ divisorCount (R₁ X) n <
              (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
          (Finset.Icc 1 X).filter
            (fun n ↦ divisorCount (R₂ X) n <
              (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)) : Set ℕ))
    (hprime₁ : ∀ X : ℕ, ∀ p ∈ R₁ X, p.Prime)
    (hprime₂ : ∀ X : ℕ, ∀ p ∈ R₂ X, p.Prime)
    (hsub₁ : ∀ X : ℕ, R₁ X ⊆ Finset.Icc 1 X)
    (hsub₂ : ∀ X : ℕ, R₂ X ⊆ Finset.Icc 1 X)
    (hμ₁ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₁ X, ((p : ℝ)⁻¹))
    (hμ₂ : ∀ᶠ X : ℕ in atTop, 0 < ∑ p ∈ R₂ X, ((p : ℝ)⁻¹))
    (hinvμ₁ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₁ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    (hinvμ₂ : Tendsto (fun X : ℕ ↦
      (∑ p ∈ R₂ X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0))
    {κ : ℝ} (hκ : 0 < κ)
    (hscale : ∀ᶠ n : (Sᶜ : Set ℕ) in atTop, 0 < scale (n : ℕ))
    (hF : ∀ᶠ n : (Sᶜ : Set ℕ) in atTop,
      κ ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ))
    (hf : (fun n : (Sᶜ : Set ℕ) ↦ (f n : ℝ)) =o[atTop]
      (fun n : (Sᶜ : Set ℕ) ↦ scale n)) :
    erdos_878.parts.i := by
  let E : ℕ → Finset ℕ := fun X ↦
    ((Finset.Icc 1 X).filter
      (fun n ↦ divisorCount (R₁ X) n <
        (∑ p ∈ R₁ X, ((p : ℝ)⁻¹)) / 2)) ∪
      (Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (R₂ X) n <
          (∑ p ∈ R₂ X, ((p : ℝ)⁻¹)) / 2)
  have hcoverE : ∀ X : ℕ, S ∩ Set.Icc 1 X ⊆ (E X : Set ℕ) := by
    intro X
    simpa [E] using hcover X
  have hboundE : Tendsto (fun X : ℕ ↦ ((E X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    simpa [E] using
      (tendsto_divisorCount_union_two_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
        R₁ R₂ hprime₁ hprime₂ hsub₁ hsub₂ hμ₁ hμ₂ hinvμ₁ hinvμ₂)
  have hS0 : S.HasDensity 0 := hasDensity_zero_of_Icc_filter_cover S E hcoverE hboundE
  exact proposed_first_question_fixed_loss_of_components (Sᶜ : Set ℕ)
    (compl_hasDensity_one_of_hasDensity_zero hS0) hf hκ hscale hF

theorem second_question_of_selected_primes
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ) (B : ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        (∀ p ∈ S, B ≤ p ^ Nat.log p (multipleBelow X S)) ∧
        1 - ε ≤ ((S.card : ℝ) * (B : ℝ)) / maximalOrderScale X) :
    erdos_878.parts.ii :=
  second_question_iff.mpr
    (tendsto_maximalOrder_of_selected_primes hselect)

/- Public FC-target wrapper for the sum-valued Track-B selection interface. -/
theorem second_question_of_selected_prime_power_sums
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
            maximalOrderScale X) :
    erdos_878.parts.ii :=
  second_question_iff.mpr
    (tendsto_maximalOrder_of_selected_prime_power_sums hselect)

/- Historical reciprocal-mass adapter. Its selection hypothesis is impossible: the normalized
   reciprocal mass is eventually at most `3/4`, uniformly in every eligible prime set.
   `not_selected_reciprocal_mass_certificate` in `Erdos878.CertificateAudit` proves this obstruction.
   The actual prime-power-sum interface above remains the relevant Track-B route. -/
theorem second_question_of_selected_reciprocal_mass
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          ((multipleBelow X S : ℕ) : ℝ) *
              (∑ p ∈ S, ((p : ℝ)⁻¹)) /
            maximalOrderScale X) :
    erdos_878.parts.ii := by
  apply second_question_iff.mpr
  apply tendsto_maximalOrder_of_eventually_one_sub_le
  intro ε hε
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscalePos : ∀ᶠ X : ℕ in atTop, 0 < maximalOrderScale X := by
    filter_upwards [hlogNat.eventually (eventually_gt_atTop (1 : ℝ))] with X hlog
    have hx : 1 < (X : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans hlog)
    unfold maximalOrderScale
    exact div_pos (mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hlog))
      (Real.log_pos hlog)
  filter_upwards [hselect ε hε, hscalePos] with X hdata hscale
  rcases hdata with ⟨S, hprime, hprod, hnormalized⟩
  have hnat :
      (multipleBelow X S : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤
        (maxUpTo f X : ℝ) := by
    exact reciprocalPrimeMass_mul_le_maxUpTo_f_of_selected_primes S hprime hprod
  have hquot :
      ((multipleBelow X S : ℕ) : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) /
          maximalOrderScale X ≤
        (maxUpTo f X : ℝ) / maximalOrderScale X := by
    exact div_le_div_of_nonneg_right hnat (le_of_lt hscale)
  exact hnormalized.trans hquot

/- Public source-sequence adapter.  The paper's known maximal-order result is naturally stated
   on a sequence of selected endpoints rather than for every endpoint.  Once that sequence limit
   is imported, only the explicit mesh and adjacent-endpoint ratio certificates remain before the
   ordinary-limit FC target is discharged. -/
theorem second_question_of_subsequence_limit_and_subsequence_cover
    (Xseq : ℕ → ℕ) (hXseq : Tendsto Xseq atTop atTop)
    (hseq : Tendsto (fun k : ℕ ↦
      (maxUpTo f (Xseq k) : ℝ) / maximalOrderScale (Xseq k)) atTop (𝓝 1))
    (hcover : ∀ K : ℕ, ∀ᶠ x : ℕ in atTop,
      ∃ k : ℕ, K ≤ k ∧ Xseq k ≤ x ∧ x ≤ Xseq (k + 1))
    (hendpoint_ratio : Tendsto (fun k : ℕ ↦
      (Xseq (k + 1) : ℝ) / (Xseq k : ℝ)) atTop (𝓝 1)) :
    erdos_878.parts.ii :=
  second_question_iff.mpr
    (tendsto_maximalOrder_of_subsequence_limit_and_subsequence_cover
      Xseq hXseq hseq hcover hendpoint_ratio)

theorem proposed_original_formula_17_sharp_of_bound
    (hbound : (1 : ℝ) ≤ atTop.liminf (fun x : ℕ ↦
      (maximalOrderGap x : ℝ) / maximalOrderGapScale x)) :
    erdos_878.variants.proposed_original_formula_17_sharp :=
  proposed_original_formula_17_sharp_iff.mpr hbound

theorem original_formula_17_of_bound
    (hbound : Tendsto (fun x : ℕ ↦
      (maximalOrderGap x : ℝ) / (x : ℝ)) atTop atTop) :
    erdos_878.variants.original_formula_17 :=
  original_formula_17_iff.mpr hbound

/- A certificate-level Track-C closure.  It is enough to exhibit, for every large `x`, an
   attainer of `m x` for which either the divisor-count deficit or (in the equality branch) the
   endpoint distance is at least a quantity `K x → ∞`.  The two finite dichotomy lemmas above then
   give `x * K x ≤ x*h(x)-m(x)`, and division by `x` proves the original formula (17). -/
theorem original_formula_17_of_eventually_attainer_gap_certificate
    (K : ℕ → ℕ)
    (hK : Tendsto (fun x : ℕ ↦ (K x : ℝ)) atTop atTop)
    (hcert : ∀ᶠ x : ℕ in atTop,
      ∃ n ≤ x, n ≠ 0 ∧ m x = f n ∧
        (K x ≤ h x - omega n ∨
          (omega n = h x ∧ x * K x ≤ h x * (x - n)))) :
    erdos_878.variants.original_formula_17 := by
  have hgap : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * (K x : ℝ) ≤ (maximalOrderGap x : ℝ) := by
    filter_upwards [hcert] with x hdata
    rcases hdata with ⟨n, hnx, hn0, hattain, hbranch⟩
    have hnat : x * K x ≤ x * h x - m x := by
      rcases hbranch with hdef | hend
      · exact maximalOrderGap_ge_mul_of_attainer_of_omega_gap hnx hn0 hattain hdef
      · have hdist : h x * (x - n) ≤ x * h x - m x :=
          maximalOrderGap_ge_mul_of_attainer_of_omega_eq_endpoint_gap
            hnx hn0 hattain hend.1 (le_refl _)
        exact hend.2.trans hdist
    have hcast : ((x * K x : ℕ) : ℝ) ≤ ((maximalOrderGap x : ℕ) : ℝ) := by
      exact_mod_cast (show (x * K x : ℕ) ≤ maximalOrderGap x from hnat)
    simpa [maximalOrderGap, Nat.cast_mul] using hcast
  have hxpos : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    exact_mod_cast hx
  have hratio : ∀ᶠ x : ℕ in atTop,
      (K x : ℝ) ≤ (maximalOrderGap x : ℝ) / (x : ℝ) := by
    filter_upwards [hgap, hxpos] with x hgx hx
    apply (le_div_iff₀ hx).2
    simpa [mul_comm] using hgx
  exact original_formula_17_of_bound
    (Filter.tendsto_atTop_mono' atTop hratio hK)

/- Direct endpoint-surplus version of the preceding Track-C closure.  Here the certificate keeps
   the actual number `K(x)` of deficient prime factors and the per-factor deficit `B(x)` instead
   of forcing their product into an integer-valued auxiliary function. -/
theorem original_formula_17_of_eventually_attainer_endpoint_surplus_certificate
    (K B : ℕ → ℕ)
    (hKB : Tendsto (fun x : ℕ ↦
      ((K x * B x : ℕ) : ℝ) / (x : ℝ)) atTop atTop)
    (hcert : ∀ᶠ x : ℕ in atTop,
      ∃ n ≤ x, n ≠ 0 ∧ m x = f n ∧ omega n = h x ∧
        K x ≤ (n.primeFactors.filter
          (fun p ↦ B x ≤ n - p ^ Nat.log p n)).card) :
    erdos_878.variants.original_formula_17 := by
  have hgap : ∀ᶠ x : ℕ in atTop,
      ((K x * B x : ℕ) : ℝ) ≤ (maximalOrderGap x : ℝ) := by
    filter_upwards [hcert] with x hdata
    rcases hdata with ⟨n, hnx, hn0, hattain, heq, hcount⟩
    have hnat : K x * B x ≤ x * h x - m x :=
      maximalOrderGap_ge_mul_of_attainer_of_endpoint_surplus_count
        hnx hn0 hattain heq hcount
    exact_mod_cast (show (K x * B x : ℕ) ≤ maximalOrderGap x from hnat)
  have hxpos : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    exact_mod_cast hx
  have hratio : ∀ᶠ x : ℕ in atTop,
      ((K x * B x : ℕ) : ℝ) / (x : ℝ) ≤
        (maximalOrderGap x : ℝ) / (x : ℝ) := by
    filter_upwards [hgap, hxpos] with x hprod hx
    exact (div_le_div_of_nonneg_right hprod (le_of_lt hx))
  exact original_formula_17_of_bound
    (Filter.tendsto_atTop_mono' atTop hratio hKB)

/- A monotone-transfer bridge for the exact source formula.  Once an endpoint-band argument gives
   the pointwise comparison `maximalOrderGapScale ≤ maximalOrderGap`, it is enough to prove that
   the proposed scale divided by `x` diverges.  This isolates the Track-C arithmetic from the
   still-missing endpoint-band estimate. -/
theorem original_formula_17_of_scale_lower
    (hscale : Tendsto (fun x : ℕ ↦
      maximalOrderGapScale x / (x : ℝ)) atTop atTop)
    (hbound : ∀ᶠ x : ℕ in atTop,
      maximalOrderGapScale x ≤ (maximalOrderGap x : ℝ)) :
    erdos_878.variants.original_formula_17 := by
  have hx : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    exact_mod_cast hx
  have hratio : ∀ᶠ x : ℕ in atTop,
      maximalOrderGapScale x / (x : ℝ) ≤
        (maximalOrderGap x : ℝ) / (x : ℝ) := by
    filter_upwards [hbound, hx] with x hs hx
    exact (div_le_div_of_nonneg_right hs (le_of_lt hx))
  exact original_formula_17_of_bound
    (Filter.tendsto_atTop_mono' atTop hratio hscale)

/- A ratio-form Track-C closure.  If the gap dominates its proposed scale eventually, then the
   scale-to-`x` divergence proved above transfers directly to the source formula (17). -/
theorem original_formula_17_of_eventually_gap_ratio_ge_one
    (hbound : ∀ᶠ x : ℕ in atTop,
      (1 : ℝ) ≤ (maximalOrderGap x : ℝ) / maximalOrderGapScale x) :
    erdos_878.variants.original_formula_17 := by
  have hscalePos := eventually_maximalOrderGapScale_pos
  have hscaleLower : ∀ᶠ x : ℕ in atTop,
      maximalOrderGapScale x ≤ (maximalOrderGap x : ℝ) := by
    filter_upwards [hbound, hscalePos] with x hx hscale
    have hmul := (le_div_iff₀ hscale).mp hx
    simpa using hmul
  exact original_formula_17_of_scale_lower
    tendsto_maximalOrderGapScale_div_self_atTop hscaleLower

/- One final certificate-level package for the three requested targets.  The theorem is deliberately
   conditional: it makes every remaining analytic obligation explicit (the summatory H upper
   bound and F lower limit for Track A, prime-power selection for Track B, and the gap divergence
   for formula (17)) while proving that no further Lean glue is needed once those certificates are
   supplied. -/
theorem all_three_targets_of_analytic_certificates
    {C : ℝ}
    (hHupper : ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / (n : ℝ)) ≤
        C * (X : ℝ) * Real.log (Real.log (Real.log (X : ℝ))))
    (hF : Tendsto (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)))
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
            maximalOrderScale X)
    (hgap : Tendsto (fun x : ℕ ↦
      (maximalOrderGap x : ℝ) / (x : ℝ)) atTop atTop) :
    erdos_878.variants.proposed_first_question_sharp ∧
      erdos_878.parts.ii ∧
      erdos_878.variants.original_formula_17 := by
  refine ⟨?_, ?_, ?_⟩
  · exact proposed_first_question_sharp_of_H_and_F hHupper hF
  · exact second_question_of_selected_prime_power_sums hselect
  · exact original_formula_17_of_bound hgap

/- The local dyadic argument already proves the source-scale summatory bound used by Track A.
   This wrapper therefore removes that now-internal certificate from the public three-target
   interface.  The remaining inputs are exactly the genuinely unresolved analytic certificates:
   the density-one lower limit for `F`, the selected prime-power sums for ordinary maximal order,
   and the gap divergence needed for formula (17). -/
theorem all_three_targets_of_source_blocks_and_analytic_certificates
    (hF : Tendsto (fun n : (fSqrtBadSetᶜ : Set ℕ) ↦
      (F (n : ℕ) : ℝ) / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)))
    (hselect : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∃ (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) ∧
        primeProduct S ≤ X ∧
        1 - ε ≤
          (∑ p ∈ S, ((p ^ Nat.log p (multipleBelow X S) : ℕ) : ℝ)) /
            maximalOrderScale X)
    (hgap : Tendsto (fun x : ℕ ↦
      (maximalOrderGap x : ℝ) / (x : ℝ)) atTop atTop) :
    erdos_878.variants.proposed_first_question_sharp ∧
      erdos_878.parts.ii ∧
      erdos_878.variants.original_formula_17 := by
  rcases exists_global_summatory_f_div_Icc_le_source_logloglog with
    ⟨C, hC, hHupper⟩
  exact all_three_targets_of_analytic_certificates hHupper hF hselect hgap

/- A convenient order-theoretic entry point for Track C: an eventual pointwise lower bound is
already enough for the proposed liminf inequality.  The missing endpoint-band estimate can thus
target this simple hypothesis directly. -/
theorem original_formula_17_sharp_of_eventually_ratio_ge_one
    (hbounded : IsCoboundedUnder (fun x y : ℝ ↦ x ≥ y) atTop
      (fun x : ℕ ↦ (maximalOrderGap x : ℝ) / maximalOrderGapScale x))
    (hbound : ∀ᶠ x : ℕ in atTop,
      (1 : ℝ) ≤ (maximalOrderGap x : ℝ) / maximalOrderGapScale x) :
    (1 : ℝ) ≤ atTop.liminf (fun x : ℕ ↦
      (maximalOrderGap x : ℝ) / maximalOrderGapScale x) := by
  exact le_liminf_of_le (hf := hbounded) (h := hbound)

end Erdos878

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license; see LICENSE at the publication package root.
Modified for Erdős 878: renamed definitions, simplified hypotheses, arbitrary-weight API.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Complex.BigOperators

/-!
# Track B: Vaughan's identity with arbitrary finite weights

This file supplies the first analytic component of the proposed all-endpoint lower bound for
Erdős 878(ii).  The important interface is `vaughan_weighted_sum`: its weight is an arbitrary
function `ℕ → ℂ`, so the later phase `exp (2π i a / log n)` can be inserted without rebuilding
the Dirichlet-convolution algebra.

The decomposition and its proof were adapted from
`AnalyticNT.Vaughan.Identity` in `gersh/ternary-goldbach-lean` (Apache-2.0, commit
`27df23af6a712895f22204d0d81102baa74f0ebe`).  We keep a small local version because that
repository's full analytic-number-theory package has several large local path dependencies and is
pinned to a different Mathlib release.  The present module needs only Mathlib.

No asymptotic estimate is claimed here.  This is the exact, finite algebraic decomposition which
the later Type-I/Type-II estimates consume.
-/

namespace Erdos878
namespace TrackB

open scoped ArithmeticFunction BigOperators

/-- The von Mangoldt function restricted to `n ≤ V`. -/
noncomputable def lambdaLE (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The von Mangoldt function restricted to `V < n`. -/
noncomputable def lambdaGT (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The real-valued Möbius function restricted to `n ≤ U`. -/
noncomputable def muLE (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The real-valued Möbius function restricted to `U < n`. -/
noncomputable def muGT (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

@[simp] theorem lambdaLE_apply (V n : ℕ) :
    lambdaLE V n = if n ≤ V then ArithmeticFunction.vonMangoldt n else 0 :=
  rfl

@[simp] theorem lambdaGT_apply (V n : ℕ) :
    lambdaGT V n = if V < n then ArithmeticFunction.vonMangoldt n else 0 :=
  rfl

@[simp] theorem muLE_apply (U n : ℕ) :
    muLE U n = if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0 :=
  rfl

@[simp] theorem muGT_apply (U n : ℕ) :
    muGT U n = if U < n then (ArithmeticFunction.moebius n : ℝ) else 0 :=
  rfl

/-- The two Möbius cutoffs form an exact partition. -/
theorem muLE_add_muGT (U : ℕ) :
    muLE U + muGT U = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  by_cases hn : n ≤ U
  · have hnot : ¬ U < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : U < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- The two von Mangoldt cutoffs form an exact partition. -/
theorem lambdaLE_add_lambdaGT (V : ℕ) :
    lambdaLE V + lambdaGT V =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  ext n
  by_cases hn : n ≤ V
  · have hnot : ¬ V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- Vaughan's logarithmically weighted Type-I piece. -/
noncomputable def vaughanTypeILog (U : ℕ) : ArithmeticFunction ℝ :=
  muLE U * ArithmeticFunction.log

/-- Vaughan's low-von-Mangoldt Type-I cross term. -/
noncomputable def vaughanTypeILambda (U V : ℕ) : ArithmeticFunction ℝ :=
  muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLE V)

/-- Vaughan's bilinear tail. -/
noncomputable def vaughanTypeII (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaGT V * (muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

/-- Vaughan's identity as an equality of real-valued arithmetic functions.

The usual side conditions `1 ≤ U` and `1 ≤ V` are not needed for the identity itself; they enter
only when the four pieces are estimated. -/
theorem vaughan_identity_function (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      lambdaLE V + vaughanTypeILog U - vaughanTypeILambda U V + vaughanTypeII U V := by
  have hMuZeta :
      (muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := by
    rw [muLE_add_muGT, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  have hLambdaHigh :
      lambdaGT V = vaughanTypeILog U - vaughanTypeILambda U V + vaughanTypeII U V := by
    have hExpand :
        lambdaGT V = lambdaGT V *
            ((muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [hMuZeta, mul_one]
    have hDistribute :
        lambdaGT V *
            ((muLE U + muGT U) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
          muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaGT V) +
            vaughanTypeII U V := by
      unfold vaughanTypeII
      ring
    have hLambdaHighEq :
        lambdaGT V =
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaLE V := by
      have hsplit := lambdaLE_add_lambdaGT V
      rw [← hsplit]
      abel
    have hFirst :
        muLE U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaGT V) =
          vaughanTypeILog U - vaughanTypeILambda U V := by
      rw [hLambdaHighEq, mul_sub, ArithmeticFunction.zeta_mul_vonMangoldt]
      unfold vaughanTypeILog vaughanTypeILambda
      ring
    rw [hExpand, hDistribute, hFirst]
  rw [← lambdaLE_add_lambdaGT V, hLambdaHigh]
  abel

/-- Pointwise form of `vaughan_identity_function`. -/
theorem vaughan_identity (U V n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      lambdaLE V n + vaughanTypeILog U n - vaughanTypeILambda U V n +
        vaughanTypeII U V n := by
  have h := congrArg (fun a : ArithmeticFunction ℝ ↦ a n)
    (vaughan_identity_function U V)
  simpa only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg] using h

/-- A finite complex-weighted sum of a real-valued arithmetic function. -/
noncomputable def weightedArithmeticSum
    (I : Finset ℕ) (w : ℕ → ℂ) (a : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ I, (a n : ℂ) * w n

/-- Vaughan's identity after multiplication by an arbitrary complex weight and finite summation.

This is deliberately more general than the standard linear exponential sum.  In Track B the
intended weight is a sharp interval indicator times `exp (2π i a / log n)`. -/
theorem vaughan_weighted_sum (U V : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum I w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      weightedArithmeticSum I w (lambdaLE V) +
        weightedArithmeticSum I w (vaughanTypeILog U) -
        weightedArithmeticSum I w (vaughanTypeILambda U V) +
        weightedArithmeticSum I w (vaughanTypeII U V) := by
  unfold weightedArithmeticSum
  calc
    (∑ n ∈ I, ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n : ℂ) * w n) =
        ∑ n ∈ I,
          ((lambdaLE V n : ℂ) * w n +
            (vaughanTypeILog U n : ℂ) * w n -
            (vaughanTypeILambda U V n : ℂ) * w n +
            (vaughanTypeII U V n : ℂ) * w n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hreal := vaughan_identity U V n
      have hcomplex :
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) =
            (lambdaLE V n : ℂ) + (vaughanTypeILog U n : ℂ) -
              (vaughanTypeILambda U V n : ℂ) + (vaughanTypeII U V n : ℂ) := by
        exact_mod_cast hreal
      rw [hcomplex]
      ring
    _ = (∑ n ∈ I, (lambdaLE V n : ℂ) * w n) +
          (∑ n ∈ I, (vaughanTypeILog U n : ℂ) * w n) -
          (∑ n ∈ I, (vaughanTypeILambda U V n : ℂ) * w n) +
          (∑ n ∈ I, (vaughanTypeII U V n : ℂ) * w n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The logarithmic Type-I piece expanded over factor pairs. -/
theorem vaughanTypeILog_apply (U n : ℕ) :
    vaughanTypeILog U n =
      ∑ ab ∈ n.divisorsAntidiagonal,
        muLE U ab.1 * ArithmeticFunction.log ab.2 := by
  rw [vaughanTypeILog, ArithmeticFunction.mul_apply]

/-- The bilinear tail expanded over factor pairs.  The second coefficient still contains the
inner Möbius--zeta convolution; retaining it is the exact form of the identity. -/
theorem vaughanTypeII_apply (U V n : ℕ) :
    vaughanTypeII U V n =
      ∑ ab ∈ n.divisorsAntidiagonal,
        lambdaGT V ab.1 *
          (muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ab.2 := by
  rw [vaughanTypeII, ArithmeticFunction.mul_apply]

/-- Finite weighted form of the Type-II factor-pair expansion. -/
theorem weightedArithmeticSum_vaughanTypeII
    (U V : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum I w (vaughanTypeII U V) =
      ∑ n ∈ I,
        (∑ ab ∈ n.divisorsAntidiagonal,
          (lambdaGT V ab.1 : ℂ) *
            ((muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ab.2 : ℂ)) * w n := by
  unfold weightedArithmeticSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [vaughanTypeII_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

end TrackB
end Erdos878

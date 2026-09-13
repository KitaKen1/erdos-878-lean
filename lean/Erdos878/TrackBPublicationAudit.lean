import Erdos878.TrackBEndpointParameters

/-!
# Track B: publication regression audit

This small module is deliberately independent of the long analytic proof file. It fixes three
review-sensitive facts at the public boundary:

* the core `erdos_878.parts.ii` unfolds to the exact ordinary maximal-order limit;
* the final Track-B result inhabits that source-question type directly; and
* the packed-multiple construction has the intended meaning on a concrete finite example.
-/

namespace Erdos878.TrackB
open Filter Finset
open scoped Topology

/-- Statement checksum for the second natural-language question. -/
theorem parts_ii_statement_checksum : erdos_878.parts.ii ↔
    Tendsto (fun x : ℕ ↦
      (Erdos878.maxUpTo Erdos878.f x : ℝ) /
        ((x : ℝ) * Real.log x / Real.log (Real.log x)))
      atTop (𝓝 1) := by
  rfl

/-- Publication-facing alias whose type is the source question itself. -/
theorem parts_ii_publication_candidate : erdos_878.parts.ii :=
  erdos_878_parts_ii_proved

/-- The two-prime test family has product six. -/
theorem primeProduct_two_three :
    Erdos878.primeProduct ({2, 3} : Finset ℕ) = 6 := by
  norm_num [Erdos878.primeProduct]

/-- For `X = 35`, the construction chooses the largest multiple of six, namely thirty. -/
theorem multipleBelow_thirty_five_two_three :
    Erdos878.multipleBelow 35 ({2, 3} : Finset ℕ) = 30 := by
  norm_num [Erdos878.multipleBelow, Erdos878.primeProduct]

/-- At that packed multiple, the selected contributions are `2^4 + 3^3 = 43`. -/
theorem selectedPowerSum_two_three :
    (∑ p ∈ ({2, 3} : Finset ℕ),
      p ^ Nat.log p (Erdos878.multipleBelow 35 ({2, 3} : Finset ℕ))) = 43 := by
  have h2 : Nat.log 2 30 = 4 := by decide
  have h3 : Nat.log 3 30 = 3 := by decide
  norm_num [Erdos878.multipleBelow, Erdos878.primeProduct, h2, h3]

/-- The generic packing theorem accepts the concrete test family and places its sum below the
actual finite maximum of `f`. -/
theorem packing_regression_two_three :
    (∑ p ∈ ({2, 3} : Finset ℕ),
      p ^ Nat.log p (Erdos878.multipleBelow 35 ({2, 3} : Finset ℕ))) ≤
      Erdos878.maxUpTo Erdos878.f 35 := by
  apply Erdos878.sum_primePower_le_maxUpTo_f_of_selected_primes
  · intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  · norm_num [Erdos878.primeProduct]

#print axioms parts_ii_statement_checksum
#print axioms parts_ii_publication_candidate
#print axioms packing_regression_two_three

end Erdos878.TrackB

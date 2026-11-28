import Mathlib

/-!
# A306211: Concatenation of the current sequence with the lengths of the runs in the sequence,
with a(1) = 1.

Source: https://oeis.org/A306211
Credit: @Solfanbtc

Construction (entry, "alternative definition"): start with `[1]`, and repeatedly append to the
current sequence its RUNS transform (the list of the lengths of its maximal runs of equal terms).
The generations are `1`, `11`, `112`, `11221`, `11221221`, ...; each is a prefix of the next, and
A306211 is their limit.

Conjecture (Peter Kagey, Jan 29 2019): "All terms are less than or equal to 5."

The entry also records the opposite conjecture of N. J. A. Sloane (Jan 29 2019), "Every number
appears!", based on the analogy with A090822. The two are incompatible (Sloane's implies that `6`
occurs), so they cannot both be stated in one theorem; Kagey's, listed first, is stated here.
(B. Chaffin found the largest term among the first 10228800161220 terms to be 5.)

Formalization. `gen t` is generation `t` (`gen 0 = [1]`). Since `gen t` has at least `t + 1`
terms and is a prefix of every later generation, `a n = (gen n)[n-1]` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a306211

/-- The RUNS transform: the lengths of the maximal runs of equal consecutive terms. -/
def runs (l : List ℕ) : List ℕ := (l.splitBy (· == ·)).map List.length

/-- Generation `t` of the construction: `gen 0 = [1]`, `gen (t+1) = gen t ++ runs (gen t)`. -/
def gen : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => gen t ++ runs (gen t)

/-- `a n` is the `n`-th term of A306211 (`n ≥ 1`). -/
def a (n : ℕ) : ℕ := (gen n).getD (n - 1) 0

/-- Kagey's conjecture: every term of A306211 is at most `5`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 5 := by
  sorry

end OMA.S_oeis_a306211

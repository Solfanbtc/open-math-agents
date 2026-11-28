import Mathlib

/-!
# A055189: Cumulative counting sequence, method A (adjective-before-noun) pairs, starting with 3

Source: https://oeis.org/A055189
Credit: @Solfanbtc

Construction (entry, examples): write `3`; then each new segment records what has been written so
far, as pairs "count, value" (adjective before noun), one pair for each distinct value written so
far, the values taken in order of first occurrence: `3; 1,3; 2,3,1,1; 3,3,3,1,1,2; 6,3,5,1,2,2; …`
("3 3's and 3 1's and 1 2"). Below, `seqAfter k` is the list of terms after `k` new segments
(`seqAfter 0 = [3]`); each is a prefix of the next, and the sequence is their union. This
reproduces all 86 data terms.

Conjecture (Clark Kimberling, Mar 25 2013, OEIS comment): every nonnegative integer occurs.

Minimal fix: `0` never occurs (every term is a count `≥ 1` or a value already written, and the
first term is `3`), so the claim fails at the trivial value `0`; it is stated for every positive
integer. (Python: after 20503 terms, every integer from `1` to `59` has occurred.)
-/

namespace OMA.S_oeis_a055189

/-- The distinct elements of `l` in order of first occurrence. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- The next segment: `count, value` for each value of `l`, in order of first occurrence. -/
def segment (l : List ℕ) : List ℕ := (firstOcc l).flatMap fun v => [l.count v, v]

/-- The terms after `k` new segments. -/
def seqAfter : ℕ → List ℕ
  | 0 => [3]
  | k + 1 => seqAfter k ++ segment (seqAfter k)

/-- Kimberling's conjecture (for positive integers): every `m ≥ 1` occurs in A055189. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k, m ∈ seqAfter k := by
  sorry

end OMA.S_oeis_a055189

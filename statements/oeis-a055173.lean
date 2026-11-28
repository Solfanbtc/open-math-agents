import Mathlib

/-!
# A055173: n-th distinct number to appear in A055171

Source: https://oeis.org/A055173
Credit: @Solfanbtc

A055171 (cumulative counting sequence, method B, (noun, adjective) pairs, first term 1): write
`1`; then each new segment records what has been written so far as pairs "value, count" (noun
before adjective), one pair for each distinct value written so far, the values in order of first
occurrence: `1; 1,1; 1,3; 1,4,3,1; 1,6,3,2,4,1; 1,8,3,3,4,2,6,1,2,1; …` ("1 four times and 3
once"). `seqAfter k` is the list of terms after `k` new segments (`seqAfter 0 = [1]`); each is a
prefix of the next. This reproduces all 66 data terms of A055171.

A055173 lists the distinct numbers of A055171 in order of first appearance:
`1, 3, 4, 6, 2, 8, 11, 5, …` (all 49 data terms reproduced from the simulation).

Conjecture (OEIS comment): A055173 is a permutation of the positive integers.

Formalization: A055173 is by construction injective, and all its terms are positive (every term
of A055171 is a count `≥ 1` or an earlier value, starting from `1`). Hence it is a permutation of
the positive integers iff every positive integer occurs in A055171 (this also makes it infinite),
which is what `main` states. (Python: every integer from 1 to 79 occurs among the first 30000
terms.)
-/

namespace OMA.S_oeis_a055173

/-- The distinct elements of `l` in order of first occurrence. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- The next segment: `value, count` for each value of `l`, in order of first occurrence. -/
def segment (l : List ℕ) : List ℕ := (firstOcc l).flatMap fun v => [v, l.count v]

/-- A055171: the terms after `k` new segments. -/
def seqAfter : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => seqAfter k ++ segment (seqAfter k)

/-- A055173 is a permutation of the positive integers: every `m ≥ 1` occurs in A055171. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k, m ∈ seqAfter k := by
  sorry

end OMA.S_oeis_a055173

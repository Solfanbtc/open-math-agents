import Mathlib

/-!
# A055188: Cumulative counting sequence: method A (adjective-before-noun) pairs, starting with 2.

Source: https://oeis.org/A055188
Credit: @Solfanbtc

Start with `2`; each new segment lists, for every distinct value `x` already written (in order
of first appearance), the pair `c, x` where `c` is the number of occurrences of `x` in
everything written so far. Segments: `2; 1,2; 2,2,1,1; 4,2,3,1; 5,2,4,1,1,4,1,3; …` (the
entry's Mathematica program `s = {2}; Do[s = Flatten[{s, {Count[s, #], #} & /@
DeleteDuplicates[s]}], ...]`). Each stage is a prefix of the next; the sequence is their union.
Checked with python3: the construction reproduces the 86 listed terms.

Conjecture (Clark Kimberling, 2013): "every nonnegative integer occurs". Taken literally this
fails at `0`: the first term is 2 and every later term is a count (≥ 1) or an earlier value,
so `0` never occurs. The minimal fix, stated here, is that every positive integer occurs
(the analogous conjecture for A217760, which starts with 0, includes 0).
-/

namespace OMA.S_oeis_a055188

/-- Distinct elements of a list, in order of first appearance. -/
def firstOcc : List ℕ → List ℕ
  | [] => []
  | x :: l => x :: (firstOcc l).filter (· ≠ x)

/-- One step: append the (count, value) pairs of the distinct values written so far. -/
def step (s : List ℕ) : List ℕ :=
  s ++ (firstOcc s).flatMap (fun x => [s.count x, x])

/-- The terms written after `n` steps, starting from `[2]`. -/
def stage (n : ℕ) : List ℕ := step^[n] [2]

/-- The conjecture (with `0` excluded, see above): every positive integer occurs. -/
theorem main : ∀ m : ℕ, 0 < m → ∃ n, m ∈ stage n := by
  sorry

end OMA.S_oeis_a055188

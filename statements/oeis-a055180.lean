import Mathlib

/-!
# A055180: Cumulative counting sequence: method B (noun,adjective)-pairs with first term 4.

Source: https://oeis.org/A055180
Credit: @Solfanbtc

The sequence is built in segments: start with `4`; each new segment lists, for every distinct
value `x` already written (in order of first appearance), the pair `x, c` where `c` is the
number of times `x` occurs in everything written so far (the segment being built excluded).
Segments: `4; 4,1; 4,2,1,1; 4,3,1,3,2,1; ...` (this is the entry's Mathematica program
`s = {4}; Do[s = Flatten[{s, {#, Count[s, #]} & /@ DeleteDuplicates[s]}], ...]`).
Each stage is a prefix of the next, so the sequence is the union of the stages `stage n`.

The entry's conjecture: every positive integer occurs in the sequence.
Checked with python3: the construction reproduces the listed data (87 terms).
-/

namespace OMA.S_oeis_a055180

/-- Distinct elements of a list, in order of first appearance (Mathematica's
`DeleteDuplicates`). -/
def firstOcc : List ℕ → List ℕ
  | [] => []
  | x :: l => x :: (firstOcc l).filter (· ≠ x)

/-- One step: append the (value, count) pairs of the distinct values written so far. -/
def step (s : List ℕ) : List ℕ :=
  s ++ (firstOcc s).flatMap (fun x => [x, s.count x])

/-- The terms written after `n` steps, starting from `[4]`. -/
def stage (n : ℕ) : List ℕ := step^[n] [4]

/-- The conjecture: every positive integer occurs in A055180. -/
theorem main : ∀ m : ℕ, 0 < m → ∃ n, m ∈ stage n := by
  sorry

end OMA.S_oeis_a055180

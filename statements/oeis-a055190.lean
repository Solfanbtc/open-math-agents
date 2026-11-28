import Mathlib

/-!
# A055190: Cumulative counting sequence: method A (adjective-before-noun) pairs, starting with 4.

Source: https://oeis.org/A055190
Credit: @Solfanbtc

Conjecture (Clark Kimberling, Mar 25 2013, in the entry): every positive integer occurs.

Conventions.
* Construction (method A, made precise by the entry's Mathematica program
  `s = {4}; Do[s = Flatten[{s, {Count[s, #], #} & /@ DeleteDuplicates[s]}], ...]`): start with
  the list [4]; at each step append, for each distinct value x of the current list in order of
  first appearance, the pair (number of occurrences of x in the current list), x. The sequence
  is the limit of these lists (each is a prefix of the next). python3: 4, 1, 4, 2, 4, 1, 1, 3,
  4, 3, 1, 1, 2, 4, 4, 5, ... (the data).
* `firstOcc` lists the distinct values in order of first appearance (Mathematica's
  DeleteDuplicates). "Every positive integer occurs" is stated as: for every m ≥ 1 some
  iterate of the construction contains m.
-/

namespace OMA.S_oeis_a055190

/-- Distinct values in order of first appearance. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- One step of the method A construction. -/
def step (s : List ℕ) : List ℕ := s ++ (firstOcc s).flatMap fun x => [s.count x, x]

theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, m ∈ step^[k] [4] := by
  sorry

end OMA.S_oeis_a055190

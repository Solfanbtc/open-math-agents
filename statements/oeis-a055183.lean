import Mathlib

/-!
# A055183: Cumulative counting sequence: method B (noun,adjective)-pairs with first term 5.

Source: https://oeis.org/A055183
Credit: @Solfanbtc

Conjecture (in the entry): every positive integer occurs.

Conventions.
* Construction (method B, as in A055168, made precise by the entry's Mathematica program
  `s = {5}; Do[s = Flatten[{s, {#, Count[s, #]} & /@ DeleteDuplicates[s]}], ...]`): start with
  the list [5]; at each step append, for each distinct value x of the current list in order of
  first appearance, the pair x, (number of occurrences of x in the current list). The sequence
  is the limit of these lists (each is a prefix of the next). python3: 5, 5, 1, 5, 2, 1, 1, 5, 3,
  1, 3, 2, 1, 5, 4, ... (the data).
* `firstOcc` lists the distinct values in order of first appearance (Mathematica's
  DeleteDuplicates). "Every positive integer occurs" is stated as: for every m ≥ 1 some
  iterate of the construction contains m.
-/

namespace OMA.S_oeis_a055183

/-- Distinct values in order of first appearance. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- One step of the method B construction. -/
def step (s : List ℕ) : List ℕ := s ++ (firstOcc s).flatMap fun x => [x, s.count x]

theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, m ∈ step^[k] [5] := by
  sorry

end OMA.S_oeis_a055183

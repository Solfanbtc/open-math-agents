import Mathlib

/-!
# A055176: the distinct values of the cumulative counting sequence A055174 are all positive integers

Source: https://oeis.org/A055176
Credit: @Solfanbtc

A055174: the cumulative counting sequence, method B (noun, adjective) pairs, with first term 2:
write 2; then repeatedly append a segment which, for each integer written so far (in order of
first appearance), states the integer and then how many times it has been written so far. The
entry's program: `s = {2}; Do[s = Flatten[{s, {#, Count[s, #]} & /@ DeleteDuplicates[s]}], …]`.
Segments 2; 2,1; 2,2,1,1; 2,4,1,3,2,5,… Data 2, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 5, …
A055176: the `n`-th distinct number to appear in A055174: 2, 1, 4, 3, 5, 6, 7, 8, 9, 10, 12, …

Conjecture (in the entry): A055176 is a permutation of the positive integers. Since A055176 lists
the distinct values of A055174 in order of first appearance, it is automatically injective and
positive, so the conjecture says exactly that every positive integer occurs in A055174 (which is
also the conjecture stated in A055174). `main` states: for every `m ≥ 1` there is a stage of the
construction whose word contains `m`. (Each stage extends the previous one, so A055174 is the
limit word.)

Lean details. `firstOcc` lists the distinct entries of a list in order of first appearance (like
Mathematica's `DeleteDuplicates`; Mathlib's `List.dedup` keeps last occurrences instead). Checked
with python3: the construction reproduces the 34 listed terms of A055174 and the listed terms of
A055176.
-/

namespace OMA.S_oeis_a055176

/-- The distinct entries of `l` in order of first appearance. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- One step: append, for each value written so far, the value and its current count. -/
def step (s : List ℕ) : List ℕ := s ++ (firstOcc s).flatMap fun x => [x, s.count x]

/-- The word after `n` steps, starting from `[2]`. -/
def word (n : ℕ) : List ℕ := step^[n] [2]

/-- The conjecture: every positive integer occurs in A055174 (equivalently, A055176 is a
permutation of the positive integers). -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, m ∈ word n := by
  sorry

end OMA.S_oeis_a055176

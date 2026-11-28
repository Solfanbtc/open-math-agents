import Mathlib

/-!
# A055177: Cumulative counting sequence: method B (noun,adjective)-pairs with first term 3.

Source: https://oeis.org/A055177
Credit: @Solfanbtc

Conjecture (OEIS A055177): every positive integer occurs in the sequence.

Construction (as at A055168, "method B", noun before adjective): write 3; then, segment after
segment, for each integer already written, write the integer followed by the number of times it
has been written so far (before the current segment). The integers are taken in the order of their
first appearance: the segments are 3; 3,1; 3,2,1,1; 3,3,1,3,2,1; 3,6,1,5,2,2; 3,7,1,6,2,4,6,1,5,1;
... (this order is the one matching the data: e.g. 6 is listed before 5 in the sixth segment).
`written k` is the list after k segments beyond the initial 3; the sequence is the limit of these
lists (each is a prefix of the next), so the conjecture says that every m >= 1 lies in some
`written k`. Checked numerically: the construction reproduces all 86 listed terms.
-/

namespace OMA.S_oeis_a055177

/-- The distinct entries of a list, in order of first appearance. -/
def firstOcc (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- The next segment: each integer written so far, followed by its number of occurrences. -/
def segment (w : List ℕ) : List ℕ := (firstOcc w).flatMap fun x => [x, w.count x]

/-- The terms written after `k` segments (starting from the single term 3). -/
def written : ℕ → List ℕ
  | 0 => [3]
  | k + 1 => written k ++ segment (written k)

theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, m ∈ written k := by
  sorry

end OMA.S_oeis_a055177

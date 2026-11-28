import Mathlib

/-!
# A057652: Numbers n such that n-2^k is a lucky number for all k such that 1 < 2^k < n.

Source: https://oeis.org/A057652 (lucky numbers: https://oeis.org/A000959)
Credit: @Solfanbtc

Lucky numbers (A000959): start from 1, 2, 3, 4, ...; the second number is 2, so delete every
second number, leaving the odd numbers 1, 3, 5, 7, ...; the next surviving number (the second
one) is 3, so delete every third remaining number; the next surviving number (the third one) is
7, so delete every seventh remaining number; and so on: at stage `i` (`i = 1, 2, ...`, positions
counted from 0) the number `v` at position `i` of the current list is used to delete every
`v`-th remaining number. Survivors: 1, 3, 7, 9, 13, 15, 21, 25, ...

The deletions at each stage only depend on positions, so sieving the finite list of odd numbers
`≤ N` with the same rule deletes exactly the lucky-sieve deletions below `N` (a stage whose
sieving number exceeds the list length deletes nothing there, and every later sieving number is
larger still). Hence `n` is lucky iff it survives the sieve run on the odd numbers `≤ n`; this is
`IsLucky` below (`luckyUpTo N` runs at most `N` stages, more than enough).

A057652: `n` such that `n - 2^k` is lucky for every `k` with `1 < 2^k < n`:
1, 2, 3, 5, 11, 17, 647.

Conjecture (M. F. Hasler, Oct 15 2010; cf. Erdős for A039669): this sequence is finite.
(`InSeq 0` holds vacuously; one extra element does not affect finiteness.)

Sanity check (python): the sieve gives the lucky numbers 1, 3, 7, 9, 13, 15, 21, 25, 31, ..., and
the terms up to 300000 are exactly 1, 2, 3, 5, 11, 17, 647; `#eval` in Lean agrees.
-/

namespace OMA.S_oeis_a057652

/-- Delete every `v`-th element (positions `v, 2v, ...`, counted from 1) of `l`. -/
def dropEvery (v : ℕ) (l : List ℕ) : List ℕ :=
  ((l.zipIdx).filter (fun p => (p.2 + 1) % v ≠ 0)).map Prod.fst

/-- Run stages `i, i+1, ...` of the lucky sieve on `l` (at most `fuel` stages). -/
def sieve : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, l => l
  | fuel + 1, i, l =>
    match l[i]? with
    | none => l
    | some v => sieve fuel (i + 1) (dropEvery v l)

/-- The lucky numbers `≤ N`. -/
def luckyUpTo (N : ℕ) : List ℕ := sieve N 1 ((List.range (N + 1)).filter (fun m => m % 2 = 1))

/-- `n` is a lucky number (A000959). -/
def IsLucky (n : ℕ) : Prop := n ∈ luckyUpTo n

/-- `n` belongs to A057652. -/
def InSeq (n : ℕ) : Prop := ∀ k : ℕ, 1 < 2 ^ k → 2 ^ k < n → IsLucky (n - 2 ^ k)

/-- Hasler's conjecture: A057652 is finite. -/
theorem main : Set.Finite {n : ℕ | InSeq n} := by
  sorry

end OMA.S_oeis_a057652

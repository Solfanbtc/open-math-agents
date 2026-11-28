import Mathlib

/-!
# A078943: a(1)=1; a(n+1) is either a(n)-n or a(n)+n, where we choose the smallest positive integer that's not among the values a(1), ..., a(n).

Source: https://oeis.org/A078943
Credit: @Solfanbtc

A078943 itself is finite and full (it stops after `a(24) = 19`). The conjecture recorded in it
(Peter Munn, Feb 09 2023) is about A356080: "A356080 is targeted to be such a sequence [a walk
`a(n+1) = a(n) ± n` visiting every integer exactly once], but starting from 0. Its definition
incorporates a limited look-ahead condition that is clearly a necessary condition for the
sequence not to encounter a dead end (i.e., be finite) and is conjectured to be a sufficient
condition." This is the conjecture of A356080 (Munn): the sequence is infinite (and so a
permutation of the nonnegative integers). We state that A356080 never stops.

A356080, as defined there. Paths are lists `p = [a(1), a(2), …]` of nonnegative integers with
`a(1) = 0`, `|a(n+1) - a(n)| = n` and no two terms equal (`Valid`; with 0-indexed lists the step
from position `i` to `i + 1` has size `i + 1`). The path `P` is extended in stages. Let `m` be
the least number absent from `P`. An extension route `R` (a list with `P ++ R` valid) is
*suitable* if (1) `R` ends in `m` and (2) some further route `R'` with `P ++ R ++ R'` valid ends
in a record, a number greater than every term of `P ++ R`. If there is no suitable `R`, the
sequence finishes; otherwise `P` is extended by the lexicographically earliest among the
shortest suitable routes. The process starts with `P = [0]`.

Checked in Python: this process reproduces the first 110 terms of the b-file of A356080 (all
that the search was run for), which include all of its %S, %T, %U data.
-/

namespace OMA.S_oeis_a078943

/-- `|p[i+1] - p[i]| = i + 1` for all consecutive positions, and the terms are distinct. -/
def Valid (p : List ℕ) : Prop :=
  p.Nodup ∧ ∀ i : ℕ, i + 1 < p.length →
    ((p[i + 1]! : ℤ) - p[i]! = i + 1 ∨ (p[i]! : ℤ) - p[i + 1]! = i + 1)

/-- The least number absent from `p`. -/
noncomputable def mex (p : List ℕ) : ℕ := sInf {m : ℕ | m ∉ p}

/-- `r` is a suitable extension route of `p`. -/
def Suitable (p r : List ℕ) : Prop :=
  Valid (p ++ r) ∧ r.getLast? = some (mex p) ∧
    ∃ r' : List ℕ, Valid (p ++ r ++ r') ∧
      ∃ x : ℕ, (r ++ r').getLast? = some x ∧ ∀ y ∈ p ++ r, y < x

/-- `r` is the lexicographically earliest shortest suitable route from `p`. -/
def IsNext (p r : List ℕ) : Prop :=
  Suitable p r ∧ ∀ r' : List ℕ, Suitable p r' →
    r.length < r'.length ∨ (r.length = r'.length ∧ (r = r' ∨ List.Lex (· < ·) r r'))

/-- Munn's conjecture: the construction of A356080 never finishes. -/
theorem main : ∃ P : ℕ → List ℕ, P 0 = [0] ∧
    ∀ j : ℕ, ∃ r : List ℕ, IsNext (P j) r ∧ P (j + 1) = P j ++ r := by
  sorry

end OMA.S_oeis_a078943

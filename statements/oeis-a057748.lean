import Mathlib

/-!
# A057748: Number of decompositions of 2n-1 into sum of a twin lucky number and a twin even-lucky-number (from A045955, A045956).

Source: https://oeis.org/A057748
Credit: @Solfanbtc

Lucky numbers (A000959): from the odd numbers 1, 3, 5, …, for `i = 2, 3, …` (1-indexed) take
the `i`-th surviving number `k` and delete every `k`-th surviving number. Even-lucky numbers
(A045954, 2, 4, 6, 10, 12, 18, …): the same sieve started from the even numbers 2, 4, 6, …
(the entries' Mathematica program). A twin lucky number is a lucky number `x` such that `x - 2`
or `x + 2` is lucky; a twin even-lucky number is defined likewise (A045955 / A045956 are the
lower / upper members of the pairs). As in the entry's examples (`3 = 1 + 2`, `5 = 3 + 2 = 1 + 4`),
both members of a pair count.

Whether `x` survives the sieve depends only on the numbers `≤ x` (deletions are by position),
so `x` is lucky iff it survives the finite sieve on the odd numbers `≤ x`.

A057748(n) counts the ways `2n - 1 = a + b` with `a` twin lucky (odd) and `b` twin even-lucky.
Conjecture: A057748(n) > 0 for every `n > 1`. Checked with python3: the definitions reproduce
the listed data (104 terms), and the conjecture holds for `2 ≤ n < 1300`.
-/

namespace OMA.S_oeis_a057748

/-- Delete every `k`-th element (positions `k, 2k, …`, 1-indexed). -/
def deleteEvery (k : ℕ) (l : List ℕ) : List ℕ :=
  ((l.zipIdx 1).filter (fun p => (p.2 % k != 0))).map Prod.fst

/-- The sieve, from the element at (0-indexed) position `i` on, with `fuel` steps. -/
def sieveAux : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, l => l
  | fuel + 1, i, l =>
    match l[i]? with
    | none => l
    | some k => sieveAux fuel (i + 1) (deleteEvery k l)

/-- The lucky-number sieve applied to a finite list (first sieving number: its second element). -/
def sieve (l : List ℕ) : List ℕ := sieveAux l.length 1 l

/-- `x` is a lucky number (A000959). -/
def IsLucky (x : ℕ) : Prop :=
  x ∈ sieve ((List.range (x + 1)).filter (fun m => m % 2 == 1))

/-- `x` is an even-lucky number (A045954). -/
def IsEvenLucky (x : ℕ) : Prop :=
  x ∈ sieve ((List.range (x + 1)).filter (fun m => 0 < m && m % 2 == 0))

/-- A member of a pair of twin lucky numbers. -/
def IsTwinLucky (x : ℕ) : Prop :=
  IsLucky x ∧ (IsLucky (x + 2) ∨ (2 ≤ x ∧ IsLucky (x - 2)))

/-- A member of a pair of twin even-lucky numbers (A045955 ∪ A045956). -/
def IsTwinEvenLucky (x : ℕ) : Prop :=
  IsEvenLucky x ∧ (IsEvenLucky (x + 2) ∨ (2 ≤ x ∧ IsEvenLucky (x - 2)))

/-- The conjecture: for every `n > 1`, `2n - 1` is the sum of a twin lucky number and a twin
even-lucky number. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ a b : ℕ, a + b = 2 * n - 1 ∧ IsTwinLucky a ∧ IsTwinEvenLucky b := by
  sorry

end OMA.S_oeis_a057748

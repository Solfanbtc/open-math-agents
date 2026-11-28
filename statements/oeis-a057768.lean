import Mathlib

/-!
# A057768: Goldbach-type decompositions with prime lucky numbers and twin even-lucky numbers

Source: https://oeis.org/A057768 (see A000959, A031157, A045954, A045955, A045956)
Credit: @Solfanbtc

* Lucky numbers (A000959): from 1, 3, 5, 7, ... (the odd numbers, i.e. after the first stage
  of deleting every 2nd number), at each stage `i = 1, 2, ...` (positions counted from 0) the
  number `v` at position `i` of the current list is used to delete every `v`-th remaining number.
* Even-lucky numbers (A045954): the same sieve started from the even numbers 2, 4, 6, ...
  ("first term > 2 is 4 so starting from 2 remove every 4th number ...; next number is 6 so
  remove every 6th term"): 2, 4, 6, 10, 12, 18, 20, 22, 26, ...
* Prime lucky numbers (A031157): lucky numbers that are prime: 3, 7, 13, 31, ...
* Twin even-lucky numbers (A045955 lower terms, A045956 upper terms): even-lucky numbers `e`
  such that `e + 2` or `e - 2` is also even-lucky.

As in A057652, sieving the finite list of odd (resp. even) numbers `≤ N` performs exactly the
deletions of the infinite sieve below `N`, so `n` is (even-)lucky iff it survives the sieve run on
the odd (even) numbers `≤ n`.

`a(n)` is the number of decompositions of `2n - 1` as `p + t` with `p` a prime lucky number and
`t` a twin even-lucky number (`a(1) = a(2) = 0`, `5 = 3 + 2`, `7 = 3 + 4`, `9 = 3 + 6 = 7 + 2`).

Conjecture (entry): `a(n) > 0` for `n > 2`, i.e. every `2n - 1` with `n > 2` is such a sum.

Sanity check (python): these definitions reproduce A045954, A045955, A045956 and all 105 listed
terms of A057768, and the conjecture holds for `3 ≤ n < 199990`.
-/

namespace OMA.S_oeis_a057768

/-- Delete every `v`-th element (positions `v, 2v, ...`, counted from 1) of `l`. -/
def dropEvery (v : ℕ) (l : List ℕ) : List ℕ :=
  ((l.zipIdx).filter (fun p => (p.2 + 1) % v ≠ 0)).map Prod.fst

/-- Run stages `i, i+1, ...` of a lucky-type sieve on `l` (at most `fuel` stages). -/
def sieve : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, l => l
  | fuel + 1, i, l =>
    match l[i]? with
    | none => l
    | some v => sieve fuel (i + 1) (dropEvery v l)

/-- `n` is a lucky number (A000959). -/
def IsLucky (n : ℕ) : Prop :=
  n ∈ sieve n 1 ((List.range (n + 1)).filter (fun m => m % 2 = 1))

/-- `n` is an even-lucky number (A045954). -/
def IsEvenLucky (n : ℕ) : Prop :=
  n ∈ sieve n 1 ((List.range (n + 1)).filter (fun m => m % 2 = 0 ∧ 0 < m))

/-- `t` is a twin even-lucky number (a term of A045955 or A045956). -/
def IsTwinEvenLucky (t : ℕ) : Prop :=
  IsEvenLucky t ∧ (IsEvenLucky (t + 2) ∨ (2 ≤ t ∧ IsEvenLucky (t - 2)))

/-- The conjecture: for `n > 2`, `2n - 1` is a prime lucky number plus a twin even-lucky
number. -/
theorem main : ∀ n : ℕ, 2 < n →
    ∃ p t : ℕ, p.Prime ∧ IsLucky p ∧ IsTwinEvenLucky t ∧ p + t = 2 * n - 1 := by
  sorry

end OMA.S_oeis_a057768

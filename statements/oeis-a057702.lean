import Mathlib

/-!
# A057702: Even numbers not the sum of a pair of twin lucky numbers.

Source: https://oeis.org/A057702 (lucky numbers: A000959; cf. A007534 for twin primes)
Credit: @Solfanbtc

Lucky numbers (A000959): from 1, 3, 5, 7, ... (the odd numbers, i.e. after the first stage of
deleting every 2nd number), at each stage `i = 1, 2, ...` (positions counted from 0) the number
`v` at position `i` of the current list is used to delete every `v`-th remaining number. As in
A057652, sieving the odd numbers `≤ n` performs exactly the deletions of the infinite sieve below
`n`, so `n` is lucky iff it survives the sieve run on the odd numbers `≤ n`.

A twin lucky number is a lucky number `ℓ` such that `ℓ + 2` or `ℓ - 2` is also lucky
(1, 3, 7, 9, 13, 15, ...). As for twin primes in A007534, "the sum of a pair of twin lucky
numbers" means `a + b` with `a` and `b` twin lucky numbers (possibly equal, e.g. `2 = 1 + 1`; with
distinct summands 2, 6, 26, 30 would also be exceptions, contradicting the data). The listed
exceptions among the positive even numbers are
92, 94, 96, 110, ..., 7034, 7036, 7038 (63 numbers).

Conjecture (entry): the list is complete, i.e. the positive even numbers that are not such a sum
are exactly the 63 listed numbers.

Sanity check (python): with this reading, the exceptions among the even numbers `≤ 10^6` are
exactly the 63 listed terms.
-/

namespace OMA.S_oeis_a057702

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

/-- `n` is a lucky number (A000959). -/
def IsLucky (n : ℕ) : Prop :=
  n ∈ sieve n 1 ((List.range (n + 1)).filter (fun m => m % 2 = 1))

/-- `ℓ` is a twin lucky number. -/
def IsTwinLucky (ℓ : ℕ) : Prop :=
  IsLucky ℓ ∧ (IsLucky (ℓ + 2) ∨ (2 ≤ ℓ ∧ IsLucky (ℓ - 2)))

/-- The listed terms of A057702. -/
def listed : Finset ℕ :=
  {92, 94, 96, 110, 112, 114, 152, 154, 156, 188, 190, 192, 212, 214, 216, 230, 232, 234,
   278, 280, 282, 344, 346, 348, 374, 376, 378, 380, 382, 384, 572, 574, 576, 698, 700,
   702, 764, 766, 768, 824, 826, 828, 830, 832, 834, 842, 844, 846, 1742, 1744, 1746, 2168, 2170,
   2172, 2546, 2548, 2550, 5948, 5950, 5952, 7034, 7036, 7038}

/-- The conjecture: A057702 is complete. -/
theorem main :
    {n : ℕ | 0 < n ∧ Even n ∧ ¬ ∃ a b : ℕ, IsTwinLucky a ∧ IsTwinLucky b ∧ a + b = n} =
      (listed : Set ℕ) := by
  sorry

end OMA.S_oeis_a057702

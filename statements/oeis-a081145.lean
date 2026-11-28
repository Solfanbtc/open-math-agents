import Mathlib

/-!
# A081145: the Slater-Vélez permutation has a permutation as its absolute difference sequence

Source: https://oeis.org/A081145
Credit: @Solfanbtc

A081145 (offset 1): `a(1) = 1`; thereafter `a(n)` is the least positive integer which has not
already occurred and is such that `|a(n) - a(n-1)|` is different from any `|a(k) - a(k-1)|` which
has already occurred. Data 1, 2, 4, 7, 3, 8, 14, 5, 12, 20, …

The entry: "The 1977 paper of Slater and Vélez proves that this sequence is a permutation of
positive integers and conjectures that its absolute difference sequence (see A308007) is also a
permutation." Status: "Indeed, the sequence of absolute differences is also a permutation of the
positive integers (see Floros, 2026)". `main` states the Slater-Vélez conjecture: the map
`n ↦ |a(n+1) - a(n)|` (`n ≥ 1`) is injective and takes every positive integer value.
(Injectivity holds by construction; the content is surjectivity.)

Lean details. The terms are built by appending one at a time. With `M` the sum of the terms so
far, `x = 2M + 1` is always admissible (it is new, and `x - a(n-1) > M` exceeds every earlier
difference), so the search over `1, …, 2M + 1` always succeeds and the default `0` is never
used. Checked with python3: this reproduces the data of A081145 and of A308007.
-/

namespace OMA.S_oeis_a081145

/-- The absolute differences of consecutive entries of `l`. -/
def diffs (l : List ℕ) : List ℕ :=
  (List.range (l.length - 1)).map fun i => Int.natAbs ((l.getD (i + 1) 0 : ℤ) - l.getD i 0)

/-- Append the next term of A081145. -/
def extend (l : List ℕ) : List ℕ :=
  let last := l.getLastD 0
  l ++ [((List.range' 1 (2 * l.sum + 1)).find? fun x =>
    !(l.contains x) && !((diffs l).contains (Int.natAbs ((x : ℤ) - last)))).getD 0]

/-- A081145: `a(n)` for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := ((extend)^[n - 1] [1]).getD (n - 1) 0

/-- `|a(n+1) - a(n)|` (A308007). -/
def d (n : ℕ) : ℕ := Int.natAbs ((a (n + 1) : ℤ) - a n)

/-- The Slater-Vélez conjecture (proved by Floros): the absolute differences form a permutation
of the positive integers. -/
theorem main : (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → d m = d n → m = n) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ d n = k := by
  sorry

end OMA.S_oeis_a081145

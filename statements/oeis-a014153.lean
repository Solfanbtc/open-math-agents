import Mathlib

/-!
# A014153: Expansion of `1/((1-x)^2 ∏_{k≥1} (1-x^k))`

Source: https://oeis.org/A014153
Credit: @Solfanbtc

`a(n)` (offset 0) is the coefficient of `x^n` in `1/((1-x)^2 ∏_{k≥1}(1-x^k))`, i.e. the
partial sums of the partial sums of the partition numbers:
`a(n) = ∑_{m=0}^{n} (n - m + 1) p(m)` = `1, 3, 7, 14, 26, 45, …` (all 41 data terms agree).

Conjecture (George Beck, May 21 2016, OEIS formula): let
`t(n, k) = ∑_{i=0}^{k} ∑_{j=0}^{n} s(n, j) C(i, j) p(k - n - i)`, where `s(n, j)` are the
Stirling numbers of the first kind, `C(i, j)` is the number of compositions of `i` into `j`
parts and `p` is the partition function; then `a(k) = t(2, k + 2)`.

Conventions. `s(n, j)` is the (signed) Stirling number of the first kind,
`(-1)^(n-j)` times Mathlib's unsigned `Nat.stirlingFirst n j`. `C(i, j)` is as in the twin formula
of A126442, where it counts the ways to distribute `i` identical zeros into `j` distinct blocks
(blocks may receive none): `C(i, j) = binom(i + j - 1, j - 1)` for `j ≥ 1`, `C(i, 0) = [i = 0]`
(with this `C` and Stirling numbers of the second kind the formula reproduces the rows of
A126442, e.g. `3, 4, 5` and `5, 7, 11, 15`). `p(m) = 0` for `m < 0`.

Offset fix (minimal, needed): with these conventions `t(2, k + 2) = 0, 1, 3, 7, 14, 26, …` for
`k = 0, 1, 2, …`, i.e. `t(2, k + 2) = a(k - 1)`: the conjecture is off by one at the sequence's
offset 0 (already `t(2, 2) = 0 ≠ 1 = a(0)`), and holds exactly when `A014153` is indexed from
1. (Unsigned Stirling numbers with strict compositions give the same values; other readings
match nowhere.) So it is stated as `a(k - 1) = t(2, k + 2)` for `k ≥ 1`. Checked with Python
for `k ≤ 41`.
-/

namespace OMA.S_oeis_a014153

/-- The partition function `p(m)`. -/
def p (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- A014153: `a(n) = ∑_{m ≤ n} (n - m + 1) p(m)`. -/
def a (n : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), (n - m + 1) * p m

/-- Signed Stirling numbers of the first kind `s(n, j)`. -/
def s (n j : ℕ) : ℤ := (-1) ^ (n - j) * (Nat.stirlingFirst n j : ℤ)

/-- `C(i, j)`: compositions of `i` into `j` (possibly empty) parts. -/
def C (i j : ℕ) : ℕ := if j = 0 then (if i = 0 then 1 else 0) else Nat.choose (i + j - 1) (j - 1)

/-- Beck's `t(n, k) = ∑_{i=0}^{k} ∑_{j=0}^{n} s(n, j) C(i, j) p(k - n - i)`, with `p` of a negative
argument equal to `0`. -/
def t (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (n + 1),
    s n j * C i j * (if n + i ≤ k then (p (k - n - i) : ℤ) else 0)

/-- Beck's conjecture, with `A014153` indexed from 1 (see the module docstring). -/
theorem main : ∀ k : ℕ, 1 ≤ k → (a (k - 1) : ℤ) = t 2 (k + 2) := by
  sorry

end OMA.S_oeis_a014153

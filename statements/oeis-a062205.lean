import Mathlib

/-!
# A062205: Number of alignments of n strings of length 4.

Source: https://oeis.org/A062205
Credit: @Solfanbtc

`a(n)` (offset 0) is row `4` of A262809: the number of lattice paths from `(4, ..., 4)` (`n`
coordinates) to `(0, ..., 0)` using steps that decrement one or more coordinates by one, i.e. the
number of alignments of `n` strings of length 4 (Slowinski 1998). The entries give the closed form
`A(r, n) = ∑_{j=0}^{r n} ∑_{i=0}^{j} (-1)^i C(j, i) C(j-i, r)^n` (A062204, A262809; it is the
formula of the entries' Maple program, which generates the data), used here as the definition
with `r = 4`: `1, 1, 321, 699121, 5552351121, ...`.

Conjectures (Peter Bala, Dec 19 2019, in the entry):
1. `a(n) ≡ 1 (mod 80)` for all `n ≥ 0`;
2. for every fixed modulus `k ≥ 1`, the sequence `a(n) mod k` is eventually periodic.
Both are stated, as a conjunction.

A python3 check: the formula reproduces the data; `a(n) ≡ 1 (mod 80)` for `0 ≤ n < 60`; and
`a(n) mod k` for `k = 3, 7, 9, 11, 13, 160` shows a period within the first 30 terms.
-/

namespace OMA.S_oeis_a062205

/-- `a n = ∑_{j=0}^{4n} ∑_{i=0}^{j} (-1)^i C(j, i) C(j-i, 4)^n`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (4 * n + 1), ∑ i ∈ Finset.range (j + 1),
    (-1) ^ i * (j.choose i : ℤ) * ((j - i).choose 4 : ℤ) ^ n

/-- Bala's conjectures: `a(n) ≡ 1 (mod 80)`, and `a(n) mod k` is eventually periodic for every
`k ≥ 1`. -/
theorem main : (∀ n : ℕ, a n ≡ 1 [ZMOD 80]) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ N T : ℕ, 0 < T ∧ ∀ n, N ≤ n → a (n + T) ≡ a n [ZMOD k]) := by
  sorry

end OMA.S_oeis_a062205

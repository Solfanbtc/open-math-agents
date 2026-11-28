import Mathlib

/-!
# A026836: partitions of n into distinct parts, the greatest being k

Source: https://oeis.org/A026836
Credit: @Solfanbtc

`T(n, k)` (`1 ≤ k ≤ n`) is the number of partitions of `n` into distinct parts with greatest part
`k`, i.e. the number of sets `s ⊆ {1, …, k}` with `k ∈ s` and `∑ s = n`. This reproduces all 91
data terms (rows `n = 1..13`).

A199918 (offset 0) is the "false theta series variation of Euler's pentagonal number series":
`∑_{k ≥ 1} Kronecker(-24, k) x^((k^2 - 1)/24)` (OEIS formula), i.e.
`A199918(n) = (-24 / k)` (Jacobi symbol) if `24n + 1 = k^2` with `k ≥ 1`, and `0` otherwise
(for such `k`, `k` is odd and the Kronecker symbol is the Jacobi symbol). The sum runs over
positive `k`: the data `1, 1, 1, 0, 0, 1, 0, -1, …` (all 105 terms reproduced) fix this reading.

Conjecture (George Beck, Jan 13 2019, OEIS comment):
`A199918(n) = ∑_{k=1}^{n} (-1)^(n-k) T(n, k)` for `n ≥ 1` (the rows of `T` start at `n = 1`).
Python: holds for `1 ≤ n ≤ 400`. (A199918 also records the q-series
`1 + ∑_{k>0} x^k ∏_{i=1}^{k-1} (1 + (-x)^i)` for its g.f., from which the claim follows; with the
theta-series definition used here it is a false-theta identity.)
-/

namespace OMA.S_oeis_a026836

/-- `T(n, k)`: partitions of `n` into distinct parts with greatest part `k`. -/
def T (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).powerset.filter fun s => k ∈ s ∧ ∑ i ∈ s, i = n).card

/-- A199918: `(-24 / k)` if `24n + 1 = k^2`, else `0`. -/
def A199918 (n : ℕ) : ℤ :=
  if (Nat.sqrt (24 * n + 1)) ^ 2 = 24 * n + 1 then jacobiSym (-24) (Nat.sqrt (24 * n + 1)) else 0

/-- Beck's conjecture: `A199918(n) = ∑_{k=1}^{n} (-1)^(n-k) T(n, k)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    A199918 n = ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (n - k) * T n k := by
  sorry

end OMA.S_oeis_a026836

import Mathlib

/-!
# A065204: first EKG term with n distinct prime factors

Source: https://oeis.org/A065204 (see A064413, A065203, A002110)
Credit: @Solfanbtc

A064413 is the EKG sequence: `e(1) = 1`, `e(2) = 2`, and for `n > 2`, `e(n)` is the smallest
number not already used which shares a factor with `e(n-1)`: 1, 2, 4, 6, 3, 9, 12, 8, ...
A065203(m) is the number of distinct primes dividing `e(m)`, and A065204(n) is described as the
least `m` with A065203(m) = n: 1, 3, 22, 191, 2206, ...

Conjecture (entry): `A064413(A065204(n)) = A002110(n)` (the primorial `p_1 p_2 ⋯ p_n`), i.e. the
first EKG term with exactly `n` distinct prime factors is the `n`-th primorial.

Minimal fix (indexing): the listed values of A065204 are one less than the EKG positions they
describe: the first EKG terms with 1, 2, 3, 4, ... distinct prime factors are `e(2) = 2`,
`e(4) = 6`, `e(23) = 30`, `e(192) = 210`, ..., at positions A065204(n) + 1 (read literally,
`e(A065204(2)) = e(3) = 4` is not `6`). We state the intended claim: for every `n ≥ 1`, at the least
position `m ≥ 1` with `ω(e(m)) = n`, `e(m)` is the `n`-th primorial.

Encoding: `ekgList n` is the list `[e(1), ..., e(n)]`; at each step the next term is searched
below `e(n-1) · (n + 1)`, which suffices since among the `n` multiples `e(n-1) · j`,
`2 ≤ j ≤ n + 1`, at least one is unused.

Sanity check (python, first 600000 terms): the first terms with `ω = 1, ..., 7` are at positions
2, 4, 23, 192, 2207, 29055, 497586 and equal 2, 6, 30, 210, 2310, 30030, 510510; `#eval` in Lean
gives the EKG terms.
-/

namespace OMA.S_oeis_a065204

/-- The list `[e(1), ..., e(n)]` of the first `n` EKG terms. -/
def ekgList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | n + 3 =>
    let l := ekgList (n + 2)
    let last := l.getLastD 1
    l ++ [((List.range (last * (n + 3) + 1)).find?
      (fun k => decide (0 < k) && decide (k ∉ l) && decide (1 < Nat.gcd k last))).getD 0]

/-- The EKG sequence A064413, `e(m)` for `m ≥ 1`. -/
def ekg (m : ℕ) : ℕ := (ekgList m).getLastD 0

/-- The `n`-th primorial A002110: the product of the first `n` primes. -/
noncomputable def primorialN (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- The conjecture: the first EKG term with exactly `n` distinct prime factors is the `n`-th
primorial. -/
theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → (ekg m).primeFactors.card = n →
    (∀ j, 1 ≤ j → j < m → (ekg j).primeFactors.card ≠ n) → ekg m = primorialN n := by
  sorry

end OMA.S_oeis_a065204

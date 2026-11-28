import Mathlib

/-!
# A002122: a(n) = Sum_{t=0..n} g(t)*g(n-t) where g(t) = A002121(t).

Source: https://oeis.org/A002122
Credit: @Solfanbtc

`g = A002121`: `g(0) = 1`, `g(1) = 0`, `g(2) = -1`, and for `n ≥ 3`,
`g(n) = -g(n-2) + ∑_{primes p, 3 ≤ p ≤ n} g(n-p)` (g.f. `1/(1 + ∑_{k>0} (-x)^prime(k))`).
`a(n) = ∑_{t=0}^{n} g(t) g(n-t)`: `1, 0, -2, 2, 3, -4, -1, 8, -1, -10, ...` (offset 0).

Conjecture (T. D. Noe, Dec 05 2006, in the entry): the last negative term appears to be
`a(485)`, i.e. `a(485) < 0` and `a(n) ≥ 0` for all `n > 485`.

A python3 check: the recurrence reproduces the data, and the negative terms below `n = 6000` end
with `a(478), a(482), a(485)`.

Conventions:
* `g` is computed by building the list `[g 0, ..., g n]`; in the step for `n + 3`, the sum over
  primes `p` with `3 ≤ p ≤ n + 3` is written over `i = n + 3 - p`, `0 ≤ i ≤ n`, keeping the terms
  with `n + 3 - i` prime.
* The Lean kernel (`decide`) confirms `g 0, ..., g 11 = 1, 0, -1, 1, 1, -1, 0, 2, 0, -2, 2, 4`
  and `a 0, ..., a 11 = 1, 0, -2, 2, 3, -4, -1, 8, -1, -10, 9, 16`, matching the data.
-/

namespace OMA.S_oeis_a002122

/-- `gs n = [g 0, g 1, ..., g n]` for `g = A002121`. -/
def gs : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 0]
  | 2 => [1, 0, -1]
  | n + 3 =>
      let L := gs (n + 2)
      L ++ [-(L.getD (n + 1) 0) +
        ∑ i ∈ Finset.range (n + 1), if (n + 3 - i).Prime then L.getD i 0 else 0]

/-- `g = A002121`. -/
def g (n : ℕ) : ℤ := (gs n).getD n 0

/-- `a(n) = ∑_{t=0}^{n} g(t) g(n-t)`. -/
def a (n : ℕ) : ℤ := ∑ t ∈ Finset.range (n + 1), g t * g (n - t)

/-- Noe's conjecture: the last negative term of A002122 is `a(485)`. -/
theorem main : a 485 < 0 ∧ ∀ n : ℕ, 485 < n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a002122

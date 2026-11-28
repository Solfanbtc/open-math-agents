import Mathlib

/-!
# A075344: Number of primes between consecutive terms of A075343

Source: https://oeis.org/A075344
Credit: @Solfanbtc

A075343: `b(1) = 1`, and `b(n+1)` is the smallest number such that there are `n` composite numbers
between `b(n)` and `b(n+1)` exclusive: `1, 5, 9, 15, 22, 29, 37, …` (all 38 data terms
reproduced). A075344 (offset 1): `a(n)` is the number of primes strictly between `b(n)` and
`b(n+1)`: `2, 1, 2, 2, 1, 1, 2, …`.

Conjecture (OEIS comment, also recorded in A075343 as "there exists a prime between consecutive
terms"): `a(n) > 0` for all `n ≥ 1`, i.e. there is a prime `p` with `b(n) < p < b(n+1)`.
-/

namespace OMA.S_oeis_a075344

/-- Number of composite numbers strictly between `x` and `m`. -/
def composites (x m : ℕ) : ℕ := ((Finset.Ioo x m).filter fun k => 1 < k ∧ ¬ k.Prime).card

/-- A075343 (offset 1; `b 0 = 0` is a placeholder). -/
noncomputable def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sInf {m : ℕ | b (n + 1) < m ∧ composites (b (n + 1)) m = n + 1}

/-- A075344: the number of primes strictly between `b(n)` and `b(n+1)`. -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Ioo (b n) (b (n + 1))).filter Nat.Prime).card

/-- Conjecture: `a(n) > 0` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a075344

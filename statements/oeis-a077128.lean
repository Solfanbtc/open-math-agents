import Mathlib

/-!
# A077128: Smallest number > previous term coprime to each of the next group of n numbers.

Source: https://oeis.org/A077128
Credit: @Solfanbtc

The positive integers are cut into consecutive groups of sizes `1, 2, 3, …`; the `n`-th group is
`T(n-1)+1, …, T(n)` with `T(k) = k(k+1)/2` (e.g. the 6th group is `16, …, 21`). `a(n)` is the
smallest number greater than `a(n-1)` that is coprime to every member of the `n`-th group. The
entry's data starts with `a(1) = 2`, which corresponds to `a(0) = 1` (every number is coprime to
the first group `{1}`). Such numbers exist (any prime larger than `a(n-1)` and `T(n)`), so the
infimum below is the genuine minimum.

Conjecture (entry): every member is a prime, i.e. `a(n)` is prime for all `n ≥ 1`.
Checked with python3: the definition reproduces the 53 listed terms (e.g. `a(6) = 23`), and
`a(n)` is prime for all `n ≤ 3000`.
-/

namespace OMA.S_oeis_a077128

/-- `T(k) = k(k+1)/2`. -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A077128, with `a 0 = 1`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {m : ℕ | a n < m ∧ ∀ k ∈ Finset.Icc (T n + 1) (T (n + 1)), Nat.Coprime m k}

/-- The conjecture: every term is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a077128

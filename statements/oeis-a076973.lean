import Mathlib

/-!
# A076973: Starting with 2, largest prime divisor of the sum of all previous terms.

Source: https://oeis.org/A076973
Credit: @Solfanbtc

Offset 1. For an initial value `m`, `a(1) = m` and, for `n ≥ 2`, `a(n)` is the largest prime
factor of `a(1) + ... + a(n-1)`; A076973 is the case `m = 2`. We checked (by `#eval`) that the
definition below with `m = 2` reproduces all terms of %S, %T, %U.

Conjecture (Benoit Cloitre, 2003): for every initial value `m ≥ 2`,
`a(n) = n/2 + O(log n)` (as `n → ∞`), and there are infinitely many primes `p` with `a(2p) = p`.
-/

namespace OMA.S_oeis_a076973

/-- The largest prime factor of `s` (`0` if `s ≤ 1`). -/
def lpf (s : ℕ) : ℕ := s.primeFactors.sup id

/-- `S m n = a(1) + ... + a(n)` for the sequence started at `a(1) = m`. -/
def S (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => m
  | n + 2 => S m (n + 1) + lpf (S m (n + 1))

/-- The sequence started at `a(1) = m` (offset 1; `a m 0` is an unused placeholder). -/
def a (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => m
  | n + 2 => lpf (S m (n + 1))

/-- Cloitre's conjecture, for every initial value `m ≥ 2`. -/
theorem main : ∀ m : ℕ, 2 ≤ m →
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (a m n : ℝ) - (n : ℝ) / 2)
      (fun n : ℕ => Real.log n) ∧
    {p : ℕ | p.Prime ∧ a m (2 * p) = p}.Infinite := by
  sorry

end OMA.S_oeis_a076973

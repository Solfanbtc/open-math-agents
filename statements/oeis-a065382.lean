import Mathlib

/-!
# A065382: Number of primes between n(n+1)/2 (exclusive) and (n+1)(n+2)/2 (inclusive).

Source: https://oeis.org/A065382
Credit: @Solfanbtc

`a(n) = π((n+1)(n+2)/2) - π(n(n+1)/2)` for `n ≥ 1`: 2, 1, 1, 2, 2, 1, 2, 3, ….

The entry says the sequence is "inspired by the weaker Legendre conjecture that there should be
at least one prime between n^2 and (n+1)^2". The conjecture it refers to is the analogue for
triangular numbers: `a(n) ≥ 1` for every `n ≥ 1`, i.e. there is always a prime `p` with
`n(n+1)/2 < p ≤ (n+1)(n+2)/2`. It is stronger than Legendre's conjecture: for `n ≥ 1`, the
interval `(n², (n+1)²)` contains a whole interval between consecutive triangular numbers.
Checked with python3: the formula reproduces the data, and `a(n) ≥ 1` for `1 ≤ n ≤ 3000`.
-/

namespace OMA.S_oeis_a065382

/-- A065382(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioc (n * (n + 1) / 2) ((n + 1) * (n + 2) / 2)).filter Nat.Prime).card

/-- There is always a prime between consecutive triangular numbers: `a(n) ≥ 1` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 1 ≤ a n := by
  sorry

end OMA.S_oeis_a065382

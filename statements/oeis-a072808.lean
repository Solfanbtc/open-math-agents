import Mathlib

/-!
# A072808: Smallest m such that sigma(m) mod phi(m) = n, or 0 if no solution exists

Source: https://oeis.org/A072808
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest `m` with `σ(m) mod φ(m) = n`, or `0` if no solution exists:
`4, 5, 8, 24, 0, 22, 16, 21, 450, …` (e.g. `σ(24) = 60`, `φ(24) = 8`, `60 mod 8 = 4`).

Conjecture (OEIS comment): "It is only conjectured that there are no solutions for `n` such that
`a(n) = 0`. The search for solutions tested all `m ≤ 10^10` for these `n`" (and, Giovanni Resta,
Apr 02 2020: "all zeros corresponding to odd terms `a(n)` with `n < 64` confirmed up to
`m ≤ 10^24`"). The data list 64 terms, with `a(n) = 0` exactly for
`n ∈ {5, 21, 25, 29, 37, 41, 45, 49, 53, 55, 57, 61}`; the conjecture is stated for these `n`:
no positive integer `m` has `σ(m) mod φ(m) = n`.
-/

namespace OMA.S_oeis_a072808

open ArithmeticFunction

/-- For each `n` with `a(n) = 0` in the data, no `m ≥ 1` has `σ(m) mod φ(m) = n`. -/
theorem main : ∀ n ∈ ({5, 21, 25, 29, 37, 41, 45, 49, 53, 55, 57, 61} : Finset ℕ),
    ∀ m : ℕ, 1 ≤ m → sigma 1 m % Nat.totient m ≠ n := by
  sorry

end OMA.S_oeis_a072808

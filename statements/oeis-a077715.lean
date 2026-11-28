import Mathlib

/-!
# A077715: a(1) = 7; thereafter a(n) = the smallest prime of the form d0...0a(n-1), where d is a single digit, or 0 if no such prime exists.

Source: https://oeis.org/A077715
Credit: @Solfanbtc

`a(n)` is the smallest prime obtained by prefixing `a(n-1)` with a number of the form
`d * 10^k`, `0 < d < 10`, `k ≥ 0`, i.e. a prime `a(n-1) + d * 10^m` with
`m = (number of decimal digits of a(n-1)) + k`, so `m ≥ (Nat.digits 10 (a (n-1))).length`.
If no such prime exists, `a(n) = 0` (we use `sInf ∅ = 0`).
We checked that this definition reproduces all 18 terms of %S, %T, %U (7, 17, 317, ...,
40209100020409305372126317).

Conjecture (from the entry): such a prime `d * 10^k` prefix always exists, i.e. for every
`n ≥ 1` there is a prime of the required form built on `a(n)` (so the sequence never
reaches 0).
-/

namespace OMA.S_oeis_a077715

/-- The primes of the form `d0...0k`: `k + d * 10^m` with `1 ≤ d ≤ 9` and `m` at least the
number of decimal digits of `k`. -/
def candidates (k : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ m ≥ (Nat.digits 10 k).length, ∃ d, 1 ≤ d ∧ d ≤ 9 ∧ p = k + d * 10 ^ m}

/-- A077715 with offset 1 (`a 0` is an unused placeholder). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 7
  | n + 2 => sInf (candidates (a (n + 1)))

/-- Conjecture: for every `n ≥ 1`, a prime of the form `d0...0a(n)` exists. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m ≥ (Nat.digits 10 (a n)).length, ∃ d, 1 ≤ d ∧ d ≤ 9 ∧
    (a n + d * 10 ^ m).Prime := by
  sorry

end OMA.S_oeis_a077715

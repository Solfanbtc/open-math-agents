import Mathlib

/-!
# A095415: repunit lengths whose prime factor-digit-excess is zero

Source: https://oeis.org/A095415 (with https://oeis.org/A095414 and https://oeis.org/A046413)
`R n = (10^n - 1) / 9` is the repunit of length `n`. A095414 is the excess of the total number
of decimal digits of the *distinct* prime factors of `R n` over `n` (so `A095414(1) = -1`, and
`R 9 = 3^2 * 37 * 333667` gives `1 + 2 + 6 - 9 = 0`). A095415 lists the `n ≥ 1` with excess 0:
2, 3, 5, 7, 9, 11, 13, 17, 19, 23, 27, 31, 47, ...
A046413 lists the `k` such that `R k` has exactly 2 prime factors, counted with multiplicity
(Mathematica `PrimeOmega`; e.g. `R 7 = 239 * 4649`).

Conjectures of the entry (Chai Wah Wu, Nov 03 2019), stated together as a conjunction:
1. "Except for the number 4, A046413 is a subsequence": every `k ≥ 1`, `k ≠ 4`, with
   `Ω(R k) = 2` has excess 0.
2. "Except for the prime powers 9 and 27, all terms are prime": every `n ≥ 1` with excess 0
   is prime or equal to 9 or 27.

Conventions. Indices start at 1 (offset 1 in both entries). The restriction `1 ≤ n` is needed:
`R 0 = 0` has no prime factors, so `n = 0` would have excess 0 and break conjecture 2.
Checked with `#eval`: the excess for `n = 1..13` is -1, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0,
as in A095414.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a095415

/-- The repunit of length `n`. -/
def R (n : ℕ) : ℕ := (10 ^ n - 1) / 9

/-- A095414: total number of decimal digits of the distinct prime factors of `R n`, minus `n`. -/
def excess (n : ℕ) : ℤ :=
  ((∑ p ∈ (R n).primeFactors, (Nat.digits 10 p).length : ℕ) : ℤ) - n

theorem main :
    (∀ k : ℕ, 1 ≤ k → k ≠ 4 → ArithmeticFunction.cardFactors (R k) = 2 → excess k = 0) ∧
    (∀ n : ℕ, 1 ≤ n → excess n = 0 → n.Prime ∨ n = 9 ∨ n = 27) := by
  sorry

end OMA.S_oeis_a095415

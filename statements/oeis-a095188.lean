import Mathlib

/-!
# A095188: primes formed by the digits after the decimal point of √n

Source: https://oeis.org/A095188
`a(n)` is the smallest prime formed by the digit string after the decimal point of `√n`, or 0 if
no such prime exists: the candidates are the numbers formed by the first `k ≥ 1` digits after the
decimal point, `⌊10^k * frac(√n)⌋` (e.g. `√7 = 2.64575131...` gives 6, 64, 645, 6457, 64575,
645751, and `a(7) = 645751`). The entry's conjecture: "a(n) is nonzero if n is not a perfect
square", i.e. for every non-square `n ≥ 1`, some `⌊10^k * frac(√n)⌋` with `k ≥ 1` is prime.

Conventions. `k ≥ 1` (at least one digit). Leading zeros after the decimal point only shorten the
number, as in the entry's Mathematica program, which uses `Floor[10^k FractionalPart[n^(1/2)]]`.
Checked with python3 (exact integer square roots, Miller-Rabin): this rule reproduces every
listed term `a(1..21)`, including 0 at the squares 1, 4, 9, 16.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a095188

/-- The number formed by the first `k` decimal digits after the point of `√n`. -/
noncomputable def prefixAfterPoint (n k : ℕ) : ℤ :=
  ⌊(10 : ℝ) ^ k * Int.fract (Real.sqrt n)⌋

theorem main : ∀ n : ℕ, 1 ≤ n → ¬ IsSquare n →
    ∃ k : ℕ, 1 ≤ k ∧ (prefixAfterPoint n k).natAbs.Prime := by
  sorry

end OMA.S_oeis_a095188

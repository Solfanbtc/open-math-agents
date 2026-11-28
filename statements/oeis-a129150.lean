import Mathlib

/-!
# A129150: The n-th arithmetic derivative of 2^3.

Source: https://oeis.org/A129150
Credit: @Solfanbtc

Conjecture (J. Lowell, Sep 10 2008, comment in A129150): a strictly increasing sequence.

Status: proved. David Radcliffe (Aug 19 2014, comment in A129150): "The sequence is strictly
increasing because `(4n)' = 4n + 4n'`" (every term is a multiple of 4, and `4 n' > 0` for
`n ≥ 2`). Stated faithfully as posed.

Definitions.
* The arithmetic derivative (A003415) of `n = Π p^e`: `n' = Σ_p e * (n / p)` (`0' = 1' = 0`,
  `p' = 1` for primes `p`), the same definition as in other statements of this repository.
* `a(n)` (offset 0) is the `n`-th iterate starting from `2^3 = 8`: `8, 12, 16, 32, 80, ...`.

Checked with python3: the iteration reproduces the first 17 listed terms.
-/

namespace OMA.S_oeis_a129150

/-- The arithmetic derivative `n' = Σ_{p | n} v_p(n) * (n / p)`. -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- A129150: the `n`-th arithmetic derivative of `8`. -/
def a (n : ℕ) : ℕ := arithmeticDerivative^[n] (2 ^ 3)

/-- A129150 is strictly increasing. -/
theorem main : StrictMono a := by
  sorry

end OMA.S_oeis_a129150

import Mathlib

/-!
# A139490: Numbers n such that the quadratic form x^2 + n*x*y + y^2 represents exactly the same primes as the quadratic form x^2 + m*y^2 for some m.

Source: https://oeis.org/A139490
Credit: @Solfanbtc

Conjecture (A. Jasinski, OEIS A139490): "This sequence is finite and complete". The original
check (n ≤ 200, m ≤ 500) missed three terms 58, 82, 86 (with m = 840, 840, 1848), found by
T. D. Noe (n ≤ 1000, m ≤ 4000), after which "the sequence is probably complete now". We state
completeness of the current list of all 15 terms:
1, 4, 6, 7, 8, 10, 14, 16, 18, 22, 26, 38, 58, 82, 86.

Conventions.
* "Represents" is over the integers: `p = x^2 + n x y + y^2` for some `x y : ℤ`. (The OEIS program
  searches `x, y ≥ 1`; a python3 check over `|x|, |y| ≤ 250`, `n ≤ 40`, primes below 30000 found no
  prime represented over `ℤ` but not over positive `x, y`.)
* `n` ranges over positive integers (offset 1, the program loops from 1; `n = 0` would match `m = 1`
  trivially).
* `m` ranges over positive integers (A139491 lists the `m`). Without `m ≥ 1`, `n = 2` would match
  `m = 0`, since `(x + y)^2` and `x^2` represent no prime.
Checked with python3 for `n ≤ 100`, `m ≤ 4000`, primes below 30000: exactly the 15 listed `n`
qualify, with the `m` given in the OEIS example (and 840, 840, 1848).
-/

namespace OMA.S_oeis_a139490

/-- Primes represented by `x^2 + n x y + y^2` over `ℤ`. -/
def primesMixed (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + (n : ℤ) * x * y + y ^ 2}

/-- Primes represented by `x^2 + m y^2` over `ℤ`. -/
def primesDiag (m : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + (m : ℤ) * y ^ 2}

/-- Conjecture: the 15 listed numbers are all the terms of A139490. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ∃ m : ℕ, 1 ≤ m ∧ primesMixed n = primesDiag m} =
      {1, 4, 6, 7, 8, 10, 14, 16, 18, 22, 26, 38, 58, 82, 86} := by
  sorry

end OMA.S_oeis_a139490

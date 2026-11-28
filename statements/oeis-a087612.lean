import Mathlib

/-!
# A087612: A divisibility sequence derived from Lehmer's polynomial x^10+x^9-x^7-x^6-x^5-x^4-x^3+x+1. Square root of the terms in A059928.

Source: https://oeis.org/A087612
Credit: @Solfanbtc

A059928(n) = |det(A^n - I)|, `A` the companion matrix of Lehmer's polynomial
`L(x) = x^10 + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1`, `I` the 10×10 identity; all its
terms are squares, and A087612(n) (offset 1) is the square root. We checked by computer that
`|det(A^n - I)| = A087612(n)^2` for all 72 terms of %S, %T, %U, with the matrix below
(ones on the subdiagonal, last column `-c_0, ..., -c_9` where `L = x^10 + Σ c_i x^i`).

Conjecture (stated in the entry, after Einsiedler–Everest–Ward): the sequence contains
infinitely many primes, i.e. infinitely many primes `p` are terms: `p^2 = |det(A^n - I)|`
for some `n ≥ 1`.
-/

namespace OMA.S_oeis_a087612

/-- Coefficients `c_0, ..., c_9` of `L(x) = x^10 + Σ c_i x^i`. -/
def c : Fin 10 → ℤ := ![1, 1, 0, -1, -1, -1, -1, -1, 0, 1]

/-- The companion matrix of Lehmer's polynomial. -/
def A : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 9 then -c i else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- A087612 contains infinitely many primes. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ ((A ^ n - 1).det).natAbs = p ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a087612

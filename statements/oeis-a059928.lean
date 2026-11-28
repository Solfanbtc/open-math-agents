import Mathlib

/-!
# A059928: periodic points of the toral automorphism of Lehmer's polynomial

Source: https://oeis.org/A059928 (and https://oeis.org/A087612)
Credit: @Solfanbtc

`A059928(n) = |det(A^n - I)|`, the number of points of period `n` of the toral automorphism
`x ↦ A x mod 1` on `[0,1)^10`, where `A` is the companion matrix of Lehmer's polynomial
`x^10 + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1` (conjecturally of smallest Mahler measure).
Offset 1: 1, 1, 1, 9, 1, 1, 1, 9, 1, 1, 1, 81, 1, 169, 841, ...

Conjecture (comment by T. D. Noe, Sep 15 2003; also A087612): the terms are all squares, and the
sequence of their square roots, A087612, contains infinitely many primes (Einsiedler, Everest,
Ward give heuristics and numerical evidence). We state the second part: infinitely many primes
`p` occur as `√(A059928(n))`, i.e. infinitely many primes `p` with `p^2 = A059928(n)` for some
`n ≥ 1` (for a term `p^2` the square root is exactly `p`, so this is literally "A087612 contains
infinitely many primes", with no assumption on the other terms).

`A` is the standard companion matrix (ones on the subdiagonal, last column `-c_0, ..., -c_9` with
`c_i` the coefficient of `x^i`); its characteristic polynomial is Lehmer's polynomial, so
`|det(A^n - I)| = |∏ (λ^n - 1)|` over its roots, as in the source. (The PARI program of the entry
lists the coefficients in the other order; Lehmer's polynomial is palindromic, so it is the same
matrix.)

Sanity check (python, exact integer determinants): this matrix gives all 57 listed terms, all of
them perfect squares.
-/

namespace OMA.S_oeis_a059928

/-- Coefficients `c_0, ..., c_9` of `x^0, ..., x^9` in Lehmer's polynomial. -/
def coeffs : Fin 10 → ℤ := ![1, 1, 0, -1, -1, -1, -1, -1, 0, 1]

/-- The companion matrix of Lehmer's polynomial. -/
def A : Matrix (Fin 10) (Fin 10) ℤ :=
  fun i j => if j = 9 then -coeffs i else if (i : ℕ) = j + 1 then 1 else 0

/-- `A059928(n) = |det(A^n - I)|`. -/
def a (n : ℕ) : ℕ := ((A ^ n - 1).det).natAbs

/-- The square roots of the terms (A087612) contain infinitely many primes. -/
theorem main : Set.Infinite {p : ℕ | p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ a n = p ^ 2} := by
  sorry

end OMA.S_oeis_a059928

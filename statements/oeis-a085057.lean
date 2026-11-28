import Mathlib

/-!
# A085057: a(n) is the smallest integer of the form a*b*c.../p*q*r..., where the numerator and the denominator contain n numbers each and a,b,c,...p,q,r... are all the integers from 1 to 2n.

Source: https://oeis.org/A085057
Credit: @Solfanbtc

Split `{1, …, 2n}` into two sets `A` (numerator) and `B` (denominator) of `n` elements each; `a(n)`
is the least integer value of `∏ A / ∏ B`, i.e. the least `x` with `∏ A = x · ∏ B`. Since
`(2n)! = x · (∏ B)^2`, every such `x` is at least the squarefree part of `(2n)!` (the squarefree
`s` with `(2n)! = s m^2`, here the product of the primes with odd exponent in `(2n)!`).

Conjecture (D. Reble, 2003; true for the first 3400 terms): `a(n)` always equals this lower
bound. `main` states it for all `n ≥ 1`: the squarefree part of `(2n)!` is the least such `x`.
(python3, brute force over all splittings for `n ≤ 9`: 2, 6, 5, 70, 7, 231, 858, 1430, 12155,
equal to the squarefree parts.)
-/

namespace OMA.S_oeis_a085057

/-- Squarefree part of `N`: the product of the primes with odd exponent in `N`. -/
def sqfPart (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors, p ^ (N.factorization p % 2)

/-- Integer values `∏ A / ∏ B` over splittings of `{1, …, 2n}` into two `n`-sets. -/
def Values (n : ℕ) : Set ℕ :=
  {x | ∃ A ⊆ Finset.Icc 1 (2 * n), A.card = n ∧
    ∏ i ∈ A, i = x * ∏ i ∈ Finset.Icc 1 (2 * n) \ A, i}

theorem main : ∀ n : ℕ, 1 ≤ n → IsLeast (Values n) (sqfPart (2 * n).factorial) := by
  sorry

end OMA.S_oeis_a085057

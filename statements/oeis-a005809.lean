import Mathlib

/-!
# A005809: a(n) = binomial(3n,n).

Source: https://oeis.org/A005809
Credit: @Solfanbtc

`a(n) = binomial(3*n, n)`, offset 0: 1, 3, 15, 84, 495, 3003, 18564, ...

Comment in the entry (Gary Detlefs, Mar 23 2013):

* Conjecture: `a(n) == 3 (mod n^3)` iff `n` is an odd prime.

The entry adds that `a(p) = binomial(3*p, p) == 3 (mod p^3)` for an odd prime `p` is a known
generalization of Wolstenholme's theorem (Mestrovic, Section 6, equation 35). The statement below
is the whole equivalence, both directions, as the comment states it.

Formalized: `a n = Nat.choose (3 * n) n`. `main` states, for every natural number `n` with
`1 < n`, that `a n ≡ 3 [MOD n ^ 3]` holds exactly when `n` is prime and odd. The range `1 < n` is
the only change to the literal wording, and it is forced: for `n = 1` every congruence modulo
`1 ^ 3 = 1` holds while `1` is not prime, so the literal claim fails there for a trivial reason
(the comment clearly means `n > 1`). For `0 < n < 1500` the equivalence was checked numerically;
`n = 1` is the only exception.
-/

namespace OMA.S_oeis_a005809

/-- A005809: `a(n) = binomial(3*n, n)`. -/
def a (n : ℕ) : ℕ := Nat.choose (3 * n) n

/-- Detlefs' conjecture: for `n > 1`, `a(n) == 3 (mod n^3)` if and only if `n` is an odd prime. -/
theorem main : ∀ n : ℕ, 1 < n → (a n ≡ 3 [MOD n ^ 3] ↔ n.Prime ∧ Odd n) := by
  sorry

end OMA.S_oeis_a005809

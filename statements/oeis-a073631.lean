import Mathlib

/-!
# A073631: Nonprimes k such that k divides 3^(k-1) - 2^(k-1).

Source: https://oeis.org/A073631
Credit: @Solfanbtc

Claims recorded in the entry (Alexander Adamchuk):
1. "It appears that a(1) = 1 and a(4) = 529 = 23^2 are the only perfect squares in a(n)."
2. "Conjecture: All nonsquarefree terms of a(n) are the multiples of 23^2."
`main` states both.

Terms: positive nonprime k (k = 1 included, as in the data 1, 65, 133, 529, ...) with
k ∣ 3^(k-1) - 2^(k-1) (the difference is a natural number since 3^(k-1) >= 2^(k-1)).
Checked numerically for k < 2 * 10^6 (340 terms): the squares are 1 and 529, and every
nonsquarefree term is a multiple of 529.
-/

namespace OMA.S_oeis_a073631

/-- `k` is a term of A073631. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ ¬ k.Prime ∧ k ∣ 3 ^ (k - 1) - 2 ^ (k - 1)

theorem main :
    (∀ k : ℕ, IsTerm k → IsSquare k → k = 1 ∨ k = 529) ∧
    (∀ k : ℕ, IsTerm k → ¬ Squarefree k → 23 ^ 2 ∣ k) := by
  sorry

end OMA.S_oeis_a073631

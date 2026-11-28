import Mathlib

/-!
# A098608: a(n) = 100^n.

Source: https://oeis.org/A098608
Credit: @Solfanbtc

Conjecture (OEIS A098608): the terms a(n) = 100^n (n >= 0) are the only positive squares whose
decimal digits all lie in {0, 1}.

`main`: a positive perfect square all of whose decimal digits are 0 or 1 is a power of 100.
(The converse is immediate: 100^n = (10^n)^2 has digits 1, 0, ..., 0.)
-/

namespace OMA.S_oeis_a098608

theorem main : ∀ m : ℕ, 0 < m → (∀ d ∈ Nat.digits 10 (m ^ 2), d = 0 ∨ d = 1) →
    ∃ n : ℕ, m ^ 2 = 100 ^ n := by
  sorry

end OMA.S_oeis_a098608

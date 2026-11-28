import Mathlib

/-!
# A002760: Squares and cubes.

Source: https://oeis.org/A002760
Credit: @Solfanbtc

A002760 lists the numbers that are squares or cubes: 0, 1, 4, 8, 9, 16, 25, 27, 36, ...
The entry's comment: "Catalan's Conjecture states that 8 and 9 are the only pair of
consecutive numbers in this sequence. The conjecture was established in 2003 by Mihailescu."

Formalized: if `n` and `n + 1` are both squares or cubes of natural numbers, then `n = 8`.
Minimal fix: the sequence starts with `0 = 0^2` and `1 = 1^2`, which are also consecutive
(a trivial pair, excluded in Catalan's conjecture by requiring positive bases), so `main`
allows `n = 0` as well. A brute-force search up to `10^7` finds only `n = 0` and `n = 8`.

This is the claim restricted to squares and cubes, as the comment states it; the general
Catalan conjecture (all exponents `≥ 2`) is upstream as
`FormalConjectures/Wikipedia/Catalan.lean` (`catalans_conjecture`), and implies it.
-/

namespace OMA.S_oeis_a002760

/-- `n` is a term of A002760: a square or a cube. -/
def IsSqOrCube (n : ℕ) : Prop := (∃ k : ℕ, n = k ^ 2) ∨ ∃ k : ℕ, n = k ^ 3

theorem main : ∀ n : ℕ, IsSqOrCube n → IsSqOrCube (n + 1) → n = 0 ∨ n = 8 := by
  sorry

end OMA.S_oeis_a002760

import Mathlib

/-!
# A060464: Numbers that are not congruent to 4 or 5 mod 9.

Source: https://oeis.org/A060464
Credit: @Solfanbtc

The entry carries two conjectures:
1. n is a sum of three cubes iff n is in this sequence (already stated upstream as
   `isSumOfThreeCubes_iff_mod_9` in FormalConjectures/Wikipedia/SumOfThreeCubes.lean);
2. (Heath-Brown) n is a sum of three cubes in infinitely many ways iff n is in this sequence,
   and not at all otherwise.
Conjecture 2 implies conjecture 1, so only conjecture 2 is stated here (it is not upstream).

Conventions.
* The sequence consists of the nonnegative integers n with n mod 9 ∉ {4, 5}; n ranges over ℕ.
* "Sum of three cubes" means of three integer cubes (x, y, z ∈ ℤ, signs allowed), as for the
  sums-of-three-cubes problem; "in infinitely many ways" means the set of triples
  (x, y, z) ∈ ℤ^3 with x^3 + y^3 + z^3 = n is infinite.
* "and not at all otherwise": for n ≡ 4, 5 (mod 9) the set of such triples is empty (this
  part is the elementary mod 9 obstruction, included since the entry states it).
-/

namespace OMA.S_oeis_a060464

/-- Representations of n as a sum of three integer cubes. -/
def reps (n : ℕ) : Set (ℤ × ℤ × ℤ) := {v | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2 ^ 3 = (n : ℤ)}

theorem main : ∀ n : ℕ,
    ((n % 9 ≠ 4 ∧ n % 9 ≠ 5) ↔ (reps n).Infinite) ∧
    ((n % 9 = 4 ∨ n % 9 = 5) → reps n = ∅) := by
  sorry

end OMA.S_oeis_a060464

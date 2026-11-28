import Mathlib

/-!
# A002149: Largest prime p==3 (mod 8) such that Q(sqrt(-p)) has class number 2n+1.

Source: https://oeis.org/A002149
Credit: @Solfanbtc

Claim of the entry: the listed values are correct. The entry says "Most of these values are
only conjectured to be correct" (D. Broadhurst computed class numbers for prime discriminants
with |D| < 10^9), and that Arno, Robinson & Wheeler prove a(0)-a(11).

Conventions.
* a(n) is the largest prime p ≡ 3 (mod 8) such that the imaginary quadratic field Q(√-p) has
  class number 2n + 1. The statement covers every listed term (%S and %T: n = 0, ..., 20).
* "Q(√-p) has class number h" is stated for every number field `K` of degree 2 over ℚ that
  contains a square root of -p (all such fields are isomorphic to Q(√-p)), using Mathlib's
  `NumberField.classNumber`. For each prime p such a field exists, so the condition is not
  vacuous.
* Data check (python3, counting reduced primitive binary quadratic forms of discriminant -p,
  which for p ≡ 3 (mod 4) prime is the class number of Q(√-p)): among primes p ≡ 3 (mod 8)
  below 600000, the largest with class number 2n + 1 is the listed a(n) for every n ≤ 20.
-/

namespace OMA.S_oeis_a002149

/-- `Q(√-p)` has class number `h`. -/
def HasClassNumber (p h : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    (∃ x : K, x ^ 2 = -(p : K)) → NumberField.classNumber K = h

/-- The listed terms a(0), ..., a(20). -/
def listed : List ℕ :=
  [163, 907, 2683, 5923, 10627, 15667, 20563, 34483, 37123, 38707, 61483, 90787,
    93307, 103387, 166147, 133387, 222643, 210907, 158923, 253507, 296587]

theorem main : ∀ n : ℕ, n < listed.length →
    IsGreatest {p : ℕ | p.Prime ∧ p % 8 = 3 ∧ HasClassNumber p (2 * n + 1)}
      (listed.getD n 0) := by
  sorry

end OMA.S_oeis_a002149

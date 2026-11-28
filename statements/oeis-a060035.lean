import Mathlib

/-!
# A060035: Least m >= 0 such that 2^m has n 2's in its base-3 expansion.

Source: https://oeis.org/A060035
Credit: @Solfanbtc

Conjecture (OEIS A060035): "the value of a(42) is conjectured to be -1 because no power of 2 up to
2^10^7 has exactly 42 2's" (the old name: a(n) = -1 if no power of 2 has n 2's in base 3). So the
conjecture is that no power of 2 has exactly 42 digits 2 in its ternary expansion. Together with
the listed terms a(0..41) and the values a(43..59) given in the entry ("after a(42), that is
unknown, the sequence goes on 171, 142, ..."), `main` states:
* for n <= 41 and for 43 <= n <= 59, a(n) is the least m with exactly n ternary 2s in 2^m, with the
  listed values;
* no m has exactly 42 ternary 2s in 2^m.
Erdős's conjecture quoted in the entry (2^n has a ternary digit 2 for n > 8) is already stated
upstream and in statements/oeis-a117971.lean, and is not restated.
-/

namespace OMA.S_oeis_a060035

/-- Number of digits 2 in the base-3 expansion of 2^m. -/
def twos (m : ℕ) : ℕ := (Nat.digits 3 (2 ^ m)).count 2

/-- The listed terms a(0), ..., a(41). -/
def termsLow : List ℕ :=
  [0, 1, 3, 12, 9, 16, 15, 19, 27, 30, 44, 40, 55, 52, 65, 60, 51, 75, 73, 80, 86, 82, 81, 77,
   98, 85, 95, 79, 118, 141, 162, 107, 129, 105, 158, 145, 155, 143, 138, 152, 203, 176]

/-- The values a(43), ..., a(59) given in the entry. -/
def termsHigh : List ℕ :=
  [171, 142, 167, 197, 168, 216, 229, 193, 232, 236, 248, 226, 230, 224, 228, 303, 244]

theorem main :
    (∀ n : ℕ, n < 42 → IsLeast {m : ℕ | twos m = n} (termsLow.getD n 0)) ∧
    (∀ n : ℕ, 43 ≤ n → n < 60 → IsLeast {m : ℕ | twos m = n} (termsHigh.getD (n - 43) 0)) ∧
    (∀ m : ℕ, twos m ≠ 42) := by
  sorry

end OMA.S_oeis_a060035

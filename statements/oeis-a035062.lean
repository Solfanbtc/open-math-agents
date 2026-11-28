import Mathlib

/-!
# A035062: Numbers n such that 2^n does not contain the digit 7.

Source: https://oeis.org/A035062
Credit: @Solfanbtc

Conjecture (OEIS A035062): 71 is the last term. Together with the listed terms (all 30 terms of
%S/%T), this says that the n with no digit 7 in the decimal expansion of 2^n are exactly
0, 1, ..., 14, 16, 18, 19, 22, 23, 25, 28, 33, 41, 42, 49, 50, 54, 61, 71. Checked numerically
for n < 5000.
-/

namespace OMA.S_oeis_a035062

theorem main :
    {n : ℕ | 7 ∉ Nat.digits 10 (2 ^ n)} =
      ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 22, 23, 25, 28, 33, 41, 42,
        49, 50, 54, 61, 71} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a035062

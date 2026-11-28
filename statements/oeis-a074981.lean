import Mathlib

/-!
# A074981: Positive numbers which are not of the form r^i - s^j (conjectured list).

Source: https://oeis.org/A074981
Credit: @Solfanbtc

The entry is a "Conjectured list of positive numbers which are not of the form r^i - s^j, where
r, s, i, j are integers with r > 0, s > 0, i > 1, j > 1"; "the terms shown are only conjectured
values" (they are not differences of two powers below 10^27, Fiorentini 2020). The conjecture
stated: the positive integers m ≤ 426 (the last listed term) that are not of this form are
exactly the 52 listed terms 6, 14, 34, ..., 422, 426 (all terms of %S, %T, %U).

Conventions.
* m is "of the form r^i - s^j" iff there are naturals r, s ≥ 1 and i, j ≥ 2 with
  m = r^i - s^j (in ℤ). The listed terms being consecutive terms of the sequence, the
  conjecture says exactly that, for 1 ≤ m ≤ 426, m is not of this form iff m is listed.
* python3: with all powers up to 10^12, every m ≤ 426 not in the list is a difference of two
  powers, and the listed ones have no such representation in that range.
-/

namespace OMA.S_oeis_a074981

/-- m is a difference of two perfect powers r^i - s^j with r, s > 0 and i, j > 1. -/
def IsPowerDiff (m : ℕ) : Prop :=
  ∃ r s i j : ℕ, 0 < r ∧ 0 < s ∧ 1 < i ∧ 1 < j ∧ (m : ℤ) = (r : ℤ) ^ i - (s : ℤ) ^ j

/-- The listed terms of A074981. -/
def listed : Finset ℕ :=
  {6, 14, 34, 42, 50, 58, 62, 66, 70, 78, 82, 86, 90, 102, 110, 114, 130, 134, 158, 178, 182,
    202, 206, 210, 226, 230, 238, 246, 254, 258, 266, 274, 278, 290, 302, 306, 310, 314, 322,
    326, 330, 358, 374, 378, 390, 394, 398, 402, 410, 418, 422, 426}

theorem main : ∀ m : ℕ, 1 ≤ m → m ≤ 426 → (¬ IsPowerDiff m ↔ m ∈ listed) := by
  sorry

end OMA.S_oeis_a074981

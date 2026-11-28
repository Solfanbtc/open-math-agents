import Mathlib

/-!
# A075788: If n can be written in the form r^i-s^j (see A074981), where r,s,i,j are integers with r>0, s>0, i>1, j>1 choose the representation with smallest r^i (in case of ties, minimize i and j); or if n is not of this form set r=s=i=j=0; sequence gives values of r.

Source: https://oeis.org/A075788
Credit: @Solfanbtc

Conjecture (OEIS A075788): "The zeros are only conjectures (cf. A074981)": the listed terms equal
to 0, at n = 6, 14, 34, 42, 50, 58, 62, 66, 70, 78, 82, 86, 90, are numbers n that cannot be
written as r^i - s^j with integers r, s > 0 and i, j > 1.

`main`: for 1 <= n <= 91 (the listed range), n has no such representation iff n is one of these
13 zero positions. The "if" direction is the conjecture (the zeros are genuine); the "only if"
direction holds by the representations behind the nonzero listed terms (e.g. 1 = 3^2 - 2^3,
2 = 3^3 - 5^2, 3 = 2^2 - 1^2). The values of r themselves are not restated.
-/

namespace OMA.S_oeis_a075788

/-- `n` is a difference of two perfect powers `r^i - s^j` with `r, s > 0`, `i, j > 1`. -/
def IsPowerDiff (n : ℕ) : Prop :=
  ∃ r s i j : ℕ, 0 < r ∧ 0 < s ∧ 1 < i ∧ 1 < j ∧ (n : ℤ) = (r : ℤ) ^ i - (s : ℤ) ^ j

/-- The positions of the zeros among the listed terms. -/
def zeros : Finset ℕ := {6, 14, 34, 42, 50, 58, 62, 66, 70, 78, 82, 86, 90}

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 91 → (¬ IsPowerDiff n ↔ n ∈ zeros) := by
  sorry

end OMA.S_oeis_a075788

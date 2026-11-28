import Mathlib

/-!
# A060774: a(n) = number of lattice paths from (0,0,0) to (n,n,n) along the cracks on the surface of a Rubik-ized n X n X n cube so that no step increases distance from goal.

Source: https://oeis.org/A060774
Credit: @Solfanbtc

Conjectures (R. J. Mathar, OEIS A060774, %F, Oct 31 2015):
1. 2n(2n-1)(n-1) a(n) + (n-1)(13n^2-209n+258) a(n-1) + 2(-259n^3+1785n^2-3728n+2460) a(n-2)
   + 6(295n^3-2068n^2+4833n-3780) a(n-3) - 36(3n-10)(2n-7)(3n-11) a(n-4) = 0.
2. 2n(n-1)(2n-1)(11n^2-33n+24) a(n) - (n-1)(473n^4-1892n^3+2561n^2-1338n+216) a(n-1)
   + 6(3n-5)(3n-4)(2n-3)(11n^2-11n+2) a(n-2) = 0.
`main` is the conjunction of 1 and 2.

Minimal fix: both recurrences fail at their smallest index, where a(0) = 1 enters: 1 fails at
n = 4 and 2 fails at n = 2 (the closed form below gives 0 at n = 0, not a(0) = 1). Both hold
from the next index on, so 1 is stated for n ≥ 5 and 2 for n ≥ 3.

Conventions:
* a(n) is given by the entry's formula a(n) = 6 binomial(3n, n) - 6 binomial(2n, n) for n ≥ 1
  (a(1) = 6: the 6 orders XYZ, ..., ZYX), with a(0) = 1 (offset 0).
* The recurrences are stated in ℤ with the index shifted (`n + 5`, resp. `n + 3`) to avoid
  natural subtraction.
* Checked in Python: `a` reproduces every term of %S, %T, %U; recurrence 1 holds exactly for
  5 ≤ n < 300 (and fails at n = 4), recurrence 2 for 3 ≤ n < 300 (and fails at n = 2).
-/

namespace OMA.S_oeis_a060774

/-- A060774: `6 C(3n,n) - 6 C(2n,n)` for `n ≥ 1`, and `a 0 = 1`. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else 6 * (Nat.choose (3 * n) n : ℤ) - 6 * (Nat.choose (2 * n) n : ℤ)

/-- Mathar's two conjectured recurrences (from the first index where they hold). -/
theorem main :
    (∀ n : ℕ, let m : ℤ := n + 5;
      2 * m * (2 * m - 1) * (m - 1) * a (n + 5) + (m - 1) * (13 * m ^ 2 - 209 * m + 258) * a (n + 4)
        + 2 * (-259 * m ^ 3 + 1785 * m ^ 2 - 3728 * m + 2460) * a (n + 3)
        + 6 * (295 * m ^ 3 - 2068 * m ^ 2 + 4833 * m - 3780) * a (n + 2)
        - 36 * (3 * m - 10) * (2 * m - 7) * (3 * m - 11) * a (n + 1) = 0) ∧
    (∀ n : ℕ, let m : ℤ := n + 3;
      2 * m * (m - 1) * (2 * m - 1) * (11 * m ^ 2 - 33 * m + 24) * a (n + 3)
        - (m - 1) * (473 * m ^ 4 - 1892 * m ^ 3 + 2561 * m ^ 2 - 1338 * m + 216) * a (n + 2)
        + 6 * (3 * m - 5) * (3 * m - 4) * (2 * m - 3) * (11 * m ^ 2 - 11 * m + 2) * a (n + 1) = 0) := by
  sorry

end OMA.S_oeis_a060774

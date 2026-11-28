import Mathlib

/-!
# A049608: a(n)=T(n,n+2), array T as in A049600.

Source: https://oeis.org/A049608
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Oct 26 2015, OEIS A049608): for n >= 2 (offset 0, so that a(n-2) is a
term),
  (n-1)(2n-1)(n+2) a(n) - 12n(n-1)(n+1) a(n-1) + (n-2)(2n+1)(n+1) a(n-2) = 0.

The array T of A049600 counts lattice paths (see its name); the entry gives the closed form
T(n, k) = Σ_{j=0..n-1} binomial(k+j, j) binomial(n-1, j) (Paul D. Hanna; David Callan explains that
it counts the paths of the name by their number j of interior vertices), with T(0, k) = 0 (the
empty sum, the initial row of zeros). We use this closed form. a(n) = T(n, n+2).
Checked numerically: the rows of A049600 (e.g. 8, 20, 38, 63, 96, 138 for n = 4) and all 17
listed terms 0, 1, 6, 34, 190, ... are reproduced, and the recurrence holds for 2 <= n < 200.
-/

namespace OMA.S_oeis_a049608

/-- The array A049600. -/
def T (n k : ℕ) : ℕ := ∑ j ∈ Finset.range n, (k + j).choose j * (n - 1).choose j

/-- a(n) = T(n, n + 2). -/
def a (n : ℕ) : ℕ := T n (n + 2)

theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) - 1) * (2 * n - 1) * (n + 2) * a n - 12 * (n : ℤ) * (n - 1) * (n + 1) * a (n - 1)
      + ((n : ℤ) - 2) * (2 * n + 1) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a049608

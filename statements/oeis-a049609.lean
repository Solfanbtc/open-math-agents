import Mathlib

/-!
# A049609: a(n)=T(n,n+3), array T as in A049600.

Source: https://oeis.org/A049609
Credit: @Solfanbtc

Conjectures (R. J. Mathar, OEIS A049609, %F, Oct 26 2015):
1. -(n+3)*(n-1)*a(n) +(7*n^2+8*n-9)*a(n-1) +(-7*n^2+8*n+9)*a(n-2) +(n+1)*(n-3)*a(n-3) = 0.
2. +n*(n+3)*(n-1)*a(n) -(2*n+1)*(3*n^2+3*n-4)*a(n-1) +(n-2)*(n+2)*(n+1)*a(n-2) = 0.
`main` is the conjunction of 1 and 2.

Conventions:
* T is the array A049600, T(i,j) = number of lattice paths of the title. We use its formula
  T(i, j) = Sum_{r=0..i-1} C(j+r, r) * C(i-1, r) (Paul D. Hanna; David Callan explains it as
  counting the paths by their number r of interior vertices). So
  a(n) = T(n, n+3) = Sum_{r=0..n-1} C(n+3+r, r) * C(n-1, r), with a(0) = 0 (offset 0).
* The recurrences are stated in ℤ for every `n` at which all indices are ≥ 0, i.e. n ≥ 3 for 1
  and n ≥ 2 for 2. In Lean the index `n` is shifted (`n + 3`, resp. `n + 2`) to avoid natural
  subtraction.
* Checked in Python: `a` reproduces every term of %S, %T (n ≤ 16); recurrence 1 holds for
  3 ≤ n < 400 and recurrence 2 for 2 ≤ n < 400.
-/

namespace OMA.S_oeis_a049609

/-- A049609: `T(n, n+3) = Σ_{r<n} C(n+3+r, r) C(n-1, r)`. -/
def a (n : ℕ) : ℤ :=
  ∑ r ∈ Finset.range n, ((Nat.choose (n + 3 + r) r * Nat.choose (n - 1) r : ℕ) : ℤ)

/-- Mathar's two conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, let m : ℤ := n + 3;
      -(m + 3) * (m - 1) * a (n + 3) + (7 * m ^ 2 + 8 * m - 9) * a (n + 2)
        + (-7 * m ^ 2 + 8 * m + 9) * a (n + 1) + (m + 1) * (m - 3) * a n = 0) ∧
    (∀ n : ℕ, let m : ℤ := n + 2;
      m * (m + 3) * (m - 1) * a (n + 2) - (2 * m + 1) * (3 * m ^ 2 + 3 * m - 4) * a (n + 1)
        + (m - 2) * (m + 2) * (m + 1) * a n = 0) := by
  sorry

end OMA.S_oeis_a049609

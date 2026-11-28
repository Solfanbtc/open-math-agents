import Mathlib

/-!
# A055838: T(2n+4,n), where T is the array in A055830.

Source: https://oeis.org/A055838
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A055838, %F, Mar 13 2016):
5*n*(n+3)*(n-1)*a(n) -2*(n-1)*(11*n+8)*(n+2)*a(n-1) -3*(3*n-1)*(3*n-2)*(n+1)*a(n-2) = 0.

Conventions:
* T = A055830 (diagonal differences of A037027), defined by its g.f.
  (1 - y z)/(1 - y (1 + y + z)) = Σ T(n,k) y^n z^k. Since
  1/(1 - y(1+y+z)) = Σ_m y^m (1+y+z)^m, its coefficient of y^n z^k is
  U(n,k) = Σ_m C(m,k) C(m-k, n-m), and T(n,k) = U(n,k) - U(n-1,k-1) (with U = 0 at negative
  indices). This gives the rows 1; 1,0; 2,1,0; 3,3,1,0; 5,7,4,1,0; ... of the entry.
* a(n) = T(2n+4, n), offset 0. The recurrence involves a(n-2), so it is stated for n ≥ 2; in
  Lean the index is shifted (`n + 2`) to avoid natural subtraction, and the identity is in ℤ.
* Checked in Python: rows 0..7 of T match the example triangle of A055830, a(0..19)
  reproduces %S, %T, %U, and the recurrence holds for 2 ≤ n < 300.
-/

namespace OMA.S_oeis_a055838

/-- The coefficient of `y^n z^k` in `1/(1 - y(1+y+z))`. -/
def U (n k : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), Nat.choose m k * Nat.choose (m - k) (n - m) *
    (if k ≤ m ∧ n - m ≤ m - k then 1 else 0)

/-- A055830: `T(n,k) = U(n,k) - U(n-1,k-1)`. -/
def T (n k : ℕ) : ℤ :=
  (U n k : ℤ) - (if 1 ≤ n ∧ 1 ≤ k then (U (n - 1) (k - 1) : ℤ) else 0)

/-- A055838: `T(2n+4, n)`. -/
def a (n : ℕ) : ℤ := T (2 * n + 4) n

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, let m : ℤ := n + 2;
      5 * m * (m + 3) * (m - 1) * a (n + 2) - 2 * (m - 1) * (11 * m + 8) * (m + 2) * a (n + 1)
        - 3 * (3 * m - 1) * (3 * m - 2) * (m + 1) * a n = 0 := by
  sorry

end OMA.S_oeis_a055838

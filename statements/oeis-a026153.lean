import Mathlib

/-!
# A026153: T(n,n-2), where T is the array in A026148.

Source: https://oeis.org/A026153
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A026153, formula section, Jun 23 2013):
-(n+8)*(n-118)*a(n) +(-n^2-561*n-2878)*a(n-1) +2*(38*n^2+203*n-1070)*a(n-2)
+2*(-116*n^2+781*n+2493)*a(n-3) +(13*n^2-1012*n+3888)*a(n-4) +3*(107*n-423)*(n-4)*a(n-5) = 0.

Conventions:
* A026148 is the irregular triangle T: T(0,0) = 1; row 1 is 1, 1; row 2 is 1, 1, 2, 1, 1; and for
  n ≥ 3, T(n,0) = 1, T(n,1) = n-1, T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k) for
  k = 2..n+1, and T(n,n+2) = T(n-1,n) + T(n-1,n+1) (the last clause of the name,
  T(n,k+2) = T(n-1,k) + T(n-1,k+1), read at k = n; this reproduces the example rows of
  A026148). Entries outside a row are 0.
* a(n) = T(n, n-2) with offset 2: 1, 2, 7, 20, 60, ... Checked in Python: all 27 listed terms.
* The recurrence involves a(n-5), so it is stated for n ≥ 7 (all indices within the offset);
  it is evaluated in ℤ. Checked in Python for 7 ≤ n < 300.
-/

namespace OMA.S_oeis_a026153

/-- The triangle A026148 (0 outside the rows). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | 2, k => [1, 1, 2, 1, 1].getD k 0
  | n + 3, k =>
    if k = 0 then 1
    else if k = 1 then n + 2
    else if k ≤ n + 4 then T (n + 2) (k - 2) + T (n + 2) (k - 1) + T (n + 2) k
    else if k = n + 5 then T (n + 2) (n + 3) + T (n + 2) (n + 4)
    else 0

/-- A026153: `a(n) = T(n, n-2)` (offset 2). -/
def a (n : ℕ) : ℤ := T n (n - 2)

/-- Mathar's conjectured holonomic recurrence for A026153. -/
theorem main : ∀ n : ℤ, 7 ≤ n →
    -(n + 8) * (n - 118) * a n.toNat + (-n ^ 2 - 561 * n - 2878) * a (n - 1).toNat
      + 2 * (38 * n ^ 2 + 203 * n - 1070) * a (n - 2).toNat
      + 2 * (-116 * n ^ 2 + 781 * n + 2493) * a (n - 3).toNat
      + (13 * n ^ 2 - 1012 * n + 3888) * a (n - 4).toNat
      + 3 * (107 * n - 423) * (n - 4) * a (n - 5).toNat = 0 := by
  sorry

end OMA.S_oeis_a026153

import Mathlib

/-!
# A026299: Row sums of the array A026268 (a path-counting sequence).

Source: https://oeis.org/A026299
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
(n+2)*a(n) + (-3n-4)*a(n-1) + (-n+2)*a(n-2) + 3(n-4)*a(n-3) = 0.

Conventions.
* Definition. The entry's name describes paths s(0..n) with s(0) = 0, s(1) = 1, ... but a
  literal brute-force count of that description gives 1, 1, 2, 5, 14, 39, ... which is NOT the
  data (1, 3, 7, 19, 53, 149, ...); the description is garbled (it even requires a step
  condition "if s(2) = 1", impossible under the other conditions). The data were produced by
  R. J. Mathar's Maple program (in the entry, "Corrected and extended" by him) from the second
  description, "sum of numbers in row n+1 of the array T in A026268", with a(0) = 1. We use that:
  T is the triangle of A026268 (T(n,k) = 1 for n < 3, T(3,1) = T(3,2) = T(3,3) = 2, T(n,0) = 1,
  T(n,1) = n-1, T(n,n) = T(n-1,n-2) + T(n-1,n-1), otherwise T(n,k) = T(n-1,k-2) + T(n-1,k-1) +
  T(n-1,k), for 0 ≤ k ≤ n), a(0) = 1 and a(n) = Σ_{k=0}^{n+1} T(n+1,k) for n ≥ 1. Checked with
  python3: this reproduces all 29 listed terms (n = 0..28).
* Range. The recurrence involves a(n-3); it holds for 4 ≤ n ≤ 28 but fails at n = 3
  (5·19 - 13·7 - 1·3 + (-3)·1 = -2 ≠ 0, since a(0) = 1 is a special value), so the minimal fix
  states it for n ≥ 4.
-/

namespace OMA.S_oeis_a026299

/-- The triangle A026268 (with T(n,k) = 0 for k > n). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k ≤ 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | 2, k => if k ≤ 2 then 1 else 0
  | 3, k => if k = 0 then 1 else if k ≤ 3 then 2 else 0
  | n + 4, k =>
    if n + 4 < k then 0
    else if k = 0 then 1
    else if k = 1 then n + 3
    else if k = n + 4 then T (n + 3) (n + 2) + T (n + 3) (n + 3)
    else T (n + 3) (k - 2) + T (n + 3) (k - 1) + T (n + 3) k

/-- A026299. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ k ∈ Finset.range (n + 2), T (n + 1) k

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n + (-3 * (n : ℤ) - 4) * a (n - 1) + (-(n : ℤ) + 2) * a (n - 2)
      + 3 * ((n : ℤ) - 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026299

import Mathlib

/-!
# A026598: a(n) = Sum{i=0..n} Sum{j=0..i} T(i,j), T given by A026584.

Source: https://oeis.org/A026598
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 23 2013, OEIS A026598): for n >= 6 (offset 0, so that a(n-6) is a
term),
  n a(n) - (4n-3) a(n-1) - (2n-3) a(n-2) + 5(4n-9) a(n-3) - 7(n-3) a(n-4) - 6(4n-15) a(n-5)
  + 8(2n-9) a(n-6) = 0.

Definition of T (A026584, from its name): row i has entries j = 0..2i; T(i,0) = T(i,2i) = 1 for
i >= 0; T(i,1) = T(i,2i-1) = floor(i/2) for i >= 1; for i >= 2 and 2 <= j <= 2i-2,
T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i+j is odd and T(i-1,j-2) + T(i-1,j) if i+j is
even. T(i,j) = 0 for j > 2i (outside the row). The inner sum of a(n) runs over j = 0..i only,
as in the entry.
Checked numerically: the rows 1; 1 0 1; 1 1 2 1 1; ... of A026584 and all 28 listed terms of
A026598 are reproduced, and the recurrence holds for 6 <= n < 150.
-/

namespace OMA.S_oeis_a026598

/-- The triangle A026584. -/
def T : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j =>
    if j = 0 ∨ j = 2 * (i + 1) then 1
    else if 2 * (i + 1) < j then 0
    else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 1) / 2
    else if Odd (i + 1 + j) then T i (j - 2) + T i (j - 1) + T i j
    else T i (j - 2) + T i j

/-- a(n) = Σ_{i=0..n} Σ_{j=0..i} T(i, j). -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), T i j

theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℤ) * a n - (4 * (n : ℤ) - 3) * a (n - 1) - (2 * (n : ℤ) - 3) * a (n - 2)
      + 5 * (4 * (n : ℤ) - 9) * a (n - 3) - 7 * ((n : ℤ) - 3) * a (n - 4)
      - 6 * (4 * (n : ℤ) - 15) * a (n - 5) + 8 * (2 * (n : ℤ) - 9) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a026598

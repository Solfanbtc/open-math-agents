import Mathlib

/-!
# A026070: number of integer (s(0), ..., s(n)) with s(0) = 0, |s(i) - s(i-1)| = 1 for i = 1, 2, |s(i) - s(i-1)| ≤ 1 for i ≥ 3, s(n) = 3.

Source: https://oeis.org/A026070
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A026070, formula section, Jun 23 2013):
(n+3)*a(n) +(-5*n-6)*a(n-1) +(3*n-11)*a(n-2) +(11*n-8)*a(n-3) +2*(-2*n+17)*a(n-4)
+6*(-n+6)*a(n-5) = 0.

Conventions:
* a(n) is the number of sequences (s(0), ..., s(n)) of integers (no sign condition) with
  s(0) = 0, |s(i) - s(i-1)| = 1 for i = 1, 2 (i ≤ n), |s(i) - s(i-1)| ≤ 1 for 3 ≤ i ≤ n, and
  s(n) = 3 (the name). The set is finite (|s(i)| ≤ i); a(n) is its cardinality. Offset 3:
  a(3) = 1, a(4) = 2, a(5) = 8, ... Checked in Python (dynamic programming): all 27 listed
  terms.
* The recurrence involves a(n-5), so it is stated for n ≥ 8 (all indices within the offset);
  it is evaluated in ℤ. Checked in Python for 8 ≤ n < 300 (it holds from n = 6 on).
-/

namespace OMA.S_oeis_a026070

/-- The sequences counted by A026070(n): step `i` goes from `s (i-1)` to `s i`. -/
def Walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | s 0 = 0 ∧ s (Fin.last n) = 3 ∧
    ∀ i : Fin n,
      (i.val + 1 ≤ 2 → |s i.succ - s i.castSucc| = 1) ∧
      (3 ≤ i.val + 1 → |s i.succ - s i.castSucc| ≤ 1)}

/-- A026070 (offset 3). -/
noncomputable def a (n : ℕ) : ℤ := Nat.card (Walks n)

/-- Mathar's conjectured holonomic recurrence for A026070. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℤ) + 3) * a n + (-5 * (n : ℤ) - 6) * a (n - 1) + (3 * (n : ℤ) - 11) * a (n - 2)
      + (11 * (n : ℤ) - 8) * a (n - 3) + 2 * (-2 * (n : ℤ) + 17) * a (n - 4)
      + 6 * (-(n : ℤ) + 6) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026070

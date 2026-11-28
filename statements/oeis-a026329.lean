import Mathlib

/-!
# A026329: number of (s(0), ..., s(n)) with s(i) ≥ 0, |s(i) - s(i-1)| ≤ 1 for i = 1..n, s(0) = 2, s(n) = 6.

Source: https://oeis.org/A026329
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A026329, formula section, Jun 23 2013):
-(n+10)*(n-4)*a(n) +3*(2*n+15)*(n-4)*a(n-1) +3*(-3*n^2-n+68)*a(n-2) -4*(n+4)*(n-1)*a(n-3)
+12*(n-1)*(n-2)*a(n-4) = 0.

Conventions:
* a(n) is the number of sequences (s(0), ..., s(n)) of nonnegative integers with s(0) = 2,
  s(n) = 6 and |s(i) - s(i-1)| ≤ 1 for 1 ≤ i ≤ n (the name). The set is finite
  (s(i) ≤ i + 2); a(n) is its cardinality. Offset 4: a(4) = 1, a(5) = 5, a(6) = 21, ...
  Checked in Python (dynamic programming): all 26 listed terms.
* The recurrence involves a(n-4), so it is stated for n ≥ 8 (all indices within the offset);
  it is evaluated in ℤ. Checked in Python for 8 ≤ n < 300.
-/

namespace OMA.S_oeis_a026329

/-- The sequences counted by A026329(n). -/
def Walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = 2 ∧ s (Fin.last n) = 6 ∧
    ∀ i : Fin n, |(s i.succ : ℤ) - (s i.castSucc : ℤ)| ≤ 1}

/-- A026329 (offset 4). -/
noncomputable def a (n : ℕ) : ℤ := Nat.card (Walks n)

/-- Mathar's conjectured holonomic recurrence for A026329. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) + 10) * ((n : ℤ) - 4) * a n + 3 * (2 * (n : ℤ) + 15) * ((n : ℤ) - 4) * a (n - 1)
      + 3 * (-3 * (n : ℤ) ^ 2 - n + 68) * a (n - 2)
      - 4 * ((n : ℤ) + 4) * ((n : ℤ) - 1) * a (n - 3)
      + 12 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026329

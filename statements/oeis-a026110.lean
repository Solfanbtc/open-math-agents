import Mathlib

/-!
# A026110: number of (s(0), ..., s(n)) with s(i) ≥ 0, s(0) = 0, s(1) = 1, s(n) = 4, |s(i) - s(i-1)| ≤ 1 for i ≥ 2.

Source: https://oeis.org/A026110
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A026110, formula section, Jun 23 2013):
-(n+6)*(n-4)*a(n) +(4*n^2-n-51)*a(n-1) +(-2*n^2+11*n+18)*a(n-2) -(4*n-1)*(n-3)*a(n-3)
+3*(n-3)*(n-4)*a(n-4) = 0.

Conventions:
* a(n) is the number of sequences (s(0), ..., s(n)) of nonnegative integers with s(0) = 0,
  s(1) = 1, s(n) = 4 and |s(i) - s(i-1)| ≤ 1 for 2 ≤ i ≤ n (the name). Such sequences satisfy
  s(i) ≤ i, so the set is finite; a(n) is its cardinality (`Nat.card`), for n ≥ 1.
  Offset 4: a(4) = 1, a(5) = 4, a(6) = 15, ... Checked in Python (dynamic programming): all
  26 listed terms.
* The recurrence involves a(n-4), so it is stated for n ≥ 8 (all indices within the offset);
  it is evaluated in ℤ. Checked in Python for 8 ≤ n < 300.
-/

namespace OMA.S_oeis_a026110

/-- The sequences counted by A026110(n). -/
def Walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = 0 ∧ (∀ i : Fin (n + 1), (i : ℕ) = 1 → s i = 1) ∧ s (Fin.last n) = 4 ∧
    ∀ i : Fin n, 1 ≤ (i : ℕ) →
      |(s i.succ : ℤ) - (s i.castSucc : ℤ)| ≤ 1}

/-- A026110 (offset 4). -/
noncomputable def a (n : ℕ) : ℤ := Nat.card (Walks n)

/-- Mathar's conjectured holonomic recurrence for A026110. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) + 6) * ((n : ℤ) - 4) * a n + (4 * (n : ℤ) ^ 2 - n - 51) * a (n - 1)
      + (-2 * (n : ℤ) ^ 2 + 11 * n + 18) * a (n - 2)
      - (4 * (n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 3)
      + 3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026110

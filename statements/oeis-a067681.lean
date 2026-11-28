import Mathlib

/-!
# A067681: Diagonals and antidiagonals of the prime-composite array, B(m,n) which are zeros from the Third Borve Conjecture.

Source: https://oeis.org/A067681
Credit: @Solfanbtc

The Third Borve Conjecture (OEIS A067681): there are infinitely many integers m for which the
m-th diagonal and the m-th antidiagonal of the prime-composite array are both zero-only.

Definitions (from the entry): c(m) is the m-th composite (c(1) = 4) and p(n) the n-th prime
(p(1) = 2); B(m, n) is the exponent of p(n) in c(m) (the entry says "highest power", but its table
and examples give the exponent, e.g. B(34, 3) = 2 for c(34) = 50; zero-ness is the same either
way). The m-th diagonal is B(m, 1), B(m+1, 2), B(m+2, 3), ... (infinite); the m-th antidiagonal is
B(m, 1), B(m-1, 2), ..., B(1, m). Indices are 1-based, so c(m) = `Nat.nth` composite at m - 1.
The listed terms (8, 12, 35, 73, ...) are not restated: each is an infinite condition on its
diagonal. Checked numerically: with the diagonal truncated at 5000 entries, the m < 1700 with both
lines zero are exactly the 17 listed terms.
-/

namespace OMA.S_oeis_a067681

/-- The m-th composite number (m ≥ 1). -/
noncomputable def c (m : ℕ) : ℕ := Nat.nth (fun k => 1 < k ∧ ¬ k.Prime) (m - 1)

/-- The n-th prime (n ≥ 1). -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- B(m, n): the exponent of p(n) in c(m). -/
noncomputable def B (m n : ℕ) : ℕ := padicValNat (p n) (c m)

/-- The m-th diagonal and the m-th antidiagonal are zero-only. -/
def BothZero (m : ℕ) : Prop :=
  (∀ i : ℕ, B (m + i) (i + 1) = 0) ∧ (∀ i : ℕ, i < m → B (m - i) (i + 1) = 0)

theorem main : {m : ℕ | 1 ≤ m ∧ BothZero m}.Infinite := by
  sorry

end OMA.S_oeis_a067681

import Mathlib

/-!
# A296516: a(n) is the number of terms in expanded form of bivariate polynomial Q_n, where (P_n, Q_n) is defined by: P_0 = x, Q_0 = y, P_(n+1) = P_n + Q_n, Q_(n+1) = P_n * Q_n.

Source: https://oeis.org/A296516
Credit: @Solfanbtc

The entry records three conjectured formulas, stated together in `main`:
1. (L. Rousseau) for n > 0,
   a(n) = F(n+1)^2 - T(n-1) - T(F(n-1)) - 2 V(n) - 2 W(n), where F = Fibonacci,
   T(m) = m(m+1)/2, V(n) = Σ_{i=1..n-4} F(i) Σ_{j=i+1..n-3} (n-2-j) F(j),
   W(n) = Σ_{i=1..n-3} (n-2-i) T(F(i)) (empty sums are 0);
2. (C. Barker) a(n) = 7a(n-1) - 18a(n-2) + 20a(n-3) - 6a(n-4) - 6a(n-5) + 5a(n-6) - a(n-7)
   for n > 7 (equivalent to the stated generating function given the initial terms);
3. (L. Rousseau) for n > 0, a(n) = (F(2n+1) + F(n+2) - n^2 + n - 2) / 2, stated as
   2 a(n) = F(2n+1) + F(n+2) - n^2 + n - 2 in ℤ.
(The closed form golden-ratio expression of the entry is the same as 3, rewritten with Binet.)

Conventions: P_n, Q_n live in `MvPolynomial (Fin 2) ℤ` with x = X 0, y = X 1; the number of
terms of Q_n in expanded form is the cardinality of its support (all coefficients are
positive, so nothing cancels). Checked with python3 against brute force (n ≤ 10) and the
data: all three formulas hold on the listed terms; the ranges are sharp (the recurrence
fails at n = 7, formula 3 fails at n = 0).
-/

namespace OMA.S_oeis_a296516

open MvPolynomial

/-- The pair (P_n, Q_n). -/
noncomputable def PQ : ℕ → MvPolynomial (Fin 2) ℤ × MvPolynomial (Fin 2) ℤ
  | 0 => (X 0, X 1)
  | n + 1 => ((PQ n).1 + (PQ n).2, (PQ n).1 * (PQ n).2)

/-- a(n): the number of terms of Q_n. -/
noncomputable def a (n : ℕ) : ℤ := ((PQ n).2.support.card : ℤ)

/-- Fibonacci numbers, as integers. -/
def F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

/-- Triangular numbers T(m) = m(m+1)/2. -/
def T (m : ℤ) : ℤ := m * (m + 1) / 2

/-- V(n) = Σ_{i=1..n-4} F(i) Σ_{j=i+1..n-3} (n-2-j) F(j). -/
def V (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 (n - 4), F i * ∑ j ∈ Finset.Icc (i + 1) (n - 3), ((n : ℤ) - 2 - j) * F j

/-- W(n) = Σ_{i=1..n-3} (n-2-i) T(F(i)). -/
def W (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 (n - 3), ((n : ℤ) - 2 - i) * T (F i)

theorem main :
    (∀ n : ℕ, 0 < n →
      a n = F (n + 1) ^ 2 - T ((n : ℤ) - 1) - T (F (n - 1)) - 2 * V n - 2 * W n) ∧
    (∀ n : ℕ, 7 < n →
      a n = 7 * a (n - 1) - 18 * a (n - 2) + 20 * a (n - 3) - 6 * a (n - 4) - 6 * a (n - 5) +
        5 * a (n - 6) - a (n - 7)) ∧
    (∀ n : ℕ, 0 < n →
      2 * a n = F (2 * n + 1) + F (n + 2) - (n : ℤ) ^ 2 + n - 2) := by
  sorry

end OMA.S_oeis_a296516

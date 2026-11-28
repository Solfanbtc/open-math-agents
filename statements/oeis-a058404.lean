import Mathlib

/-!
# A058404: Coefficient triangle of polynomials (falling powers) related to Pell number convolutions. Companion triangle is A058405.

Source: https://oeis.org/A058404
Credit: @Solfanbtc

Conjecture (OEIS A058404, comment): a(k,0) = A057084(k) for k >= 0, where A057084 is given by
A057084(0) = 1, A057084(1) = 8, A057084(n) = 8*(A057084(n-1) - A057084(n-2)) (%F of A057084).

Definition of the triangle (from the comments of A058404, A058402): P0(n) = A000129(n+1)
(Pell numbers 1, 2, 5, 12, ...), and Pk is the k-th convolution of P0 with itself
(Pk(n) = A054456(n+k,k), i.e. the coefficients of (Σ P0(n) x^n)^(k+1)). The row polynomials
p(k,x) = Σ_m a(k,m) x^(k-m) and their companions q(k,x) (A058405), of degree ≤ k, satisfy
  P_{k+1}(n) = (p(k,n)(n+1) 2 P0(n+1) + q(k,n)(n+2) P0(n)) / ((k+1)! 8^(k+1))  for all n ≥ 0.
So a(k,0) is the coefficient of x^k in p(k,x).

Conventions:
* We use this identity as the definition of the triangle and do not reproduce the recursion
  quoted in A058402 (as transcribed it gives 56, 368, 564 instead of row 2 = 56, 376, 588). For
  each k, `main` asserts that polynomials p, q over ℚ of degree ≤ k satisfying the identity
  exist, and that every such p has coefficient of x^k equal to A057084(k). (The identity
  determines p and q uniquely.)
* Checked in Python with exact rationals: for k = 0..5 the identity (imposed for n < 40) has a
  unique solution, whose p reproduces the listed rows 1; 8,22; 56,376,588; ...; and the leading
  coefficients are 1, 8, 56, 384, 2624, 17920 = A057084(0..5).
-/

namespace OMA.S_oeis_a058404

open Polynomial

/-- `P0(n) = A000129(n+1)`: 1, 2, 5, 12, 29, ... -/
def P0 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * P0 (n + 1) + P0 n

/-- `Pconv j` is the `j`-th convolution of `P0` with itself (`Pconv 0 = P0`). -/
def Pconv : ℕ → ℕ → ℕ
  | 0, n => P0 n
  | j + 1, n => ∑ i ∈ Finset.range (n + 1), P0 i * Pconv j (n - i)

/-- A057084. -/
def A057084 : ℕ → ℤ
  | 0 => 1
  | 1 => 8
  | n + 2 => 8 * (A057084 (n + 1) - A057084 n)

/-- The defining identity of the row polynomials `p(k,·)`, `q(k,·)`. -/
def Identity (k : ℕ) (p q : ℚ[X]) : Prop :=
  ∀ n : ℕ, (Pconv (k + 1) n : ℚ) * (k + 1).factorial * 8 ^ (k + 1) =
    p.eval (n : ℚ) * (n + 1) * 2 * P0 (n + 1) + q.eval (n : ℚ) * (n + 2) * P0 n

/-- The conjecture `a(k,0) = A057084(k)`. -/
theorem main :
    ∀ k : ℕ, (∃ p q : ℚ[X], p.natDegree ≤ k ∧ q.natDegree ≤ k ∧ Identity k p q) ∧
      ∀ p q : ℚ[X], p.natDegree ≤ k → q.natDegree ≤ k → Identity k p q →
        p.coeff k = (A057084 k : ℚ) := by
  sorry

end OMA.S_oeis_a058404

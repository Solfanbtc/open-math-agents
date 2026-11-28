import Mathlib

/-!
# A105794: Inverse of a generalized Stirling number triangle of first kind.

Source: https://oeis.org/A105794
Credit: @Solfanbtc

T(n, k) = Sum_{i=0..n} (-1)^(n-i) * binomial(n, i) * Stirling2(i, k) (formula of P. Bala,
Jan 13 2014, used by the entry's Maple and Mathematica programs), for 0 ≤ k ≤ n.
Rows: 1; -1, 1; 1, -1, 1; -1, 1, 0, 1; 1, -1, 1, 2, 1; ...

Conjectures (W. Schulte, Feb 15 2025, in the FORMULA section), stated together:
1. Sum_{k=0..n} (-1)^(n-k) * T(n, k) * (k+m)! / m! = (m+2)^n for all n ≥ 0 and m ≥ 0.
2. (-1)^n - B(n) = Sum_{k=1..n} (-1)^k * T(n, k) * (k-1)! / (k+1) for all n ≥ 0, where
   B(n) = B(n, 0) is the n-th Bernoulli number with B(1) = -1/2 (Mathlib's `bernoulli`).

`(k+m)!/m!` is an integer and is written as Mathlib's `Nat.ascFactorial (m+1) k`
(= (m+1)(m+2)...(m+k)); conjecture 2 is taken in `ℚ`. Both were checked numerically
(conjecture 1 for n < 12, m < 8; conjecture 2 for n < 14).
-/

namespace OMA.S_oeis_a105794

/-- The triangle A105794. -/
def T (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1) ^ (n - i) * (n.choose i : ℤ) * (Nat.stirlingSecond i k : ℤ)

theorem main :
    (∀ n m : ℕ, ∑ k ∈ Finset.range (n + 1),
        (-1) ^ (n - k) * T n k * ((m + 1).ascFactorial k : ℤ) = ((m : ℤ) + 2) ^ n) ∧
    (∀ n : ℕ, (-1 : ℚ) ^ n - bernoulli n = ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ k * (T n k : ℚ) * ((k - 1).factorial : ℚ) / ((k : ℚ) + 1)) := by
  sorry

end OMA.S_oeis_a105794

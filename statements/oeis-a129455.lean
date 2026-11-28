import Mathlib

/-!
# A129455: An analog of Pascal's triangle based on A129454. T(n, k) = A129454(n+1)/(A129454(n-k+1)*A129454(k+1)).

Source: https://oeis.org/A129455
Credit: @Solfanbtc

A129454(n) = ∏_{i=1}^{n-1} ∏_{j=1}^{n-1} ∏_{k=1}^{n-1} gcd(i, j, k) (an empty product is `1`, so
A129454(0) = A129454(1) = 1), and for `0 ≤ k ≤ n`,
T(n, k) = A129454(n+1) / (A129454(n-k+1) * A129454(k+1)).

Conjecture (P. Bala, OEIS A129455): for all `0 ≤ k ≤ n`,
1. T(n, k) is an integer, i.e. `A129454(n-k+1) * A129454(k+1)` divides `A129454(n+1)`;
2. the binomial coefficient `C(n, k)` divides `T(n, k)`;
3. `T(n, k) / C(n, k)` is a perfect sixth power.
All three claims are stated together, with `T(n, k)` the exact quotient in `ℕ` (by claim 1).

Checked: `#eval` of these definitions gives all 45 listed terms (rows n = 0..8); python3 confirms
the three claims for all `0 ≤ k ≤ n ≤ 67`.
-/

namespace OMA.S_oeis_a129455

/-- A129454(n) = ∏_{1 ≤ i, j, k ≤ n-1} gcd(i, j, k). -/
def A129454 (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 (n - 1), ∏ j ∈ Finset.Icc 1 (n - 1), ∏ k ∈ Finset.Icc 1 (n - 1),
    Nat.gcd (Nat.gcd i j) k

/-- T(n, k) = A129454(n+1) / (A129454(n-k+1) * A129454(k+1)) (quotient in `ℕ`). -/
def T (n k : ℕ) : ℕ := A129454 (n + 1) / (A129454 (n - k + 1) * A129454 (k + 1))

/-- Conjecture: T(n, k) is an integer, `C(n, k) ∣ T(n, k)`, and `T(n, k) / C(n, k)` is a
perfect sixth power, for all `0 ≤ k ≤ n`. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    A129454 (n - k + 1) * A129454 (k + 1) ∣ A129454 (n + 1) ∧
    Nat.choose n k ∣ T n k ∧
    ∃ m : ℕ, T n k / Nat.choose n k = m ^ 6 := by
  sorry

end OMA.S_oeis_a129455

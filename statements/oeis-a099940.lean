import Mathlib

/-!
# A099940: a(n) = 2*(A056855(n)) /(phi(n)*n), where phi() is the Euler phi function.

Source: https://oeis.org/A099940
Credit: @Solfanbtc

A056855(n) = `(∏ k) · (∑ 1/k)`, product and sum over `1 ≤ k ≤ n` with `gcd(k, n) = 1`
(an integer: `∑_k ∏_{j ≠ k} j`). A099940 (offset 1) is `a(n) = 2 · A056855(n) / (φ(n) · n)`:
2, 1, 1, 1, 5, 1, 84, 11, ...; e.g. `a(6) = 2 · (1 + 1/5) · 1 · 5 / (6 · 2) = 1`.

Conjecture (L. Quet, 2004, in the entry): every term is an integer (checked for `n ≤ 5000` by
D. Reble). Status: B. Cloitre remarks in the entry that this follows from Leudesdorf's theorem
(Hardy and Wright, An Introduction to the Theory of Numbers, 5th ed., pp. 100-102), so it is a
known result.
-/

namespace OMA.S_oeis_a099940

/-- A056855(n) = (∏ k) · (∑ 1/k) over `1 ≤ k ≤ n` coprime to `n`. -/
def A056855 (n : ℕ) : ℚ :=
  (∏ k ∈ (Finset.Icc 1 n).filter (Nat.Coprime · n), (k : ℚ)) *
    ∑ k ∈ (Finset.Icc 1 n).filter (Nat.Coprime · n), (1 / (k : ℚ))

/-- A099940(n) = 2 · A056855(n) / (φ(n) · n). -/
def a (n : ℕ) : ℚ := 2 * A056855 n / ((Nat.totient n : ℚ) * n)

/-- Every term of A099940 is an integer. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = z := by
  sorry

end OMA.S_oeis_a099940

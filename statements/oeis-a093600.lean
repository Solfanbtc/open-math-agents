import Mathlib

/-!
# A093600: Numerator of Sum_{1<=k<=n, gcd(k,n)=1} 1/k.

Source: https://oeis.org/A093600
Credit: @Solfanbtc

`a(n)` is the numerator (in lowest terms) of `∑_{1 ≤ k ≤ n, gcd(k,n)=1} 1/k`, and `b(n)` is the
numerator of `∑_{1 ≤ k ≤ n, gcd(k,n)=1} 1/k²` (offset 1: `n ≥ 1`).

Conjecture (Thomas Ordowski, Aug 12 2019, in the OEIS entry): if, for some `e > 0`,
`n^e ∣ a(n)`, then `n^(e-1) ∣ b(n)`.

The entry also records the related observation that for odd `n` the implication appears to be an
equivalence, and asks whether there are `n > 1` with `n^4 ∣ a(n)`; those are not stated here.
Checked numerically (python3, exact fractions) for all `1 ≤ n ≤ 600`: no counterexample.
-/

namespace OMA.S_oeis_a093600

/-- `a(n)`: numerator of `∑_{1 ≤ k ≤ n, gcd(k,n)=1} 1/k`. -/
def a (n : ℕ) : ℤ :=
  (∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n), (1 : ℚ) / k).num

/-- `b(n)`: numerator of `∑_{1 ≤ k ≤ n, gcd(k,n)=1} 1/k²`. -/
def b (n : ℕ) : ℤ :=
  (∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n), (1 : ℚ) / (k : ℚ) ^ 2).num

/-- Ordowski's conjecture: `n^e ∣ a(n)` with `e > 0` implies `n^(e-1) ∣ b(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ e : ℕ, 0 < e →
    (n : ℤ) ^ e ∣ a n → (n : ℤ) ^ (e - 1) ∣ b n := by
  sorry

end OMA.S_oeis_a093600

import Mathlib

/-!
# A037097: Periodic vertical binary vectors of powers of 3, starting from bit-column 2 (halved).

Source: https://oeis.org/A037097
Credit: @Solfanbtc

`a(n) = Σ_{k=0..2^(n-1)-1} (floor(3^k / 2^n) mod 2) * 2^k` (offset 2; Maple program of the
entry: bit `n` of `3^k` becomes bit `k` of `a(n)`), giving `0, 12, 120, 57120, ...`.

Conjecture (corrected by Qiyuan Gu, Jul 24 2026): for `n ≥ 3`, `a(n)`, read as a
`GF(2)[X]`-polynomial (bit `k` = coefficient of `X^k`), is divisible by `(X + 1)^A000225(n-2)`,
where `A000225(m) = 2^m - 1`. (The entry's second sentence, "if this holds, then ...", only
names the quotient through A048720 and A136386 and is not a separate claim.)
Checked (python3): the divisibility holds for `3 ≤ n ≤ 12`, and fails for the exponent
`2^(n-2)` in each of those cases.
-/

namespace OMA.S_oeis_a037097

open Polynomial

/-- Bit `n` of `3^k`. -/
def bit (n k : ℕ) : ℕ := (3 ^ k / 2 ^ n) % 2

/-- A037097(n). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n - 1)), bit n k * 2 ^ k

/-- `a(n)` as a `GF(2)[X]`-polynomial: coefficient of `X^k` is bit `k` of `a(n)`. -/
noncomputable def P (n : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ Finset.range (2 ^ (n - 1)), C (bit n k : ZMod 2) * X ^ k

/-- The conjecture: `(X + 1)^(2^(n-2) - 1)` divides `a(n)` in `GF(2)[X]` for `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → (X + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 2) - 1) ∣ P n := by
  sorry

end OMA.S_oeis_a037097

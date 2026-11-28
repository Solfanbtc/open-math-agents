import Mathlib

/-!
# A079450: a(n) = 2^(n-1)*u(n) where u(1)=1 and u(n) = frac(3/2*u(n-1)) + 1.

Source: https://oeis.org/A079450
Credit: @Solfanbtc

`u(1) = 1`, `u(n) = frac(3/2 · u(n-1)) + 1` (fractional part), `a(n) = 2^(n-1) u(n)`; `a(n)` is
an integer, but we work in `ℚ`, which does not change the claim. The definition reproduces
every term of %S, %T, %U (checked in Python).

Greedy powers of `2/3` (A077468): scanning `k = 1, 2, 3, …`, the exponent `k` is taken when
adding `(2/3)^k` to the sum of the powers already taken keeps it `< 1` (the Mathematica program
of A077468; the sum can never equal `1` exactly, since `3^N ≠ Σ 2^k 3^(N-k)` with all `k ≥ 1`
by parity). This scan is the same as the entry's definition ("the smallest exponent that does
not cause the sum to exceed unity"), because after taking the smallest admissible `e` the
remainder is `< (2/3)^e / 2 < (2/3)^e`, so the next greedy exponent is larger than `e`. It
reproduces every listed term of A077468 (checked in Python).

Conjecture (Benoit Cloitre, in the entry): for `n ≥ 1`, `a(n+1) = 3 a(n)` iff `n` is a greedy
power of `2/3`. (The entry also notes `a(n+1) ≤ 3 a(n)`, which is not part of the conjecture.)
Checked in Python with exact arithmetic for `1 ≤ n < 1500`.
-/

namespace OMA.S_oeis_a079450

/-- `u(n)`; position `0` is unused (set to `1`). -/
def u : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => Int.fract (3 / 2 * u (n + 1)) + 1

/-- A079450 (in `ℚ`). -/
def a (n : ℕ) : ℚ := 2 ^ (n - 1) * u n

/-- `s k`: the sum of `(2/3)^e` over the greedy exponents `e ≤ k`. -/
def s : ℕ → ℚ
  | 0 => 0
  | k + 1 => if s k + (2 / 3) ^ (k + 1) < 1 then s k + (2 / 3) ^ (k + 1) else s k

/-- `k` is a greedy power of `2/3` (a term of A077468). -/
def Greedy (k : ℕ) : Prop := 1 ≤ k ∧ s (k - 1) + (2 / 3) ^ k < 1

theorem main : ∀ n : ℕ, 1 ≤ n → (a (n + 1) = 3 * a n ↔ Greedy n) := by
  sorry

end OMA.S_oeis_a079450

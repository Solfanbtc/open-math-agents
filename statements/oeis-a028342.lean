import Mathlib

/-!
# A028342: Expansion of `∏_{i ≥ 1} (1 - x^i)^(-1/i)`

Source: https://oeis.org/A028342
Credit: @Solfanbtc

`a(n)` (offset 0) is `n!` times the coefficient of `x^n` in `∏_{i≥1} (1 - x^i)^(-1/i)
= exp(∑_{n≥1} d(n) x^n / n)` (an e.g.f.), `d` = number of divisors. Here `a` is defined by the
OEIS formula (Kruchinin) `a(0) = 1`, `a(n) = (n-1)! ∑_{i=0}^{n-1} d(i+1) a(n-i-1)/(n-i-1)!`,
written over ℕ as `a(n) = ∑_{i<n} d(i+1) · (n-1)(n-2)⋯(n-i) · a(n-1-i)` (descending factorial
`(n-1)!/(n-1-i)!`). It reproduces all 23 data terms `1, 1, 3, 11, 59, 339, 2629, …`.

Conjecture (Peter Bala, Nov 14 2017, OEIS comment), for all `n ≥ 0` and `k ≥ 1`:
1. if `k` is odd, `k ∣ a(n+k) + a(n)`;
2. if `k` is even and `k ≡ 0, 2` or `6 (mod 8)`, `k ∣ a(n+k) - a(n)`;
3. if `k ≡ 4 (mod 8)`, `k ∣ 2 (a(n+k) - a(n))`.
(The consequences about periodicity modulo `k`, and the period 10 modulo 10, follow from these.)

Status: SOLVED. The OEIS entry says "Peter Bala's conjectures are correct (see Kallat, 2026)"
(Ahaan Kallat, Jul 23 2026). Stated here faithfully. Checked with Python for `k < 60`,
`n < 120`.
-/

namespace OMA.S_oeis_a028342

/-- A028342 by the recurrence `a(n) = ∑_{i<n} d(i+1) (n-1)!/(n-1-i)! a(n-1-i)`, `a(0) = 1`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1),
      (Nat.divisors (i.1 + 1)).card * n.descFactorial i.1 * a (n - i.1)
decreasing_by omega

/-- Peter Bala's three congruences for A028342 (proved by Kallat, 2026). -/
theorem main : ∀ n k : ℕ, 1 ≤ k →
    (k % 2 = 1 → (k : ℤ) ∣ (a (n + k) : ℤ) + a n) ∧
    (k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 6 → (k : ℤ) ∣ (a (n + k) : ℤ) - a n) ∧
    (k % 8 = 4 → (k : ℤ) ∣ 2 * ((a (n + k) : ℤ) - a n)) := by
  sorry

end OMA.S_oeis_a028342

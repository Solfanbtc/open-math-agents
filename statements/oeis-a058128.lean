import Mathlib

/-!
# A058128: a(1) = 1, a(n) = (n^n-n)/(n-1)^2 for n >= 2.

Source: https://oeis.org/A058128
Credit: @Solfanbtc

Conjecture (Davide Rotondo, Nov 06 2024): "For even n, a(n) is prime or a weak Fermat
pseudoprime to base n."

Conventions.
* The offset is 1, so "even n" means `n ≥ 2` even.
* `(n^n - n)/(n-1)^2` is an exact division for `n ≥ 2` (`a(n) = Σ_{k=1}^{n} k n^(n-k-1)`), so
  natural-number division is used.
* A weak Fermat pseudoprime to base `b` is a composite `m` with `b^m ≡ b (mod m)`; composite means
  `m > 1` and not prime. A python check confirms the conjecture for all even `n < 400` (it fails
  for odd `n`, e.g. `n = 5`).
-/

namespace OMA.S_oeis_a058128

/-- `a(1) = 1`, `a(n) = (n^n - n)/(n-1)^2` for `n ≥ 2`. -/
def a (n : ℕ) : ℕ := if n = 1 then 1 else (n ^ n - n) / (n - 1) ^ 2

/-- `m` is a weak Fermat pseudoprime to base `b`: `m` is composite and `b^m ≡ b (mod m)`. -/
def IsWeakFermatPsp (m b : ℕ) : Prop := 1 < m ∧ ¬ m.Prime ∧ b ^ m ≡ b [MOD m]

/-- For every even `n ≥ 2`, `a(n)` is prime or a weak Fermat pseudoprime to base `n`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → Even n → (a n).Prime ∨ IsWeakFermatPsp (a n) n := by
  sorry

end OMA.S_oeis_a058128

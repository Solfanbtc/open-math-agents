import Mathlib

/-!
# A005867: a(0) = 1; for n > 0, a(n) = (prime(n)-1)*a(n-1).

Source: https://oeis.org/A005867
Credit: @Solfanbtc

`a(n) = Product_{k=1..n} (prime(k) - 1)` (`= phi(primorial(n))`).

The `prime(n+1)`-rough numbers are the positive integers all of whose prime factors are
`≥ prime(n+1)` (equivalently, coprime to the product of the first `n` primes; `1` included):
for `n = 0, 1, 2, …` these are A000027, A005408, A007310, A007775, …. Write `r_n(1) < r_n(2) < …`
for them; their generating function is `G_n(x) = Sum_{j ≥ 1} r_n(j) x^j`.

Conjecture (Benedict W. J. Irwin, Mar 18 2016): `G_n(x) = x P(x) / (1 - x - x^{a(n)} + x^{a(n)+1})`,
where `P` is a polynomial of order `a(n)` with symmetric coefficients
(`c(0) = c(a(n)), c(1) = c(a(n)-1), …`). It is stated with the denominator cleared (the
denominator has constant term `1`, so this is equivalent), with integer coefficients.

Minimal fix: for `n = 0` (A000027, `a(0) = 1`) the identity holds with `P = 1`, a palindrome of
degree `0` but not of order `a(0) = 1` (`c(0) = 1 ≠ 0 = c(1)`), so the claim is stated for
`n ≥ 1`. Checked numerically for `1 ≤ n ≤ 5` (degree exactly `a(n)`, palindromic).
-/

namespace OMA.S_oeis_a005867

open PowerSeries

/-- A005867(n) = Product_{k=1..n} (prime(k) - 1) (`Nat.nth Nat.Prime k` is `prime(k+1)`). -/
noncomputable def a005867 (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (Nat.nth Nat.Prime k - 1)

/-- `m` is `prime(n+1)`-rough: positive, with every prime factor at least `prime(n+1)`. -/
def IsRough (n m : ℕ) : Prop := 0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → Nat.nth Nat.Prime n ≤ p

/-- `G_n(x) = Sum_{j ≥ 1} r_n(j) x^j`, `r_n(j)` the `j`-th `prime(n+1)`-rough number. -/
noncomputable def roughGF (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun j => if j = 0 then 0 else (Nat.nth (IsRough n) (j - 1) : ℤ)

/-- Irwin's conjecture (OEIS A005867), for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ P : Polynomial ℤ,
    P.natDegree = a005867 n ∧
    (∀ i ≤ a005867 n, P.coeff i = P.coeff (a005867 n - i)) ∧
    roughGF n * (1 - X - X ^ a005867 n + X ^ (a005867 n + 1)) = X * (P : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a005867

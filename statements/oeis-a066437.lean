import Mathlib

/-!
# A066437: a(n) = max_{k} {T(n,k)} where T(n,k) is the "phi/sigma tug-of-war sequence with seed n" defined by T(n,1) = phi(n), T(n,2) = sigma(phi(n)), T(n,3) = phi(sigma(phi(n))), ..., T(n,k) = phi(T(n,k-1)) if k is odd and = sigma(T(n,k-1)) if k is even.

Source: https://oeis.org/A066437
Credit: @Solfanbtc

Conjecture (OEIS A066437): a(n) is always finite; i.e. the sequence {T(n,k)} is eventually
periodic for every n (offset 1, so n >= 1).

`main` states the eventual periodicity (which gives the finiteness of the maximum): for every
n >= 1 there are i and p > 0 with T(n, j + p) = T(n, j) for all j >= i. `T n k` follows the
name: T(n, 0) = n (the seed), T(n, k) = phi(T(n, k-1)) for odd k and sigma(T(n, k-1)) for even k,
with phi = `Nat.totient` and sigma = `ArithmeticFunction.sigma 1`. Example (n = 11): 11, 10, 18, 6,
12, 4, 7, 6, 12, ... Checked numerically: for 1 <= n < 3000 the orbit becomes periodic.
-/

namespace OMA.S_oeis_a066437

/-- The phi/sigma tug-of-war sequence with seed `n`. -/
def T (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if Even (k + 1) then ArithmeticFunction.sigma 1 (T n k) else Nat.totient (T n k)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ i p : ℕ, 0 < p ∧ ∀ j ≥ i, T n (j + p) = T n j := by
  sorry

end OMA.S_oeis_a066437

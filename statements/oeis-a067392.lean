import Mathlib

/-!
# A067392: Sum of numbers <= n which have common prime factors with n.

Source: https://oeis.org/A067392
Credit: @Solfanbtc

Conjecture (V. S. Guba, OEIS A067392, comment by Max Alekseyev, May 08 2024): for any positive
n and prime p, a(n) != a(n+p).

Conventions:
* a(n) = Σ k over 1 ≤ k ≤ n with gcd(n, k) > 1 (offset 1; a(1) = 0).
* Checked in Python: `a` reproduces %S; for n + p ≤ 2·10^5 there is no equality a(n) = a(n+p)
  with p prime (there are only 25 values taken more than once in that range, none at two
  indices differing by a prime).
-/

namespace OMA.S_oeis_a067392

/-- A067392: the sum of the `k ≤ n` with `gcd(n, k) > 1`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 1 < Nat.gcd n k), k

/-- Guba's conjecture: `a(n) ≠ a(n + p)` for `n ≥ 1` and `p` prime. -/
theorem main : ∀ n p : ℕ, 1 ≤ n → p.Prime → a n ≠ a (n + p) := by
  sorry

end OMA.S_oeis_a067392

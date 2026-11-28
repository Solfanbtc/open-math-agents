import Mathlib

/-!
# A220181: E.g.f.: Sum_{n>=0} (1 - exp(-n*x))^n.

Source: https://oeis.org/A220181
Credit: @Solfanbtc

Conjecture (OEIS A220181, comment, Peter Bala, Jun 01 2022): let p be prime. The sequence
obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1.

Conventions:
* a(n) is computed by the explicit formula of the entry
  a(n) = Sum_{k=0..n} k^n * Sum_{j=0..k} (-1)^(n+k-j) * binomial(k,j) * (k-j)^n
  (equivalently Sum_{k=0..n} (-1)^(n-k) k^n k! Stirling2(n,k)), with 0^0 = 1. Evaluated with
  `#eval`, it gives 1, 1, 7, 115, 3451, 164731, 11467387, 1096832395 for n = 0..7, matching
  the data.
* "Purely periodic with period p - 1" for n >= 1 is stated as
  a(n + (p - 1)) ≡ a(n) (mod p) for every n >= 1. The minimal period can be a proper divisor
  of p - 1 (for p = 3 the residues are constant), so p - 1 is stated to be a period, not
  the least one. Checked in Python for every prime p <= 59 on the terms n = 1..139.
-/

namespace OMA.S_oeis_a220181

/-- A220181(n) by the explicit double-sum formula of the entry. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ n *
    ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (n + k - j) * (Nat.choose k j : ℤ) * ((k - j : ℕ) : ℤ) ^ n

/-- Conjecture: for every prime `p`, `a(n) mod p` is purely periodic for `n ≥ 1` with
period `p - 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
    a (n + (p - 1)) ≡ a n [ZMOD p] := by
  sorry

end OMA.S_oeis_a220181

import Mathlib

/-!
# A089381: L-th order palindromes with L > 2.

Source: https://oeis.org/A089381
Credit: @Solfanbtc

Conjecture (OEIS A089381): let P(m) = m/2 if m is even and P(m) = m + rev(m) if m is odd, where
rev(m) is the reversal of the decimal representation of m. Any number k eventually cycles when P
is repeatedly applied to it (all numbers below a million do, per the entry).

`main`: for every k, the orbit k, P(k), P(P(k)), ... is eventually periodic: P^(i+p)(k) = P^i(k)
for some i and some p > 0. rev(m) is `Nat.ofDigits 10 (Nat.digits 10 m).reverse` (leading zeros of
the reversal vanish, e.g. rev(10) = 1). Example from the entry, checked: 10917 → 82818 → 41409 →
... → 13748625 → 66433356 (a 7-cycle).
-/

namespace OMA.S_oeis_a089381

/-- Decimal reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- The map P. -/
def P (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else m + rev m

theorem main : ∀ k : ℕ, ∃ i p : ℕ, 0 < p ∧ P^[i + p] k = P^[i] k := by
  sorry

end OMA.S_oeis_a089381

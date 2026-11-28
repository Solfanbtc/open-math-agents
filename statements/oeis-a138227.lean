import Mathlib

/-!
# A138227: Odd positive integers n for which A137576((n-1)/2)-1 is not a multiple of A000010(n).

Source: https://oeis.org/A138227
Credit: @Solfanbtc

A137576(m) = A002326(m) · A006694(m) + 1, where A002326(m) = ord(2, 2m+1) is the multiplicative
order of 2 modulo `2m+1` and A006694(m) is the number of cyclotomic cosets of 2 modulo `2m+1`
minus one. We use the closed form recorded in A137576 (J. Song, Nov 13 2021):
`A137576(m) = ord(2, 2m+1) · ((Σ_{d ∣ 2m+1} φ(d) / ord(2, d)) - 1) + 1`
(each `φ(d) / ord(2, d)` is an exact quotient for odd `d`, and `ord(2, 1) = 1`).
A000010 = Euler's totient `φ`.

A138227 lists the odd positive `n` with `φ(n) ∤ A137576((n-1)/2) - 1`.
Conjecture (V. Shevelev, OEIS A138227): this sequence is infinite.

Checked with python3: the formula reproduces the 64 listed terms of A137576, and the odd
`n ≤ 305` selected by the condition are exactly the 54 listed terms 21, 35, 45, ..., 301, 305.
-/

namespace OMA.S_oeis_a138227

/-- The multiplicative order of 2 modulo `d`. -/
noncomputable def ord2 (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- A137576(m) = ord(2, 2m+1) · (Σ_{d ∣ 2m+1} φ(d)/ord(2,d) - 1) + 1. -/
noncomputable def A137576 (m : ℕ) : ℕ :=
  ord2 (2 * m + 1) * ((∑ d ∈ (2 * m + 1).divisors, Nat.totient d / ord2 d) - 1) + 1

/-- Conjecture: there are infinitely many odd `n` with `φ(n) ∤ A137576((n-1)/2) - 1`. -/
theorem main :
    {n : ℕ | Odd n ∧ ¬ (Nat.totient n ∣ A137576 ((n - 1) / 2) - 1)}.Infinite := by
  sorry

end OMA.S_oeis_a138227

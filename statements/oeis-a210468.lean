import Mathlib

/-!
# A210468: Collatz (3x+1) problem with rational numbers: number of steps to reach the end of the cycle starting with 1/(2n+1).

Source: https://oeis.org/A210468
Credit: @Solfanbtc

Conjectures (OEIS A210468): start with 1/(2n+1); if the numerator is even, divide the number by
2, otherwise multiply it by 3 and add 1. "Do we always reach the end of a cycle with a rational
number? It is conjectured that the answer is yes." More generally, "if x is of the form
x = m/(2n+1) where m is an integer", the trajectory is conjectured to end in a finite cycle.
`main` states the general form (it contains the case m = 1).

Translation. With the odd denominator d = 2n+1 fixed, x = m/d is sent to (m/2)/d when m is even
and to 3x + 1 = (3m + d)/d when m is odd, so the denominator stays d and the trajectory of x is
the trajectory of the numerator m under `step d` (m ↦ m/2 if m is even, 3m + d if m is odd),
divided by d. Reducing m/d by a common (odd) factor does not change the parity of the numerator,
so the convention for the numerator is immaterial. "Reaching the end of a cycle" means that the
trajectory is eventually periodic: some iterate is repeated later. All odd d >= 1 (n >= 0) and
all integers m are included. Example from the entry (d = 7, m = 1): 1, 10, 5, 22, 11, 40, 20, 10.
Checked numerically for odd d < 200 and |m| <= 300: every trajectory becomes periodic.
-/

namespace OMA.S_oeis_a210468

/-- The 3x+1 map on numerators over the odd denominator `d`. -/
def step (d : ℤ) (m : ℤ) : ℤ := if Even m then m / 2 else 3 * m + d

theorem main : ∀ n : ℕ, ∀ m : ℤ,
    ∃ i p : ℕ, 0 < p ∧ (step (2 * n + 1))^[i + p] m = (step (2 * n + 1))^[i] m := by
  sorry

end OMA.S_oeis_a210468

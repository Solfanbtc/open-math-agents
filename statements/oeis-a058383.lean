import Mathlib

/-!
# A058383: Primes of form 1+(2^a)*(3^b), a>0, b>0.

Source: https://oeis.org/A058383
Credit: @Solfanbtc

A058383: primes `1 + 2^a 3^b` with `a > 0` and `b > 0`: 7, 13, 19, 37, 73, 97, 109, ...

Conjecture (Benoit Cloitre, Mar 02 2018): "these are the only solutions >= 7 to the equation
A000010(x) + A000010(x-1) = floor((4*x-3)/3)", A000010 being Euler's totient.
That the terms are solutions is immediate (for `p = 1 + 2^a 3^b`, `φ(p) + φ(p-1) = (p-1) + (p-1)/3`
`= ⌊(4p-3)/3⌋`), so the claim is that for `x ≥ 7` the equation holds iff `x` is a term; we state
this equivalence. `⌊(4x-3)/3⌋` is the natural-number quotient `(4 * x - 3) / 3` (exact subtraction
for `x ≥ 7`).

Sanity check (python): for `7 ≤ x ≤ 3·10^6` the solutions are exactly the 41 terms in that range.
-/

namespace OMA.S_oeis_a058383

/-- `x` is a term of A058383: a prime of the form `1 + 2^a 3^b` with `a, b > 0`. -/
def IsTerm (x : ℕ) : Prop := x.Prime ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = 1 + 2 ^ a * 3 ^ b

/-- Cloitre's conjecture. -/
theorem main : ∀ x : ℕ, 7 ≤ x →
    (Nat.totient x + Nat.totient (x - 1) = (4 * x - 3) / 3 ↔ IsTerm x) := by
  sorry

end OMA.S_oeis_a058383

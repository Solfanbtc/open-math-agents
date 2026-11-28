import Mathlib

/-!
# A097267: Least positive integer that is the diagonal of n primitive Pythagorean quadruples, or zero if no such integer exists.

Source: https://oeis.org/A097267
Credit: @Solfanbtc

A primitive Pythagorean quadruple with diagonal `d` is `(x, y, z, d)` with
`x² + y² + z² = d²`, `0 < x ≤ y ≤ z` and `gcd(x, y, z, d) = 1` (the convention of A097265 and
A097266). Let `Q(d)` be their number. A097267(n) (offset 0) is the least `d ≥ 1` with
`Q(d) = n`, or 0 if there is none.

Conjecture (in the entry): `a(15) = a(38) = 0`, i.e. no positive integer is the diagonal of
exactly 15, or of exactly 38, primitive Pythagorean quadruples.

python3: `Q(2n+1)` reproduces the data of A097266, the first appearances reproduce all 56 listed
terms of A097267 (with `a(15) = a(38) = 0` there), and `Q(d) ∉ {15, 38}` for `1 ≤ d ≤ 1500`.
-/

namespace OMA.S_oeis_a097267

/-- `Q d`: the number of primitive Pythagorean quadruples with diagonal `d`. -/
def Q (d : ℕ) : ℕ :=
  ((Finset.Icc 1 d ×ˢ Finset.Icc 1 d ×ˢ Finset.Icc 1 d).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = d ^ 2 ∧
      Nat.gcd (Nat.gcd t.1 t.2.1) (Nat.gcd t.2.2 d) = 1).card

/-- Conjecture: `a(15) = a(38) = 0`. -/
theorem main : ∀ d : ℕ, 1 ≤ d → Q d ≠ 15 ∧ Q d ≠ 38 := by
  sorry

end OMA.S_oeis_a097267

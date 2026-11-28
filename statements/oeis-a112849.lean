import Mathlib

/-!
# A112849: Number of congruence classes (epimorphisms/vertex partitionings induced by graph endomorphisms) of undirected cycles of even length: |C(C_{2*n})|.

Source: https://oeis.org/A112849
Credit: @Solfanbtc

`a(n) = |C(C_{2n})|` (offset 1): `1, 4, 11, 36, 127, 463, 1717, ...`. The values are taken from the
formula given in the entry (M. A. Michels, diploma thesis, Oldenburg 2005):
`|C(C_{2n})| = 1 + (C(2n-1, n-1) + C(2n-1, n))/2` for `n > 1`, and `a(1) = 1` (as in the entry's
Mathematica, Magma and PARI programs). (The combinatorial definition via graph endomorphisms is
not formalized here; the formula is the entry's own description of the values.)

Conjecture (R. J. Mathar, Aug 07 2015, in the entry):
`n(3n - 5) a(n) + (-15n² + 31n - 12) a(n-1) + 2(3n - 2)(2n - 3) a(n-2) = 0`.

Minimal fix of the range: with `a(1) = 1` the recurrence FAILS at `n = 3`
(`3·4·11 - 54·4 + 2·7·3·1 = 132 - 216 + 42 = -42 ≠ 0`; it would hold with the formula value
`2` at `n = 1`: `132 - 216 + 84 = 0`). It is stated for all `n ≥ 4`, where only the formula values enter; a python3
check confirms it for all `4 ≤ n < 300` and its failure at `n = 3`.

Conventions: the recurrence is stated in `ℤ`; `C(2n-1, n-1) + C(2n-1, n)` is even (the two
binomials are equal), so the division by 2 is exact.
-/

namespace OMA.S_oeis_a112849

/-- `a n = A112849(n)` (`n ≥ 1`). -/
def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 1 else 1 + (((2 * n - 1).choose (n - 1) + (2 * n - 1).choose n) / 2 : ℕ)

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * (3 * n - 5) * a n + (-15 * (n : ℤ) ^ 2 + 31 * n - 12) * a (n - 1)
      + 2 * (3 * (n : ℤ) - 2) * (2 * n - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a112849

import Mathlib

/-!
# A068828: Geometrically weak primes

Source: https://oeis.org/A068828
Credit: @Solfanbtc

A068828: primes that are smaller than the geometric mean of their neighbors,
`prime(k)^2 < prime(k-1) · prime(k+1)` (2 is included by convention): `2, 3, 7, 13, 19, …`.
A051635 (weak primes): `prime(k) < (prime(k-1) + prime(k+1))/2`: `3, 7, 13, 19, …`.

Conjecture (R. J. Mathar, Sep 21 2026, OEIS comment): "For primes from 3 to 99973229 (and
perhaps much beyond), primes in this sequence are the same as the primes in A051635. So one may
conjecture that this is essentially the same as A051635." Stated as: for every prime `p ≥ 3`
(i.e. every `prime(k)` with `k ≥ 2`, which has a preceding prime), `p` is geometrically weak iff
it is weak; "essentially" accounts for the conventional term `2`. (AM–GM gives one direction; the
other is the open part.) With Mathlib's 0-indexed `Nat.nth Nat.Prime`, `p = nth Prime j` with
`j ≥ 1`. The comparison `prime(k)^2 ≤ prime(k-1) prime(k+1)` of the OEIS formula is the same as `<`
(equality is impossible for distinct primes).
-/

namespace OMA.S_oeis_a068828

/-- The `j`-th prime, 0-indexed (`p 0 = 2`). -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime j

/-- Mathar's conjecture: for every prime `≥ 3`, geometrically weak iff weak. -/
theorem main : ∀ j : ℕ, 1 ≤ j →
    (p j ^ 2 < p (j - 1) * p (j + 1) ↔ 2 * p j < p (j - 1) + p (j + 1)) := by
  sorry

end OMA.S_oeis_a068828

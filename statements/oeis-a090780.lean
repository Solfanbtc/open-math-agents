import Mathlib

/-!
# A090780: a(n) = n*Product_{p prime, p|n} (p - 1)/2.

Source: https://oeis.org/A090780
Credit: @Solfanbtc

`a(n) = n * ∏_{p prime, p ∣ n} (p - 1)/2` (computed in `ℚ`; for odd `n` it is a positive
integer). The Genocchi numbers of the first kind (A001469, offset 1) are
`G(k) = 2 (1 - 4^k) B_{2k}`, `k ≥ 1`: `-1, 1, -3, 17, -155, ...`; they are integers, so
`G(k)` is taken as the numerator of that rational number.

The entry's comment (Benoit Cloitre): *`a(2n+1)` is the conjectured value of the length of
period of sequence of Genocchi number of first kind read modulo `(2n + 1)`.*
The sequence `G(k) mod m` is in general only eventually periodic (for `m = 9, 25, 27, 45, 49`
the first terms are not part of the period), so the length of period is the least `p > 0`
with `G(k + p) ≡ G(k) (mod m)` for all sufficiently large `k`. The statement: for every
`n ≥ 0` that least eventual period, for `m = 2n+1`, equals `a(2n+1)`.

Remark (computer check with 700 terms, not part of the source): the conjecture appears to be
false. Modulo 21 the sequence `G(k)` is periodic with period 21 (the least common multiple of
the periods 3 mod 3 and 21 mod 7), whereas `a(21) = 63`; similarly the period modulo 63 is
63 but `a(63) = 189`. It agrees with `a(m)` for every other odd `m ≤ 81` with `3 a(m) ≤ 650`.
The statement is kept faithful; a disproof is welcome.
-/

namespace OMA.S_oeis_a090780

/-- A090780: `a(n) = n * ∏_{p prime, p ∣ n} (p - 1)/2`, as a rational number. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n : ℚ) * ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / 2)

/-- Genocchi numbers of the first kind (A001469): `G(k) = 2 (1 - 4^k) B_{2k}`, an integer. -/
def genocchi (k : ℕ) : ℤ := (2 * (1 - 4 ^ k) * bernoulli (2 * k) : ℚ).num

/-- `p` is an eventual period of `k ↦ G(k) mod m` (indices `k ≥ 1`). -/
def IsEventualPeriod (m p : ℕ) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 1 ≤ k → genocchi (k + p) ≡ genocchi k [ZMOD m]

/-- The conjecture: the length of the (eventual) period of the Genocchi numbers of the first
kind modulo `2n + 1` is `a(2n + 1)`. -/
theorem main :
    ∀ n : ℕ, ∃ p : ℕ, 0 < p ∧ (p : ℚ) = a (2 * n + 1) ∧ IsEventualPeriod (2 * n + 1) p ∧
      ∀ q : ℕ, 0 < q → q < p → ¬ IsEventualPeriod (2 * n + 1) q := by
  sorry

end OMA.S_oeis_a090780

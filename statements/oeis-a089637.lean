import Mathlib

/-!
# A089637: Smallest member of a pair of consecutive twin prime pairs that have exactly n primes between them.

Source: https://oeis.org/A089637
Credit: @Solfanbtc

`a(n)` (offset 0) is the least prime `p` such that `(p, p+2)` is a twin prime pair and exactly `n`
primes lie strictly between `p + 2` and `q`, where `(q, q+2)` is the next twin prime pair. For
example `a(0) = 3` (pairs (3,5), (5,7)), `a(1) = 17` (only 23 lies between (17,19) and (29,31)),
`a(2) = 41`. The sequence is well defined when such a `p` exists for every `n ≥ 0`.

Claim (D. A. Corneth, 2019, in the entry): "If this sequence is well defined then the Twin
Prime Conjecture is true." `main` states this implication: if for every `n` there are
consecutive twin prime pairs with exactly `n` primes between them, then there are infinitely
many twin primes. (The implication is elementary; the hypothesis itself is a strengthening of
the twin prime conjecture and is open.)
-/

namespace OMA.S_oeis_a089637

/-- `p` is the smaller member of a twin prime pair. -/
def IsTwin (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- `(p, p+2)` and `(q, q+2)` are consecutive twin prime pairs. -/
def ConsecutiveTwins (p q : ℕ) : Prop :=
  IsTwin p ∧ IsTwin q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ IsTwin r

/-- The sequence is well defined: every `n` occurs as a number of primes between consecutive
twin prime pairs. -/
def WellDefined : Prop :=
  ∀ n : ℕ, ∃ p q : ℕ, ConsecutiveTwins p q ∧
    ((Finset.Ioo (p + 2) q).filter Nat.Prime).card = n

theorem main : WellDefined → {p : ℕ | IsTwin p}.Infinite := by
  sorry

end OMA.S_oeis_a089637

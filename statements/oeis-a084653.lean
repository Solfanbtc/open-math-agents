import Mathlib

/-!
# A084653: base-2 pseudoprimes whose prime factors divide no smaller pseudoprime

Source: https://oeis.org/A084653 (see A001567, A084654, A084655, A001220)
Credit: @Solfanbtc

A (Fermat base-2) pseudoprime is a composite `n` with `n ∣ 2^(n-1) - 1` (A001567:
341, 561, 645, 1105, ...). A084653 lists the pseudoprimes none of whose prime factors divides any
smaller pseudoprime: 341, 1387, 2047, 8321, 13747, ...

Conjecture (entry): all numbers in this sequence have only two prime factors (tested for all
pseudoprimes `< 10^15`). As the entry notes, the two factors coincide when the term is the square
of a Wieferich prime, so "two prime factors" counts multiplicity: `Ω(n) = 2`, i.e. the prime
factorization of `n` has length 2.

Sanity check (python): the definition reproduces all 21 listed terms, and all 54 terms below
`5·10^6` have exactly two prime factors.
-/

namespace OMA.S_oeis_a084653

/-- `n` is a Fermat base-2 pseudoprime (A001567). -/
def IsPsp (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧ n ∣ 2 ^ (n - 1) - 1

/-- `n` is a term of A084653. -/
def IsTerm (n : ℕ) : Prop :=
  IsPsp n ∧ ∀ p, p.Prime → p ∣ n → ∀ m, m < n → IsPsp m → ¬ p ∣ m

/-- The conjecture: every term has exactly two prime factors (with multiplicity). -/
theorem main : ∀ n : ℕ, IsTerm n → n.primeFactorsList.length = 2 := by
  sorry

end OMA.S_oeis_a084653

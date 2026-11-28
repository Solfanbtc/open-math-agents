import Mathlib

/-!
# A023193: a(n) gives the largest number k for which there is at least one admissible k-tuple taken from [0, 1, ..., n-1] if the tuple starts with 0.

Source: https://oeis.org/A023193
Credit: @Solfanbtc

The source's claim: conjecturally, a(n) is the largest number of primes that occurs on an
infinite number of intervals of n consecutive integers (attributed to Dickson).

Conventions (from W. Lang's comment on the page, after Hensley and Richards):
* A finite set `S` of natural numbers (a tuple `0 ≤ b_1 < ... < b_k`) is admissible if for each
  prime `p` some residue class modulo `p` contains no member of `S`.
* a(n) is the largest `k` such that some admissible `S ⊆ {0, 1, ..., n-1}` with `0 ∈ S` has
  `k` elements. For `n ≥ 1` the set `{0}` qualifies, so the maximum exists (at most `n`).
* The intervals of `n` consecutive integers are `{x, x+1, ..., x+n-1}` for `x ∈ ℕ`; the claim
  is that the largest `m` such that infinitely many of them contain exactly `m` primes is a(n).
  (Taking "at least m primes" instead gives the same largest value.)
* Range `n ≥ 1`, the offset of the sequence.
Checked by computation: the definition gives 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 5, ... (the
data of A023193) for n ≤ 25, and the largest prime count in windows {x, ..., x+n-1} with
1000 ≤ x ≤ 2*10^6 equals a(n) for every n ≤ 15.
-/

namespace OMA.S_oeis_a023193

/-- `S` misses some residue class modulo every prime. -/
def Admissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ s ∈ S, s % p ≠ r

/-- A023193(n): the largest size of an admissible set `S ⊆ {0, ..., n-1}` with `0 ∈ S`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, S.card = k ∧ 0 ∈ S ∧ (∀ s ∈ S, s < n) ∧ Admissible S}

/-- The number of primes among the `n` consecutive integers `x, x+1, ..., x+n-1`. -/
def primesIn (n x : ℕ) : ℕ :=
  ((Finset.Ico x (x + n)).filter Nat.Prime).card

theorem main : ∀ n : ℕ, 1 ≤ n →
    IsGreatest {m : ℕ | {x : ℕ | primesIn n x = m}.Infinite} (a n) := by
  sorry

end OMA.S_oeis_a023193

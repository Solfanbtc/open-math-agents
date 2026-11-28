import Mathlib

/-!
# A054531: T(n,k) = n/gcd(n,k), read as a linear sequence, and Bulgarian solitaire cycles.

Source: https://oeis.org/A054531
Credit: @Solfanbtc

Conjecture (Andrew V. Sutherland, Nov 27 2011, in the entry): read as a linear sequence,
A054531 is the length of the shortest cycle of pebble-moves among the partitions of m
(cf. A201144).

Conventions.
* Pebble moves (A201144, "Bulgarian solitaire"): n pebbles in piles; at each turn take one
  pebble from each pile and put them into a new pile. On a partition, given as a multiset of
  positive parts, the move subtracts 1 from every part, drops the parts that become 0, and
  adds a part equal to the number of parts. It maps partitions of m to partitions of m.
* The shortest cycle length among the partitions of m is the least L ≥ 1 such that some
  partition s of m satisfies move^[L](s) = s (any such L is a multiple of the length of the
  cycle through s, so this least L is the length of the shortest cycle).
* The linear sequence: row n (n ≥ 1) has entries T(n,1), ..., T(n,n), so T(n,k) is term number
  m = n(n-1)/2 + k (1-indexed); every m ≥ 1 arises exactly once this way.
* python3: for m = 1..44 the shortest cycle lengths are 1, 2, 1, 3, 3, 1, 4, 2, 4, 1, 5, ...,
  equal to the linear sequence.
-/

namespace OMA.S_oeis_a054531

/-- s is a partition of m (multiset of positive parts summing to m). -/
def IsPartition (m : ℕ) (s : Multiset ℕ) : Prop := (∀ x ∈ s, 0 < x) ∧ s.sum = m

/-- One pebble move (Bulgarian solitaire). -/
def move (s : Multiset ℕ) : Multiset ℕ :=
  ((s.map (· - 1)).filter (· ≠ 0)) + {Multiset.card s}

/-- Length of the shortest cycle of pebble moves among the partitions of m. -/
noncomputable def shortestCycle (m : ℕ) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ ∃ s : Multiset ℕ, IsPartition m s ∧ move^[L] s = s}

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    shortestCycle (n * (n - 1) / 2 + k) = n / Nat.gcd n k := by
  sorry

end OMA.S_oeis_a054531

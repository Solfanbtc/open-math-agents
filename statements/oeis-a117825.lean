import Mathlib

/-!
# A117825: Distance from n-th highly composite number to nearest prime

Source: https://oeis.org/A117825
Credit: @Solfanbtc

`a(n)` (offset 1) is the distance from the `n`-th highly composite number `h` (A002182: positive
integers with more divisors than every smaller positive integer) to the nearest prime, i.e.
`min_p |h - p|` over primes `p`: `1, 0, 1, 1, 1, 1, 1, 1, 1, 7, …` (a Python computation of the
highly composite numbers below `10^18` reproduces all listed data terms).

Conjecture (Bill McEachen, OEIS comment, point a): entries `> 1` will always be prime. The entry
will be larger than the largest prime factor of the highly composite number. Both sentences are
stated, for every highly composite `h` with distance `> 1` (the second sentence is meant for those
entries; for entries `≤ 1` it can fail, e.g. `h = 2`). Antti Karttunen (Feb 26 2019, OEIS comment)
notes that the second sentence follows from the coprimality of `h` with the neighbouring primes;
the first is open. Points b) to d) of the comment are questions and are not stated ("Will 1 always
be the most common entry?" and c) are not precise; d) fails trivially, there is no prime strictly
between the highly composite numbers 1 and 2). Python: (a) holds for the 156 highly composite
numbers below `10^18`.
-/

namespace OMA.S_oeis_a117825

/-- `n` is highly composite (A002182). -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- Distance from `h` to the nearest prime. -/
noncomputable def distToPrime (h : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ p : ℕ, p.Prime ∧ (p = h + d ∨ h = p + d)}

/-- McEachen's conjecture (a): for a highly composite `h` whose distance `d` to the nearest prime
exceeds `1`, `d` is prime and larger than every prime factor of `h`. -/
theorem main : ∀ h : ℕ, IsHighlyComposite h → 1 < distToPrime h →
    (distToPrime h).Prime ∧ ∀ q : ℕ, q.Prime → q ∣ h → q < distToPrime h := by
  sorry

end OMA.S_oeis_a117825

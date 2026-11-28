import Mathlib

/-!
# A118122: Least prime of level 2n-1 (cf. A117563).

Source: https://oeis.org/A118122
Credit: @Solfanbtc

Conjecture (entry formula section): "Levels of primes are defined in A117563. Conjecture: there
are an infinite number of prime members at each level."

Definitions (A117078, A118534, A117563; offset 1, `p i` = the i-th prime).
* With `g = p (i+1) - p i`, the set `K i` of `k > 0` with `p (i+1) = p i + (p i mod k)`, i.e.
  `p i % k = g`.
* The weight A117078(i) is the least element of `K i` (0 if `K i` is empty), A118534(i) the
  largest one (0 if empty; `K i` is bounded by `p i`).
* The level A117563(i) is A118534(i) / A117078(i), and 0 when A117078(i) = 0 (this happens only
  for the primes 2, 3, 7).
With these definitions python3 reproduces the 85 data terms of A117563.
* "each level": the levels that occur are the odd numbers (A118122 lists the least prime of
  level 2n-1 for every n, and the data show all of 1, 3, 5, ..., 99), so the statement is: for
  every n ≥ 1, infinitely many primes have level 2n - 1. (python3, primes below 6*10^6: the
  least prime of level 2n - 1 reproduces all 50 data terms, up to 5378731, and no prime has an
  even level other than 0.)
-/

namespace OMA.S_oeis_a118122

/-- The i-th prime, offset 1. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- The `k > 0` with `p (i+1) = p i + (p i mod k)`. -/
def K (i : ℕ) : Set ℕ := {k : ℕ | 0 < k ∧ p i % k = p (i + 1) - p i}

/-- A117078(i): the weight. -/
noncomputable def weight (i : ℕ) : ℕ := sInf (K i)

/-- A118534(i). -/
noncomputable def big (i : ℕ) : ℕ := sSup (K i)

/-- A117563(i): the level of the i-th prime. -/
noncomputable def level (i : ℕ) : ℕ := if weight i = 0 then 0 else big i / weight i

theorem main : ∀ n : ℕ, 1 ≤ n → {i : ℕ | 1 ≤ i ∧ level i = 2 * n - 1}.Infinite := by
  sorry

end OMA.S_oeis_a118122

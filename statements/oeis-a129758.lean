import Mathlib

/-!
# A129758: Smallest prime p such that there are primes q and r with the property that p, q and r form an arithmetic progression and their sum is the same as three times the n-th prime number.

Source: https://oeis.org/A129758
Credit: @Solfanbtc

Conjecture (Alain Rocchelli, May 01 2024):
  Limit_{N->oo} (Sum_{n=1..N} a(n)) / (Sum_{n=1..N} prime(n+2)) = 1.

Definitions.
* Offset 3 (since Jul 2026): a(n) is the greatest prime p < prime(n) such that
  2 prime(n) - p is prime (Andrew Howroyd's description and PARI program; the triple is
  p, prime(n), 2 prime(n) - p with the smallest common difference). `sSup` of that finite set
  (0 if it were empty). This reproduces the 58 data terms (python3).
* Index alignment. The conjecture was written in 2024, when the offset was 1, so its a(n) is the
  current a(n+2): the conjecture pairs each term with the prime it is built from. With the
  current offset it reads
  (Sum_{n=3..N} a(n)) / (Sum_{n=3..N} prime(n)) → 1 as N → ∞,
  which is what we state. (Shifting the index by a constant does not change the limit.)
python3: the ratio is 0.99885 at N = 15000.
-/

namespace OMA.S_oeis_a129758

/-- The n-th prime, offset 1. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A129758(n), n ≥ 3. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p < prime n ∧ (2 * prime n - p).Prime}

theorem main :
    Filter.Tendsto
      (fun N : ℕ => ((∑ n ∈ Finset.Icc 3 N, a n : ℕ) : ℝ) / (∑ n ∈ Finset.Icc 3 N, prime n : ℕ))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a129758

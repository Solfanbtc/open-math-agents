import Mathlib

/-!
# A049094: Jovovic's conjecture "2^n - 1 is squarefree iff gcd(n, 2^n - 1) = 1" (refuted)

Source: https://oeis.org/A049094
Credit: @Solfanbtc

A049094: the numbers `m` such that `2^m - 1` is divisible by a square `> 1`.

Conjecture (V. Jovovic, Apr 12 2002, in the entry): "2^n-1 is squarefree iff gcd(n,2^n-1)=1."

Status: false, as the entry itself records (V. Jovovic, Nov 01 2005): "counterexamples are
n = 364 and n = 1755, i.e., gcd(364,2^364-1) = 1 and (2^364-1) mod 1093^2 = 0 and
gcd(1755,2^1755-1) = 1 and (2^1755-1) mod 3511^2 = 0", where 1093 and 3511 are the Wieferich
primes (A001220). (Both facts re-checked with python3.) The entry adds that the equivalence
holds for `n` not a multiple of the order of 2 modulo any Wieferich prime.

`main` states the conjecture exactly as posed, for every `n ≥ 1`, so that its refutation is a
target (`OMA.disproof`, e.g. at `n = 364`).
-/

namespace OMA.S_oeis_a049094

/-- Jovovic's (refuted) conjecture: `2^n - 1` is squarefree iff `gcd(n, 2^n - 1) = 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (Squarefree (2 ^ n - 1) ↔ Nat.gcd n (2 ^ n - 1) = 1) := by
  sorry

end OMA.S_oeis_a049094

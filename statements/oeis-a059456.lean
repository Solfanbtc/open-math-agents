import Mathlib

/-!
# A059456: Unsafe primes: primes not in A005385.

Source: https://oeis.org/A059456
Credit: @Solfanbtc

Conjecture (Vincenzo Librandi, OEIS A059456, comment, Aug 07 2010): from the sequence of prime
numbers, keep 2 and remove the primes of its iteration p -> 2p+1 (5, 11, 23, 47); keep 3 and
remove the primes of its iteration (7); and so on; the primes that remain are exactly the
unsafe primes (2, 3, 13, 17, 19, 29, ...). The entry's example also applies the iteration to
p = 23 (which removes 47), so every prime is iterated.
Status: the entry calls it a conjecture, but it follows directly from the definitions: a
removed prime has the form 2r + 1 with r prime, and every safe prime 2r + 1 is removed by the
iteration of r. It is stated here as recorded in the entry.

Conventions:
* The iteration of p is the Cunningham chain 2p+1, 2(2p+1)+1, ..., i.e. the numbers
  2^k (p+1) - 1, k ≥ 1, as long as they are prime: q is removed by p if q = 2^k (p+1) - 1 for
  some k ≥ 1 and 2^j (p+1) - 1 is prime for every 1 ≤ j ≤ k.
* A prime q is safe (A005385) if (q-1)/2 is prime, i.e. q = 2r + 1 with r prime; unsafe primes
  are the other primes.
* Checked in Python for primes below 5000: the primes left by the sieve are exactly the unsafe
  primes, and they reproduce %S, %T, %U.
-/

namespace OMA.S_oeis_a059456

/-- `q` is removed by the iteration `x ↦ 2x+1` started at the prime `p`. -/
def RemovedBy (p q : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ q = 2 ^ k * (p + 1) - 1 ∧ ∀ j ∈ Finset.Icc 1 k, (2 ^ j * (p + 1) - 1).Prime

/-- `q` is a safe prime (A005385). -/
def IsSafePrime (q : ℕ) : Prop := ∃ r, r.Prime ∧ q = 2 * r + 1

/-- Librandi's sieve leaves exactly the unsafe primes. -/
theorem main :
    ∀ q : ℕ, (q.Prime ∧ ¬ ∃ p, p.Prime ∧ RemovedBy p q) ↔ (q.Prime ∧ ¬ IsSafePrime q) := by
  sorry

end OMA.S_oeis_a059456

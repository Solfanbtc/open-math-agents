import Mathlib

/-!
# A108137: primes p such that p + 6^k is composite for all k ≥ 0

Source: https://oeis.org/A108137
The entry lists the primes `p` such that `p + 6^k` is composite for every `k ≥ 0`:
3, 19, 29, 59, 79, 89, 109, 139, 149, 179, 199, 229, 239, 269, 349, 359, 379, 389, 409, 419, 439,
449, 479, 499, 509, 569, 599, 619, 659, 709, 719, 739, 769, 809, 829, 839, 859, 919, 929.
N. J. A. Sloane (Jun 30 2005): "The PARI code given suggests that these values are merely
conjectures" (the program only tests `k ≤ m` with pseudoprime tests).

We state that the listed values are correct and complete up to the last listed term: a prime
`p ≤ 929` has `p + 6^k` composite for all `k ≥ 0` iff `p` is one of the 39 listed primes.
("Composite" is read as "not prime": `p + 6^k ≥ 3` is never 0 or 1.)

Status note. This is settled by a finite computation and is expected to be true: 3 and every
listed `p ≡ 9 (mod 10)` are terms because `3 ∣ 3 + 6^k` for `k ≥ 1` (and `3 + 1 = 4`), and
`5 ∣ p + 6^k` for all `k` when `p ≡ 4 (mod 5)`. Every other prime `p ≤ 929` has a prime
`p + 6^k` with `k ≤ 10` (python3, Miller-Rabin; e.g. `547 + 6^10`), and these witnesses are
small enough to certify. The statement is the source's claim, stated faithfully.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a108137

/-- `p` is a term of A108137. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∀ k : ℕ, ¬ (p + 6 ^ k).Prime

/-- The listed terms. -/
def listed : Finset ℕ :=
  {3, 19, 29, 59, 79, 89, 109, 139, 149, 179, 199, 229, 239, 269, 349, 359, 379, 389, 409, 419,
    439, 449, 479, 499, 509, 569, 599, 619, 659, 709, 719, 739, 769, 809, 829, 839, 859, 919, 929}

theorem main : ∀ p : ℕ, p ≤ 929 → (IsTerm p ↔ p ∈ listed) := by
  sorry

end OMA.S_oeis_a108137

import Mathlib

/-!
# A143027: Sturdy prime numbers: p such that in binary notation k*p has at least as many 1-bits as p for all k > 0.

Source: https://oeis.org/A143027
Credit: @Solfanbtc

A prime `p` is sturdy if for every `k > 0` the binary expansion of `k * p` has at least as many
1-bits as that of `p`. Data: `2, 3, 5, 7, 17, 31, 73, 89, 127, 257, 1801, 2089, 8191, 65537,
131071, 178481, 262657, 524287, 2099863, 616318177, 2147483647, 4432676798593`.

Conjecture (Max Alekseyev, reported by T. D. Noe, Mar 01 2010, in the entry): 616318177 is the
next term after 2099863, i.e. 616318177 is a sturdy prime and no prime strictly between 2099863
and 616318177 is sturdy. (Alekseyev showed that the earlier candidates 6700417, 13264529,
20394401, 97685839 are not sturdy.)

Status: SOLVED. The entry says (Jeffrey Shallit, Feb 10 2020) that Clokie et al. verified that the
next two sturdy primes after 2099863 are 616318177 and 2147483647 (T. Clokie, T. F. Lidbetter,
A. J. Molina Lovett, J. Shallit, L. Zamboni, "Computational Aspects of Sturdy and Flimsy
Numbers", 2020). The conjecture is stated here as Alekseyev formulated it.

Conventions:
* The number of 1-bits of `n` is `(Nat.digits 2 n).sum` (A000120).
-/

namespace OMA.S_oeis_a143027

/-- Number of 1-bits in the binary expansion of `n` (A000120). -/
def bitCount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- `p` is a sturdy prime: every positive multiple of `p` has at least as many 1-bits as `p`. -/
def IsSturdyPrime (p : ℕ) : Prop := p.Prime ∧ ∀ k : ℕ, 0 < k → bitCount p ≤ bitCount (k * p)

/-- Alekseyev's conjecture: 616318177 is the next sturdy prime after 2099863. -/
theorem main : IsSturdyPrime 616318177 ∧
    ∀ p : ℕ, 2099863 < p → p < 616318177 → ¬ IsSturdyPrime p := by
  sorry

end OMA.S_oeis_a143027

import Mathlib

/-!
# A092559: Numbers k such that 2^k + 1 is a semiprime.

Source: https://oeis.org/A092559
Credit: @Solfanbtc

`k` is a term iff `2^k + 1` is a semiprime (has exactly two prime factors counted with
multiplicity, `Ω = 2`; e.g. `2^3 + 1 = 3^2`, `2^11 + 1 = 3 · 683`).

The entry contains no open conjecture; its precise mathematical claims are those of
Giuseppe Coppoletta (May 09 2017), which are stated here (they are known/provable results):
1. Since `3 ∣ 2^k + 1` for odd `k`, all odd terms are prime, and
2. the odd terms are exactly the Wagstaff numbers A000978, i.e. the `k` with `(2^k + 1)/3`
   prime (equivalently the prime-Jacobsthal indices A107036, since the Jacobsthal number
   `J(k) = (2^k + 1)/3` for odd `k`);
3. excluding `k = 3`, the sequence coincides with A073936 (`2^k + 1` is a product of two
   distinct primes), because `2^k + 1 = p^2` forces `p = k = 3` by Mihăilescu's theorem
   (Catalan's conjecture).
The remaining comments (which large values are terms, based on probable-prime tests) are
computational data, not stated here.
Checked with `#eval`: for `k < 45` the terms are 3, 5, 6, 7, 11, 12, 13, 17, 19, 20, 23, 28,
31, 32, 40, 43 (as in %S), and the odd `k < 45` with `(2^k+1)/3` prime are exactly the odd ones.
-/

namespace OMA.S_oeis_a092559

/-- `n` is a semiprime: exactly two prime factors counted with multiplicity. -/
def IsSemiprime (n : ℕ) : Prop := n.primeFactorsList.length = 2

/-- `k ∈ A092559`. -/
def InSeq (k : ℕ) : Prop := IsSemiprime (2 ^ k + 1)

/-- Coppoletta's claims about A092559. -/
theorem main :
    (∀ k : ℕ, Odd k → InSeq k → k.Prime) ∧
    (∀ k : ℕ, Odd k → (InSeq k ↔ ((2 ^ k + 1) / 3).Prime)) ∧
    (∀ k : ℕ, k ≠ 3 →
      (InSeq k ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 2 ^ k + 1 = p * q)) := by
  sorry

end OMA.S_oeis_a092559

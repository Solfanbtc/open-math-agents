import Mathlib

/-!
# A027854: Mutinous numbers: n > 1 such that n/p^k > p, where p is the largest prime dividing n and p^k is the highest power of p dividing n.

Source: https://oeis.org/A027854
Credit: @Solfanbtc

`n > 1` is mutinous if `n / p^k > p`, where `p` is the largest prime factor of `n` and `p^k` the
highest power of `p` dividing `n`: `12, 24, 30, 36, 40, 45, 48, 56, 60, 63, ...`.

Conjecture (in the entry): if `m` is in the sequence then so is `A003961(m)`, where A003961 is
the prime shift: `A003961(∏ pᵢ^{eᵢ}) = ∏ q(pᵢ)^{eᵢ}` with `q(p)` the prime following `p`.

A python3 check: the definition reproduces the data, and the conjecture holds for all mutinous
`m < 10⁶`.

Conventions:
* The prime following `p` is `Nat.nth Nat.Prime (π(p))` (for prime `p = Nat.nth Nat.Prime i`,
  `π(p) = i + 1`).
* The largest prime factor is `n.primeFactors.sup id`; `p^k` is `p ^ n.factorization p`.
-/

namespace OMA.S_oeis_a027854

/-- `n` is mutinous. -/
def IsMutinous (n : ℕ) : Prop :=
  1 < n ∧ n.primeFactors.sup id < n / (n.primeFactors.sup id) ^ (n.factorization (n.primeFactors.sup id))

/-- The prime following the prime `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.nth Nat.Prime (Nat.primeCounting p)

/-- A003961: the prime shift, replacing each prime factor by the next prime. -/
noncomputable def primeShift (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, nextPrime p ^ (n.factorization p)

/-- Conjecture: the mutinous numbers are closed under the prime shift A003961. -/
theorem main : ∀ m : ℕ, IsMutinous m → IsMutinous (primeShift m) := by
  sorry

end OMA.S_oeis_a027854

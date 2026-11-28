import Mathlib

/-!
# A090496: Ratio of numerator(Bernoulli(2*n)/(2*n)) to numerator(Bernoulli(2*n)/(2*n*(2*n-1))) for n's for which they are different.

Source: https://oeis.org/A090496 (and https://oeis.org/A092291)
Credit: @Solfanbtc

For `n ≥ 1` let `q(n) = numerator(B(2n)/(2n)) / numerator(B(2n)/(2n(2n-1)))` (a positive integer,
taken here in `ℚ`; `B` = Mathlib's `bernoulli`, which agrees with the usual Bernoulli numbers at
even indices). The sequence lists the values `q(n) > 1`; the first is `q(574) = 37`
(checked numerically, consistent with A092291).

Conjecture (Roland Bacher, Feb 04 2004, in the entry): all indices `n` yielding a given prime `p`
(i.e. with `q(n) = p`) form an arithmetic progression `n0 + d k`, `k = 0, 1, 2, …`, of step
`d = p (p - 1) / 2` (e.g. `574 + 666 k` for `p = 37`). We state it for every prime `p` that is
yielded by at least one index (for the other primes the set of indices is empty and the claim is
vacuous).

**Status.** The entry itself records that this is false as stated: T. D. Noe (Feb 12 2004) found
`2n = 272876` (`n = 136438 = 574 + 666 · 204`) with quotient `37 · 59`, and notes that
"composite quotients imply there are missing terms in the arithmetic progression conjectured by
Bacher". See also B. C. Kellner, arXiv:math/0410297. The statement is recorded faithfully; its
expected resolution is a disproof.
-/

namespace OMA.S_oeis_a090496

/-- `q(n) = numerator(B(2n)/(2n)) / numerator(B(2n)/(2n(2n-1)))`, as a rational number. -/
def quot (n : ℕ) : ℚ :=
  ((bernoulli (2 * n) / (2 * n : ℚ)).num : ℚ) /
    ((bernoulli (2 * n) / ((2 * n : ℚ) * (2 * n - 1))).num : ℚ)

/-- The indices `n ≥ 1` yielding the quotient `p`. -/
def indices (p : ℕ) : Set ℕ := {n | 1 ≤ n ∧ quot n = p}

/-- Bacher's conjecture (OEIS A090496): for every prime `p` yielded by some index, the indices
yielding `p` are exactly an arithmetic progression `n0 + (p(p-1)/2) k`, `k ≥ 0`. -/
theorem main : ∀ p : ℕ, p.Prime → (indices p).Nonempty →
    ∃ n0 : ℕ, indices p = {n | ∃ k : ℕ, n = n0 + p * (p - 1) / 2 * k} := by
  sorry

end OMA.S_oeis_a090496

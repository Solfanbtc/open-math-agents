import Mathlib

/-!
# A120934: Least prime p such that the interval [p,p+log(p)] contains n primes.

Source: https://oeis.org/A120934
Credit: @Solfanbtc

`a(n)` is the least prime `p` such that the interval `[p, p + log p]` (natural logarithm) contains
(at least) `n` primes: `2, 11, 457, 3251, 165701, ...`. ("At least": the entry's Mathematica
program searches for the first `p` with count `≥ n`; a python3 check with this reading
reproduces `a(1), ..., a(5)`.)

Question and claim (T. D. Noe, in the entry): is there an upper limit to the number of primes in
such an interval? Not if the prime k-tuple conjecture is true, in which case `a(n)` exists for all
`n`. Stated here is the conclusion: `a(n)` exists for every `n`, i.e. for every `n` some prime `p`
has at least `n` primes in `[p, p + log p]` (so there is no upper limit).

Status: the entry derives this from the prime k-tuple conjecture. It also follows unconditionally
from Maynard's theorem (J. Maynard, "Small gaps between primes", Ann. of Math. 181 (2015),
383-413; also T. Tao): for every `m`, `liminf (p_{k+m} - p_k) < ∞`, and `log p` exceeds any fixed
bound for `p` large. This is not mentioned in the entry.

Conventions:
* `p + log p` is computed in `ℝ`; the primes counted are the `q` with `p ≤ q` and `q ≤ p + log p`
  (all such `q` lie in `[p, 2p]`, since `log p < p`).
-/

namespace OMA.S_oeis_a120934

/-- The number of primes in the interval `[p, p + log p]`. -/
noncomputable def primesInInterval (p : ℕ) : ℕ :=
  ((Finset.Icc p (2 * p)).filter (fun q : ℕ => q.Prime ∧ (q : ℝ) ≤ (p : ℝ) + Real.log (p : ℝ))).card

/-- `a(n)` exists for every `n`: some prime `p` has at least `n` primes in `[p, p + log p]`. -/
theorem main : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n ≤ primesInInterval p := by
  sorry

end OMA.S_oeis_a120934

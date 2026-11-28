import Mathlib

/-!
# A023199: a(n) is the least k with sigma(k) >= n*k.

Source: https://oeis.org/A023199
Credit: @Solfanbtc

Conjecture (Santi Spadaro, OEIS A023199, comment, Aug 13 2002: "Initially, each term is
divisible by the previous one. Is there a reason this should always be true?"; called "the
conjecture a(n)|a(n+1)" by Devin Kilminster, Mar 10 2003, who checked it out to n = 10):
a(n) divides a(n+1) for every n ≥ 1.
Status: the entry records that the conjecture fails for n = 15 (T. D. Noe, Jul 08 2005,
reconfirmed Oct 13 2009 after a correction of a(15)), i.e. a(15) does not divide a(16). The
conjecture is stated here as posed; it is expected to be refutable.

Conventions:
* a(n) is the least positive integer k with sigma(k) ≥ n k (offset 1; a(1) = 1, a(2) = 6,
  a(3) = 120). k ranges over positive integers (k = 0 would trivially satisfy 0 ≥ 0). Such k
  exists for every n since sigma(k)/k is unbounded, so the `sInf` is attained.
-/

namespace OMA.S_oeis_a023199

/-- A023199: the least `k ≥ 1` with `σ(k) ≥ n k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ n * k ≤ ArithmeticFunction.sigma 1 k}

/-- Spadaro's conjecture (refuted at `n = 15` per the entry): `a(n) ∣ a(n+1)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ∣ a (n + 1) := by
  sorry

end OMA.S_oeis_a023199

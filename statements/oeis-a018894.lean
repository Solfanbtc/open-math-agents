import Mathlib

/-!
# A018894: Numbers k such that sigma(k)/phi(k) sets a new record.

Source: https://oeis.org/A018894
Credit: @Solfanbtc

Conjecture of David A. Corneth (Sep 10 2020, in the entry): "For all terms t > 1 there exists
a p | t such that t/p is a term" (verified by Corneth for the 240 terms 1 < t ≤ 10^40). In context
p is a prime divisor (Corneth's search multiplies terms by primes); we state it with p prime.
(Checked with python3 for all terms ≤ 2·10^5.)

Not stated: Corneth's other conjecture, "these 466 terms are the terms <= 10^75". The 466 terms
are only in a file attached to the entry, not in the entry itself, and the claim is about that
specific list; stating only the count (466 terms ≤ 10^75) would be weaker than the source, so
this file states the second conjecture alone.

Conventions.
* k ≥ 1 is a term iff σ(k)/φ(k) > σ(j)/φ(j) for every 1 ≤ j < k (strict record, the usual
  OEIS convention; this reproduces the data 1, 2, 4, 6, 12, 24, 30, 60, 120, 180, 210, ...;
  note 3 is not a term since σ(3)/φ(3) = 2 < 3 = σ(2)/φ(2)). Ratios are compared in ℚ.
-/

namespace OMA.S_oeis_a018894

/-- σ(k)/φ(k) as a rational number. -/
def ratio (k : ℕ) : ℚ := (ArithmeticFunction.sigma 1 k : ℚ) / (Nat.totient k : ℚ)

/-- k is a term of A018894: σ(k)/φ(k) sets a new record. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ ∀ j : ℕ, 1 ≤ j → j < k → ratio j < ratio k

theorem main :
    ∀ t : ℕ, IsTerm t → 1 < t → ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ IsTerm (t / p) := by
  sorry

end OMA.S_oeis_a018894

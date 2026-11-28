import Mathlib

/-!
# A092291: Let p = n-th irregular prime, A000928(n). Then a(n) = smallest value of m such that numerator(Bernoulli(2*m)/(2*m)) / numerator(Bernoulli(2*m)/(2*m*(2*m-1))) equals p.

Source: https://oeis.org/A092291
Credit: @Solfanbtc

Claim (OEIS A092291, comment by T. D. Noe, Feb 10 2004): it was conjectured that
a(n) = (1 + A000928(n) * (A035112(n) - 1))/2.

STATUS: the entry itself says this conjecture is FALSE: B. Kellner's paper shows that the
formula first fails for the irregular prime 6449. The statement below is the original
conjecture, stated faithfully, so the expected resolution is a disproof (`¬ main`'s type).

Conventions:
* `bernoulli` is Mathlib's Bernoulli numbers (only even indices `2 * m`, `m ≥ 1`, occur, so
  the sign convention for B_1 plays no role); `Rat.num` is the numerator.
* p is irregular (A000928) iff p is an odd prime dividing the numerator of some B_{2k} with
  2 <= 2k <= p - 3; A035112(n) is the least such even index 2a (B_0 = 1 is never divisible
  by p, so the range 0 <= 2a in A035112 is the same). The statement quantifies over each
  irregular prime p together with this least index 2a, which is the same as quantifying
  over n.
* a(n) is the least m >= 1 such that the ratio of the two numerators equals p, so the claim
  is that `(1 + p * (2a - 1)) / 2` is the least element of that set (p and 2a - 1 are odd,
  so the division by 2 is exact).
* Checked in Python: the formula gives 574, 1269, 1910, 3384 for p = 37, 59, 67, 101 (the
  first data terms), and m = 574 is indeed the least m with ratio 37.
-/

namespace OMA.S_oeis_a092291

/-- The ratio numerator(B_{2m}/(2m)) / numerator(B_{2m}/(2m(2m-1))) as a rational number. -/
def ratio (m : ℕ) : ℚ :=
  ((bernoulli (2 * m) / (2 * m)).num : ℚ) /
    ((bernoulli (2 * m) / (2 * m * (2 * m - 1))).num : ℚ)

/-- The (refuted) conjecture: for every irregular prime `p`, with `2 * a` the least even
index in `[2, p - 3]` such that `p` divides the numerator of `B_{2a}`, the least `m ≥ 1`
whose ratio equals `p` is `(1 + p * (2 * a - 1)) / 2`. -/
theorem main : ∀ p a : ℕ, p.Prime → p ≠ 2 → 1 ≤ a → 2 * a ≤ p - 3 →
    (p : ℤ) ∣ (bernoulli (2 * a)).num →
    (∀ b : ℕ, 1 ≤ b → b < a → ¬ (p : ℤ) ∣ (bernoulli (2 * b)).num) →
    IsLeast {m : ℕ | 1 ≤ m ∧ ratio m = p} ((1 + p * (2 * a - 1)) / 2) := by
  sorry

end OMA.S_oeis_a092291

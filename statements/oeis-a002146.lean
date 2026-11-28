import Mathlib

/-!
# A002146: Smallest prime == 7 (mod 8) where Q(sqrt(-p)) has class number 2n+1.

Source: https://oeis.org/A002146
Credit: @Solfanbtc

Conjecture (Jianing Song, Jul 20 2022, OEIS A002146): a(n) < A002148(n) for all n >= 1,
where A002148(n) is the smallest prime p == 3 (mod 8) such that Q(sqrt(-p)) has class
number 2n+1. Both sequences have offset 0 (a(0) = 7, A002148(0) = 3, class number 1), which
is why the conjecture starts at n = 1 (at n = 0 it fails, 7 > 3).

Translation: Q(sqrt(-p)) is `AdjoinRoot (X ^ 2 + C p)` over ℚ, as in upstream
`OeisA38552.HasClassNumber`. Saying that the smallest prime q == 3 (mod 8) with class number
2n+1 is larger than the smallest prime p == 7 (mod 8) with class number 2n+1 is the same as:
every prime q == 3 (mod 8) with class number 2n+1 has a prime p == 7 (mod 8) below it with class
number 2n+1. When A002148(n) exists this is exactly a(n) < A002148(n) (and it implies that
a(n) exists); the source does not claim the existence of the terms, only the comparison.
-/

namespace OMA.S_oeis_a002146

open Polynomial

/-- The class number of the imaginary quadratic field Q(sqrt(-k)) equals h. -/
def HasClassNumber (k h : ℕ) : Prop :=
  ∃ (hirr : Irreducible (X ^ 2 + C (k : ℚ))),
    haveI := Fact.mk hirr
    NumberField.classNumber (AdjoinRoot (X ^ 2 + C (k : ℚ))) = h

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∀ q : ℕ, q.Prime → q % 8 = 3 → HasClassNumber q (2 * n + 1) →
      ∃ p : ℕ, p.Prime ∧ p % 8 = 7 ∧ HasClassNumber p (2 * n + 1) ∧ p < q := by
  sorry

end OMA.S_oeis_a002146

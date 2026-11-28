import Mathlib

/-!
# A060651: Smallest odd prime p such that Q(sqrt(-p)) has class number 2n+1.

Source: https://oeis.org/A060651
Credit: @Solfanbtc

A060651(n) is the smallest odd prime `p` such that `ℚ(√-p)` has class number `2n+1`;
A002146(n) (resp. A002148(n)) is the smallest prime `p ≡ 7 (mod 8)` (resp. `p ≡ 3 (mod 8)`)
with that property. Such primes are `≡ 3 (mod 4)`, so `a(n) = min(A002146(n), A002148(n))`.

Conjecture (Jianing Song, 2022): `a(n) = A002146(n)` for all `n ≥ 1`, i.e.
`A002148(n) > A002146(n)` for all `n ≥ 1`. (For `n = 0` it fails: `A002146(0) = 7`,
`A002148(0) = 3`.) Stated as: for `n ≥ 1`, every prime `q ≡ 3 (mod 8)` with `h(-q) = 2n+1` is
preceded by a prime `p ≡ 7 (mod 8)`, `p < q`, with `h(-p) = 2n+1`. When A002148(n) exists this
is exactly `A002146(n) < A002148(n)`. `HasClassNumber` follows the upstream convention of
`FormalConjectures/OEIS/38552.lean`, with `ℚ(√-k)` as `AdjoinRoot (X^2 + k)`.
Checked with python3 (class numbers by counting reduced forms of discriminant `-p`, `p < 60000`):
the first terms of A002146 and A002148 are reproduced and there is no counterexample for
`2n+1 ≤ 119`.
-/

namespace OMA.S_oeis_a060651

open Polynomial

/-- The class number of the imaginary quadratic field `ℚ(√-k)` equals `n`. -/
def HasClassNumber (k n : ℕ) : Prop :=
  ∃ (h : Irreducible (X ^ 2 + C (k : ℚ))),
  haveI := Fact.mk h
  NumberField.classNumber (AdjoinRoot (X ^ 2 + C (k : ℚ))) = n

/-- The conjecture: for `n ≥ 1`, A002146(n) < A002148(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ q : ℕ, q.Prime → q % 8 = 3 → HasClassNumber q (2 * n + 1) →
    ∃ p : ℕ, p.Prime ∧ p % 8 = 7 ∧ p < q ∧ HasClassNumber p (2 * n + 1) := by
  sorry

end OMA.S_oeis_a060651

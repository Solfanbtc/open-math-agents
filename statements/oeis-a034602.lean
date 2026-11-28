import Mathlib

/-!
# A034602: Wolstenholme quotient W_p = (binomial(2p-1,p) - 1)/p^3 for prime p=A000040(n).

Source: https://oeis.org/A034602
Credit: @Solfanbtc

`A034602(n) = (C(2p - 1, p) - 1)/p³ = (C(2p, p) - 2)/(2p³)` for `p = prime(n)`, `n ≥ 3`.

Claim (Alexander R. Povolotsky, Apr 18 2013, in the entry): the terms are replicated by the
conjectured general formula of A223886, `(C(jkp, jp) - C(kj, j)) / (k p³)` with `p = prime(n)`,
for `k = 2`, `j = 1` and `n ≥ 3`. The conjecture behind it (Gary Detlefs, as restated by
Povolotsky in A223886): for any fixed integers `k > 0` and `j > 0`, there is `N` such that for all
`n > N`, `(C(jkp, jp) - C(kj, j)) / (k p³)` is an integer, `p = prime(n)`. (For `k = 2`, `j = 1`
this is Wolstenholme's theorem, giving exactly A034602.) Stated here is that general conjecture:
for all `j, k ≥ 1`, eventually in `n`, `k · prime(n)³ ∣ C(jk · prime(n), j · prime(n)) - C(kj, j)`.

Remarks: Detlefs' own wording uses an arbitrary integer `n` in place of `prime(n)`; the prime
version is the one written in A223886 and used for A034602. The divisibility by `p³` alone is
Jacobsthal's classical congruence `C(ap, bp) ≡ C(a, b) (mod p³)` for primes `p ≥ 5`; the extra
factor `k` is the part specific to this formula. A python3 check: for `1 ≤ k ≤ 8`, `1 ≤ j ≤ 6`
and primes `p < 400`, the divisibility fails only for `p ∈ {2, 3}`.

Conventions: `prime(n) = Nat.nth Nat.Prime (n - 1)` (1-indexed); the divisibility is in `ℤ`.
-/

namespace OMA.S_oeis_a034602

open Filter

/-- The `n`-th prime, 1-indexed. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Detlefs–Povolotsky conjecture: for all `j, k ≥ 1`, for all large `n`,
`(C(jkp, jp) - C(kj, j)) / (k p³)` is an integer, `p = prime(n)`. -/
theorem main : ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
    ∀ᶠ n in atTop, ((k : ℤ) * (prime n : ℤ) ^ 3) ∣
      (((j * k * prime n).choose (j * prime n) : ℕ) : ℤ) - ((k * j).choose j : ℕ) := by
  sorry

end OMA.S_oeis_a034602

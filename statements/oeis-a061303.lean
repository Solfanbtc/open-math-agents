import Mathlib

/-!
# A061303: Smarandache prime generator sequence.

Source: https://oeis.org/A061303
Credit: @Solfanbtc

Given a prime `p`, let `s(p, 0) = p` and let `s(p, n+1)` be the smallest prime `≡ 1 (mod s(p, n))`.
Let `S(p) = {s(p, n) : n = 0, 1, ...}`. (E.g. `S(2) = {2, 3, 7, 29, ...}` (A061092),
`S(5) = {5, 11, 23, 47, ...}`, `S(13) = {13, 53, 107, 643, ...}`.) The sequence A061303 lists
`a(0) = 2` and then the smallest primes not in `S(a(0)), ..., S(a(n))`.

Conjecture (in the entry): for primes `p` and `q`, the sets `S(p)` and `S(q)` are disjoint,
unless one is contained in the other.

A python3 check: the map `x ↦` (smallest prime `≡ 1 (mod x)`) is injective on the primes
`x < 2·10^6` (this injectivity is equivalent to the conjecture); and the primes outside its
image, below `440`, are exactly the listed terms of A061303.

Conventions: `next x = sInf {r | r prime ∧ r ≡ 1 [MOD x]}`; for `x` prime the set is nonempty
(Dirichlet), so this is the smallest such prime. `s p n` is the `n`-fold iterate of `next` on
`p`, and `S(p) = Set.range (s p)`.
-/

namespace OMA.S_oeis_a061303

/-- The smallest prime `≡ 1 (mod x)`. -/
noncomputable def next (x : ℕ) : ℕ := sInf {r : ℕ | r.Prime ∧ r ≡ 1 [MOD x]}

/-- `s p n = s(p, n)`. -/
noncomputable def s (p : ℕ) : ℕ → ℕ
  | 0 => p
  | n + 1 => next (s p n)

/-- `S(p)`, the set of terms of the sequence `s(p, ·)`. -/
noncomputable def S (p : ℕ) : Set ℕ := Set.range (s p)

/-- The conjecture: for primes `p`, `q`, `S(p)` and `S(q)` are disjoint unless one contains
the other. -/
theorem main : ∀ p q : ℕ, p.Prime → q.Prime →
    Disjoint (S p) (S q) ∨ S p ⊆ S q ∨ S q ⊆ S p := by
  sorry

end OMA.S_oeis_a061303

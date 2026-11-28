import Mathlib

/-!
# A128379: only the 23rd and 24th iterated partial sums of Ramanujan's τ have zeros

Source: https://oeis.org/A128379 (with https://oeis.org/A128378 and https://oeis.org/A000594)
A000594 is Ramanujan's tau function, `∑ τ(n) q^n = q ∏_{m ≥ 1} (1 - q^m)^24`. A128379 is
`A000012^23 * A000594`, i.e. the partial sum operator applied 23 times to `τ` (offset 1):
1, -1, -24, 0, 276, ... and A128378 is the 24-fold partial sums: 1, 0, -24, -24, 252, ...
Conjecture (Gary W. Adamson): "given A000012^k * A000594, k=23 and 24 are the only k's generating
sequences with zeros"; A128378 specifies `k` ranges over 1, 2, 3, ... ("k in succession =
1, 2, 3, ...").

We state: for every `k ≥ 1`, the `k`-fold partial sums `S_k` of `τ` (`S_0 = τ`,
`S_{k+1}(n) = ∑_{m=1}^{n} S_k(m)`) have a zero `S_k(n) = 0` at some `n ≥ 1` iff `k = 23` or
`k = 24`. (`k = 0` is excluded, as in the source; it would be Lehmer's conjecture, upstream
`lehmer_ramanujan_tau`.)

Formalization. `τ(n)` is the coefficient of `X^n` in `X ∏_{m=1}^{n} (1 - X^m)^24`, which equals
the coefficient of the infinite product (factors with `m > n` do not affect it).
Checked with python3: the 32 listed terms of A128379; for `1 ≤ k < 80` and `n ≤ 3000`, the only
zeros are `S_23(4) = 0` and `S_24(2) = 0`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a128379

open Polynomial

/-- Ramanujan's tau function A000594. -/
noncomputable def τ (n : ℕ) : ℤ :=
  (X * ∏ m ∈ Finset.range n, (1 - X ^ (m + 1)) ^ 24 : ℤ[X]).coeff n

/-- `S k n`: the partial sum operator applied `k` times to `τ`. -/
noncomputable def S : ℕ → ℕ → ℤ
  | 0, n => τ n
  | k + 1, n => ∑ m ∈ Finset.Icc 1 n, S k m

theorem main : ∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ S k n = 0) ↔ k = 23 ∨ k = 24) := by
  sorry

end OMA.S_oeis_a128379

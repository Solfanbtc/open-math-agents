import Mathlib

/-!
# A060941: Duchon's numbers

The number of paths of length `5n` from the origin to the line `y = 2x/3` with unit East and
North steps that stay below the line or touch it.

Source: https://oeis.org/A060941
Credit: @Solfanbtc

Conjecture (Peter Bala, Sep 12 2021, generalized Oct 23 2024, formula section of A060941):
let `A(x) = Σ a(n) xⁿ` be the generating function. "Let r be an integer and s a positive integer
and define a sequence u(n) by u(n) = [x^(s*n)] A(x)^(r*n). Then we conjecture that the
supercongruences u(n*p^k) == u(n*p^(k-1)) (mod p^(3*k)) hold for all primes p >= 7 and positive
integers n and k."

This contains Bala's original 2021 conjecture `b(p) ≡ b(1) (mod p³)` for primes `p ≥ 7`, where
`b(n) = [xⁿ] A(x)ⁿ` (the case `r = s = 1`, `n = k = 1`).

Formalization.
* `a n` counts East/North lattice paths from `(0,0)` to `(3n, 2n)` (the point of the line
  `y = 2x/3` reached after `5n` steps) all of whose points `(x, y)` satisfy `3y ≤ 2x`. The
  recursion `pathCount x y` counts such paths ending at `(x, y)`; it reproduces
  `1, 2, 23, 377, 7229, 151491` for `n = 0..5`.
* `A` is the generating function in `ℤ⟦X⟧`. Since `A(0) = 1`, it is a unit, and a negative power
  `A^(-m)` is `(A⁻¹)^m` with `A⁻¹ = PowerSeries.invOfUnit A 1`. The values `u(n)` are integers, and
  the congruence is `Int.ModEq` modulo `p^(3k)`.
* A python check (exact rational arithmetic) confirms the congruence for `p = 7`, `k = 1`,
  `n = 1, 2` and `(r, s) ∈ {(1,1), (-1,1), (2,1), (1,2), (-3,2), (3,5)}`.

Not formalized: Bala's companion conjecture of Oct 24 2024 about the iterated sequences
`a(i,n) = [xⁿ] (exp(Σ_{k≥1} a(i-1,k) xᵏ/k))ⁿ` with `a(1,n) = a(n)`. As written it fails: already
`a(2,5) = 1345389/4` is not an integer, and `a(2,7) - a(2,1) = 4425312757/20` is not divisible
by `7` even `7`-adically, so it cannot be stated faithfully.
-/

namespace OMA.S_oeis_a060941

/-- `pathCount x y` is the number of East/North unit-step paths from `(0,0)` to `(x,y)` whose
points `(x', y')` all satisfy `3y' ≤ 2x'` (stay below or on the line `y = 2x/3`). -/
def pathCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | x + 1, 0 => pathCount x 0
  | 0, _ + 1 => 0
  | x + 1, y + 1 =>
      if 3 * (y + 1) ≤ 2 * (x + 1) then pathCount x (y + 1) + pathCount (x + 1) y else 0

/-- Duchon's numbers: `a n` is the number of such paths of length `5n` ending on the line
`y = 2x/3`, i.e. at `(3n, 2n)`. -/
def a (n : ℕ) : ℕ := pathCount (3 * n) (2 * n)

/-- The generating function `A(x) = Σ a(n) xⁿ`. -/
noncomputable def A : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)

/-- `A(x)^m` for an integer exponent `m` (`A` is invertible since `A(0) = a 0 = 1`). -/
noncomputable def Apow (m : ℤ) : PowerSeries ℤ :=
  if 0 ≤ m then A ^ m.toNat else (PowerSeries.invOfUnit A 1) ^ (-m).toNat

/-- Bala's sequence `u(n) = [x^(s n)] A(x)^(r n)`. -/
noncomputable def u (r : ℤ) (s n : ℕ) : ℤ := PowerSeries.coeff (s * n) (Apow (r * n))

/-- Bala's conjecture: for every integer `r`, positive integer `s`, prime `p ≥ 7` and positive
integers `n, k`, `u(n p^k) ≡ u(n p^(k-1)) (mod p^(3k))`. -/
theorem main : ∀ (r : ℤ) (s : ℕ), 0 < s → ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ n k : ℕ, 0 < n → 0 < k →
      u r s (n * p ^ k) ≡ u r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a060941

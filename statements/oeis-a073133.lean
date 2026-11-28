import Mathlib

/-!
# A073133: Table by antidiagonals of T(n,k) = n*T(n,k-1) + T(n,k-2) starting with T(n,1) = 1.

Source: https://oeis.org/A073133
Credit: @Solfanbtc

Gary W. Adamson (2013, 2019) observes that row `n + 1` of the array is the INVERT transform of
row `n`, and that the array extends above the Fibonacci row by successive INVERTi transforms:

  ..., (1, -2, 5, -12, ...), (1, -1, 2, -3, ...), (1, 0, 1, 0, ...),
  (1, 1, 2, 3, ...), (1, 2, 5, 12, ...), ...

so that the rows `k` steps above the aerated sequence `(1, 0, 1, 0, ...)` are the rows `k` steps
below with alternating signs, and the row starting `(1, k, ...)` is the `(2k)`-th INVERT
transform of the same sequence with alternating signs.

Conjecture (Adamson, 2019): the same "reflection" principle holds when one starts from any
aerated sequence `1, 0, s_2, 0, s_4, 0, ...` with positive signs, the rows below being its
successive INVERT transforms and the rows above its successive INVERTi transforms.

Conventions. Sequences are indexed from 0 (their first term is the term 0). The INVERT
transform used by the array (row `n` has g.f. `1/(1 - n x - x^2)` in this indexing, and row `n+1`
is the INVERT transform of row `n`) is `b(x) = a(x) / (1 - x a(x))`, i.e. the OEIS INVERT transform
`1 + Σ_{m ≥ 1} b_m x^m = 1 / (1 - Σ_{m ≥ 1} a_m x^m)` for the sequences read with offset 1.
Equivalently `b_m = a_m + Σ_{i + j = m - 1} a_i b_j`. INVERTi is its inverse,
`b(x) = a(x) / (1 + x a(x))`, i.e. `b_m = a_m - Σ_{i + j = m - 1} a_i b_j`.
The `#eval`s in a scratch file reproduce the six rows shown above from `(1, 0, 1, 0, ...)`.

`main` states both parts of the principle for every such sequence and every `k`:
the `k`-th INVERT transform is the `k`-th INVERTi transform with alternating signs, and
the `k`-th INVERT transform is the `(2k)`-th INVERT transform of itself with alternating signs.
(In g.f. terms `1 / INVERT^k(s)(x) = 1 / s(x) - k x` and `1 / INVERTi^k(s)(x) = 1 / s(x) + k x`, so for
an even `s(x)` the claim is elementary; the hypotheses are kept exactly as the source states them.)
-/

namespace OMA.S_oeis_a073133

/-- `b_m = a_m + σ * Σ_{i + j = m - 1} a_i b_j`: INVERT for `σ = 1`, INVERTi for `σ = -1`. -/
def transform (σ : ℤ) (a : ℕ → ℤ) : ℕ → ℤ
  | m => a m + σ * ∑ i : Fin m, a i * transform σ a (m - 1 - i)
termination_by m => m
decreasing_by omega

/-- The INVERT transform, `b(x) = a(x) / (1 - x a(x))`. -/
def invert (a : ℕ → ℤ) : ℕ → ℤ := transform 1 a

/-- The INVERTi transform, `b(x) = a(x) / (1 + x a(x))`. -/
def inverti (a : ℕ → ℤ) : ℕ → ℤ := transform (-1) a

/-- Adamson's reflection conjecture for aerated sequences `1, 0, s_2, 0, s_4, ...`
with positive terms `s_{2i}`. -/
theorem main : ∀ s : ℕ → ℤ, s 0 = 1 → (∀ i, s (2 * i + 1) = 0) →
    (∀ i, 0 < s (2 * i)) → ∀ k : ℕ,
    (∀ m, (invert^[k] s) m = (-1) ^ m * (inverti^[k] s) m) ∧
      invert^[2 * k] (fun m => (-1) ^ m * (invert^[k] s) m) = invert^[k] s := by
  sorry

end OMA.S_oeis_a073133

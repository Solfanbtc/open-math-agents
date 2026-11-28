import Mathlib

/-!
# A054391: non-capturing set partitions of {1..n}

Source: https://oeis.org/A054391
Credit: @Solfanbtc

A054391 (offset 0): "Number of permutations with certain forbidden subsequences" (Barcucci et
al., From Motzkin to Catalan Permutations); data 1, 1, 2, 5, 14, 41, 123, 374, 1147, 3538, …
Its g.f. (Mansour and Shattuck) is `1 - 2x^2 / (2x^2 - 3x + 1 - sqrt(1 - 2x - 3x^2))`. Writing
`sqrt(1 - 2x - 3x^2) = 1 - x - 2x^2 M(x)` with `M(x)` the Motzkin g.f. (`M = 1 + xM + x^2 M^2`),
this is `1 + x / (1 - x - x M(x))`, which we use as the definition (`M` via its coefficient
recurrence `m(0) = 1`, `m(k+1) = m(k) + Sum_{i+j=k-1} m(i) m(j)`).

Conjecture (G. Wiseman, Jun 22 2019): "Also the number of non-capturing set partitions of
{1..n}. A set partition is capturing if it has two blocks of the form {...x...y...} and
{...z...t...} where x < z and y > t or x > z and y < t." Status: "The above conjecture is true"
(C. Sievers, Oct 29 2024, via Mansour and Shattuck).

Reading. In a block written `{…x…y…}` we have `x < y`, so the two cases say that one block has
elements `x < y` and the other elements `z < t` with `x < z < t < y` (or the same with the blocks
exchanged). `main` states: for every `n`, the number of set partitions of `Fin n` (Mathlib's
`Finpartition` of `univ`) with no two distinct blocks `B, C` and `x, y ∈ B`, `z, t ∈ C`,
`x < z < t < y`, equals `a(n)`. Checked with python3: the g.f. gives the 15 listed terms, and the
partition count matches for `0 ≤ n ≤ 9`.
-/

namespace OMA.S_oeis_a054391

open PowerSeries

/-- Motzkin numbers. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | k + 1 => motzkin k + ∑ i : Fin k, motzkin i.val * motzkin (k - 1 - i.val)
decreasing_by
  all_goals first
    | omega
    | (have := i.isLt; omega)

/-- A054391 via `1 + x / (1 - x - x M(x))`. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (1 + X * (1 - X - X * PowerSeries.mk (fun k => (motzkin k : ℚ)))⁻¹)

/-- A set partition of `Fin n` is capturing. -/
def Capturing {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n))) : Prop :=
  ∃ B ∈ P.parts, ∃ C ∈ P.parts, B ≠ C ∧
    ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ C, ∃ t ∈ C, x < z ∧ z < t ∧ t < y

/-- Wiseman's conjecture (proved by Sievers): A054391 counts the non-capturing set partitions. -/
theorem main : ∀ n : ℕ,
    ({P : Finpartition (Finset.univ : Finset (Fin n)) | ¬ Capturing P}.ncard : ℚ) = a n := by
  sorry

end OMA.S_oeis_a054391

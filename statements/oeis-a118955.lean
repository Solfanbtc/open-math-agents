import Mathlib

/-!
# A118955: Numbers of the form 2^k + prime

Source: https://oeis.org/A118955
Credit: @Solfanbtc

The set `S = {2^k + p : k ≥ 0, p prime}` (A118955: `3, 4, 5, 6, 7, 9, 10, 11, …`).

The entry (Charles R Greathouse IV, 2008 and 2021) records density bounds: "The lower density is
at least 0.09368 (Pintz) and upper density is at most 0.49095 (Habsieger & Roblot). The density,
if it exists, is called Romanov's constant. Romani conjectures that it is around 0.434.
Elsholtz & Schlage-Puchta improve the bound on lower density to 0.107648. Unpublished work by Jie
Wu improves this to 0.110114."

Stated here: the two published bounds in their best recorded form, lower density
`≥ 0.107648` (Elsholtz & Schlage-Puchta, which implies Pintz's `0.09368`) and upper density
`≤ 0.49095` (Habsieger & Roblot). These are known results (the claimed theorems of those papers).
Not stated: Romani's "around 0.434" (no precise claim) and Wu's unpublished bound; the existence
of the density is only mentioned as a hypothesis ("if it exists"), not claimed. (Upstream
`erdos_851.variants.romanoff` states only that the lower density is positive.)

Densities: with `count N = #{n ∈ [1, N] : n ∈ S}`, the lower and upper densities are
`liminf count N / N` and `limsup count N / N` (`N → ∞`; the ratios lie in `[0, 1]`).
-/

namespace OMA.S_oeis_a118955

open Classical in
/-- `#{n ∈ [1, N] : n ∈ S} / N`. (In any representation `n = 2^k + p` one has `k < n` and
`p ≤ n`, so the bounded quantifiers below describe exactly the `n ∈ S`.) -/
noncomputable def ratio (N : ℕ) : ℝ :=
  (((Finset.Icc 1 N).filter fun n =>
      ∃ k ∈ Finset.range n, ∃ p ∈ Finset.range (n + 1), p.Prime ∧ n = 2 ^ k + p).card : ℝ) / N

/-- Known bounds: lower density `≥ 0.107648`, upper density `≤ 0.49095`. -/
theorem main :
    (0.107648 : ℝ) ≤ Filter.liminf ratio Filter.atTop ∧
      Filter.limsup ratio Filter.atTop ≤ (0.49095 : ℝ) := by
  sorry

end OMA.S_oeis_a118955

import Mathlib

/-!
# A067955: dissections of a convex polygon into even-sided polygons, counted by edges.

Source: https://oeis.org/A067955
Credit: @Solfanbtc

A067955(n) (`n ≥ 1`) is the number of dissections of a convex polygon by nonintersecting
diagonals into polygons with an even number of sides, having `n` edges in total (sides and
diagonals). The entry gives its g.f. `G(z) = Σ_{n ≥ 1} a(n) z^n` by
`(1+z) G^3 - z G^2 - G + z = 0`; since `G` has no constant term and the coefficient of `G` is
`-1`, this equation determines all coefficients of `G` recursively, so it characterizes
A067955 (equivalently, `G` is the series reversion of `(x - x^3)/(1 - x^2 + x^3)`).

Conjecture (Nicholas Ham, 2015): a(n) is the number of lattice paths from `(1,0)` to `(n,0)`
that never go below the x-axis, using up-steps `(1,1)` and down-steps `(1,-z)` with `z` a
positive even integer. Such a path has `n - 1` steps. `walks m h` counts the step sequences of
length `m` from height `h` that end at height `0` without going below `0`; the paths of the
conjecture are counted by `walks (n-1) 0`. `main` states that the generating function
`Σ_{n ≥ 1} walks (n-1) 0 · z^n` satisfies the defining equation of A067955's g.f., which (by the
uniqueness above) says exactly that the counts equal A067955(n) for every `n ≥ 1`.
Checked with python3: `walks (n-1) 0` reproduces the 37 listed terms (e.g. `a(8) = 1`), and the
equation holds up to `z^39`.
-/

namespace OMA.S_oeis_a067955

open PowerSeries

/-- Number of step sequences of length `m`, starting at height `h`, with steps `+1` or `-z`
(`z` positive and even), never going below height `0` and ending at height `0`. -/
def walks : ℕ → ℕ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | m + 1, h => walks m (h + 1) +
      ∑ z ∈ (Finset.range (h + 1)).filter (fun z => 0 < z ∧ Even z), walks m (h - z)

/-- The generating function `Σ_{n ≥ 1} walks (n-1) 0 · z^n` of the path counts. -/
noncomputable def P : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (walks (n - 1) 0 : ℤ)

/-- The conjecture: the path counts have the g.f. of A067955, i.e. they equal A067955(n). -/
theorem main : (1 + X) * P ^ 3 - X * P ^ 2 - P + X = 0 := by
  sorry

end OMA.S_oeis_a067955

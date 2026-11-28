import Mathlib

/-!
# A106369: Number of circular compositions of n such that no two adjacent parts are equal.

Source: https://oeis.org/A106369
Credit: @Solfanbtc

A circular composition of `n` is an equivalence class of compositions of `n` (lists of positive
parts summing to `n`) with the parts on a circle, two compositions being equivalent when one is a
cyclic shift of the other (P. Hadjicostas, OEIS %C). No two adjacent parts may be equal: with
`k ≥ 2` parts `c_0, ..., c_{k-1}`, `c_i ≠ c_{i+1 mod k}` for all `i`. A single part has no
neighbour, so it is allowed: `a(1) = a(2) = 1`, and `a(6) = 6`: 6, 5+1, 4+2, 3+2+1, 3+1+2,
2+1+2+1.

Conjecture (V. Kotesovec, Sep 06 2017, OEIS %F): `a(n) ~ A241902^n / n`. Here
`A241902 = 1.75024129...` is `lim A003242(n)^(1/n)`, the growth constant of Carlitz compositions,
equivalently `1/ρ` where `ρ ∈ (0,1)` is the root of `Σ_{k ≥ 1} ρ^k/(1 + ρ^k) = 1` (the singularity
of the Carlitz g.f. `1/(1 - Σ_{k≥1} x^k/(1+x^k))`). The left side is strictly increasing on
`(0,1)`, from 0 to infinity, so that root is unique, and quantifying over it is equivalent to
naming it. Numerically `1/ρ = 1.7502412917183...`, matching A241902. The definition of `a` below was
evaluated in Lean for `n = 1..14` and matches the data.
-/

namespace OMA.S_oeis_a106369

/-- The parts are circularly Carlitz: with at least two parts, cyclically adjacent parts
differ. -/
def CircCarlitz (l : List ℕ) : Prop :=
  2 ≤ l.length → ∀ i < l.length, l.getD i 0 ≠ l.getD ((i + 1) % l.length) 0

instance : DecidablePred CircCarlitz := fun l => by unfold CircCarlitz; infer_instance

/-- A106369(n): circular compositions of `n` with no two adjacent parts equal, counted up to
rotation (`Cycle ℕ` is the quotient of lists by rotation). -/
def a (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Composition n)).filter (fun c => CircCarlitz c.blocks)).image
    (fun c => (c.blocks : Cycle ℕ))).card


theorem main : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∑' k : ℕ, ρ ^ (k + 1) / (1 + ρ ^ (k + 1)) = 1 →
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / ((1 / ρ) ^ n / n)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a106369

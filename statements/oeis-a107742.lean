import Mathlib

/-!
# A107742: G.f.: Product{j>=1} Product{i>=1} (1 + x^(i*j)).

Source: https://oeis.org/A107742
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Aug 29 2018, %F line of A107742):
`log(a(n)) ~ π * sqrt(n * log(n) / 6)`.

Formalization.
* Expanding `∏_{i ≥ 1} ∏_{j ≥ 1} (1 + x^(i j))`, the coefficient of `x^n` is the number of
  finite sets `S` of pairs `(i, j)` of positive integers with `∑_{(i,j) ∈ S} i j = n`. Every pair
  in such a set has `i j ≤ n`, so `i, j ≤ n`, and `a n` counts the subsets of
  `{(i, j) | 1 ≤ i, j ≤ n, i j ≤ n}` with that sum (`a 0 = 1`, the empty set).
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`.

Checked with python3 (via `∏_k (1 + x^k)^{d(k)}`, an equivalent g.f. given in the entry) and
`#eval` of `a` for `n ≤ 7`: the definition reproduces the listed terms
`1, 1, 2, 4, 6, 10, 17, 25, ...`.
-/

namespace OMA.S_oeis_a107742

open Asymptotics Filter

/-- Pairs `(i, j)` with `1 ≤ i, j` and `i * j ≤ n`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => p.1 * p.2 ≤ n)

/-- A107742: the coefficient of `x^n` in `∏_{i,j ≥ 1} (1 + x^(i j))`. -/
def a (n : ℕ) : ℕ :=
  ((pairs n).powerset.filter (fun S => ∑ p ∈ S, p.1 * p.2 = n)).card

/-- Kotesovec's conjecture: `log a(n) ~ π √(n log n / 6)`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => Real.log (a n))
    (fun n : ℕ => Real.pi * Real.sqrt (n * Real.log n / 6)) := by
  sorry

end OMA.S_oeis_a107742

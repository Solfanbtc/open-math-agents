import Mathlib

/-!
# A096969: Number of ways to number the cells of an n X n square grid with 1,2,3,...,n^2 so that successive integers are in adjacent cells (horizontally or vertically).

Source: https://oeis.org/A096969
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of numberings of the cells of the `n × n` grid by `1, ..., n²`
such that successive integers are in horizontally or vertically adjacent cells, i.e. the number
of directed Hamiltonian paths in the `n × n` grid graph: `1, 8, 40, 552, 8648, ...`.

Conjecture (Nicolas Bělohoubek, Jun 12 2022, in the entry):
`lim_{n → ∞} (log_{(n+1)!} a(n+1) - log_{n!} a(n)) = c` with `0.09 < c < 0.11`, where
`log_b x = log x / log b`. Stated as: there is `c` with `0.09 < c < 0.11` such that
`log a(n+1) / log (n+1)! - log a(n) / log n! → c`.

A python3 check: a brute-force count gives `1, 8, 40, 552` for `n ≤ 4`; from the 15 data terms the
differences for `n = 8, ..., 14` are `0.116, 0.066, 0.122, 0.082, 0.122, 0.090, 0.120, 0.094`
(oscillating). (Remark, not part of the statement: if `log a(n) ~ κ n²`, as the usual connective-
constant heuristics suggest, the difference would tend to 0 like `κ / log n`.)

Conventions: a numbering is a bijection `f : Fin (n²) ≃ Fin n × Fin n` (cell of the number
`i + 1`); cells `(r, s)` and `(r', s')` are adjacent iff they differ by 1 in exactly one
coordinate. `a(n)` is the cardinality of the finite set of such bijections with `f i` and
`f (i+1)` adjacent for all `i + 1 < n²`.
-/

namespace OMA.S_oeis_a096969

open Filter Topology

/-- Horizontally or vertically adjacent cells of the grid. -/
def Adj {n : ℕ} (x y : Fin n × Fin n) : Prop :=
  (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- `a n = A096969(n)`: directed Hamiltonian paths in the `n × n` grid. -/
noncomputable def a (n : ℕ) : ℕ :=
  {f : Fin (n ^ 2) ≃ Fin n × Fin n |
    ∀ i : Fin (n ^ 2), ∀ h : i.val + 1 < n ^ 2, Adj (f i) (f ⟨i.val + 1, h⟩)}.ncard

/-- `log_{n!} a(n)`. -/
noncomputable def L (n : ℕ) : ℝ := Real.log (a n) / Real.log (n.factorial)

/-- Bělohoubek's conjecture. -/
theorem main : ∃ c : ℝ, 0.09 < c ∧ c < 0.11 ∧
    Tendsto (fun n : ℕ => L (n + 1) - L n) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a096969

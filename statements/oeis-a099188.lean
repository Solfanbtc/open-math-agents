import Mathlib

/-!
# A099188: shortest lattice path with integer edges from (0,0) to (n,n)

Source: https://oeis.org/A099188
`a(n) = 2 ⌈n / √2⌉` (offset 0): 0, 2, 4, 6, 6, 8, 10, 10, ...
The entry says: "Conjecturally, length of shortest polygonal path from (0,0) to (n,n) with integer
vertices and edges. This is true for n <= 10000."

Formalization. A polygonal path with integer vertices and integer edges is a list of edges, each an
integer vector `(x, y)` together with its length `d : ℕ` with `x^2 + y^2 = d^2`; consecutive
vertices are partial sums, so the path goes from `(0,0)` to `(n,n)` iff the edge vectors sum to
`(n, n)`, and its length is the sum of the `d`. The conjecture: for every `n`, some such path has
length `a(n)`, and every such path has length at least `a(n)`.
Checked with python3: the data agree with `2 ⌈n/√2⌉` (via the entry's PARI form
`2 + 2 isqrt((n^2-1)/2)`), and a Dijkstra search over integer-length steps (vertices within 6 of
the square `[0,n]^2`) gives shortest length `a(n)` for all `n ≤ 40`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a099188

/-- A099188: `2 ⌈n / √2⌉`. -/
noncomputable def a (n : ℕ) : ℤ := 2 * ⌈(n : ℝ) / Real.sqrt 2⌉

/-- A list of edges `(x, y, d)` is a polygonal path from `(0,0)` to `(n,n)` with integer
vertices and integer edges: each edge vector `(x, y)` has integer length `d`, and the edge
vectors add up to `(n, n)`. -/
def IsPath (n : ℕ) (P : List (ℤ × ℤ × ℕ)) : Prop :=
  (∀ e ∈ P, e.1 ^ 2 + e.2.1 ^ 2 = (e.2.2 : ℤ) ^ 2) ∧
  (P.map (·.1)).sum = n ∧ (P.map (·.2.1)).sum = n

/-- The length of the path. -/
def length (P : List (ℤ × ℤ × ℕ)) : ℕ := (P.map (·.2.2)).sum

theorem main : ∀ n : ℕ,
    (∃ P, IsPath n P ∧ (length P : ℤ) = a n) ∧
    ∀ P, IsPath n P → a n ≤ length P := by
  sorry

end OMA.S_oeis_a099188

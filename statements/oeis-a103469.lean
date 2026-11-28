import Mathlib

/-!
# A103469: components of the Collatz graph on {1, …, n} and polyominoes of three n-gons

Source: https://oeis.org/A103469
Credit: @Solfanbtc

A103469 (offset 3): the number of polyominoes consisting of 3 regular unit `n`-gons; by the
entry's formula `a(n) = floor((n-2)/2) - floor((n-1)/6) + 1`, which we use as the definition.
Data 1, 2, 2, 3, 2, 3, 3, 4, 4, 5, …

Conjecture (L. Sauras Altuzarra, Apr 07 2020, corrected by P. von Brömssen, Jan 22 2021): "if
n > 3, then a(n + 3) is the number of connected components of the subgraph that is
vertex-induced on Collatz's graph by the vertex subset {1, ..., n}."

Definitions. Collatz's graph has the positive integers as vertices and an edge between `m` and
`T(m)`, where `T(m) = m/2` for even `m` and `T(m) = 3m + 1` for odd `m`. The induced subgraph on
`{1, …, n}` is modelled on `Fin n` (vertex `i` is the number `i + 1`), with `i ~ j` iff `i ≠ j`
and one of `i + 1`, `j + 1` is the image of the other under `T`. (The loop-free reading matters
only for `T(m) = m`, which never happens for `m ≥ 1`.) Checked with python3: with this map (and
not with the shortcut map `(3m + 1)/2`) the identity holds for `4 ≤ n < 3000`.
-/

namespace OMA.S_oeis_a103469

/-- A103469 by the entry's formula. -/
def a (n : ℕ) : ℕ := (n - 2) / 2 - (n - 1) / 6 + 1

/-- The Collatz map. -/
def T (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

/-- The subgraph of Collatz's graph induced by `{1, …, n}`, on `Fin n` (vertex `i` is `i + 1`). -/
def collatzGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => T (i.val + 1) = j.val + 1

/-- The conjecture: for `n > 3`, the induced Collatz graph on `{1, …, n}` has `a(n + 3)`
connected components. -/
theorem main : ∀ n : ℕ, 3 < n → Nat.card (collatzGraph n).ConnectedComponent = a (n + 3) := by
  sorry

end OMA.S_oeis_a103469

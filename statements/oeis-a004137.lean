import Mathlib

/-!
# A004137: Maximal number of edges in a graceful graph on n nodes.

Source: https://oeis.org/A004137
Credit: @Solfanbtc

The source conjecture (P. Luschny): an optimal ruler with more than 12 segments is a Wichmann
ruler, so that it is impossible to improve upon Wichmann's construction, and the sequence
continues 232, 251, 270, 289, 308, 327, ... (these are the terms for n = 26, ..., 31).

Conventions used here.
* A graceful labeling of a graph `G` with `m` edges on the vertex set `Fin n` is an injective map
  `f : Fin n → ℕ` with values in `{0, ..., m}` such that distinct edges get distinct labels
  `|f u - f v|` (the labels are then exactly `1, ..., m`). Isolated vertices are allowed.
  `a n` is the largest number of edges of a graceful graph on `n` vertices; it equals the largest
  length of a complete ruler with `n` marks (marks = vertex labels, one edge per distance).
  Brute force gives `a 1, ..., a 9 = 0, 1, 3, 6, 9, 13, 17, 23, 29`, matching the OEIS data.
* The Wichmann ruler `W(r, s)` has the segment sequence
  `1^r, r+1, (2r+1)^r, (4r+3)^s, (2r+2)^(r+1), 1^r`: it has `4r+s+2` segments, `n = 4r+s+3`
  marks and length `4r(r+s+2) + 3(s+1)`. `wichmannMax n` is the largest Wichmann length with `n`
  marks. For `n = 21` it is `153` (`r = 3`, `s = 6`, the ruler quoted on the OEIS page), and for
  `n = 26, ..., 31` it is `232, 251, 270, 289, 308, 327`, the continuation stated in the source.
* "More than 12 segments" means at least 13 segments, i.e. `n ≥ 14` marks. The bound is sharp:
  `a 13 = 58` while `wichmannMax 13 = 57`.

Since every Wichmann ruler is a complete ruler, `wichmannMax n ≤ a n` always holds; the
conjecture that Wichmann's construction cannot be improved is the statement `a n = wichmannMax n`
for all `n ≥ 14`, which is what `main` states (the stronger claim that every optimal ruler is
itself of Wichmann type is not needed for the values of the sequence and is not stated).
-/

namespace OMA.S_oeis_a004137

/-- `G` on `Fin n` is graceful: some injective labeling `f` with values in `{0, ..., #edges}`
gives distinct edges distinct differences `|f u - f v|`. -/
def IsGraceful {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → ℕ, Function.Injective f ∧ (∀ v, f v ≤ G.edgeSet.ncard) ∧
    ∀ u v u' v', G.Adj u v → G.Adj u' v' →
      |(f u : ℤ) - f v| = |(f u' : ℤ) - f v'| → s(u, v) = s(u', v')

/-- A004137: the maximal number of edges in a graceful graph on `n` nodes. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n), IsGraceful G ∧ G.edgeSet.ncard = m}

/-- The largest length `4r(r+s+2) + 3(s+1)` of a Wichmann ruler `W(r, s)` with
`n = 4r + s + 3` marks (`r, s ≥ 0`); `0` if `n < 3`. -/
def wichmannMax (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun r => 4 * r + 3 ≤ n)).sup
    (fun r => 4 * r * (r + (n - 3 - 4 * r) + 2) + 3 * ((n - 3 - 4 * r) + 1))

/-- Luschny's conjecture: for rulers with more than 12 segments (`n ≥ 14` marks) Wichmann's
construction is optimal, so `a n` is the largest Wichmann length. -/
theorem main : ∀ n : ℕ, 14 ≤ n → a n = wichmannMax n := by
  sorry

end OMA.S_oeis_a004137

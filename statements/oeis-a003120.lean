import Mathlib

/-!
# A003120: Number of rooted trees with n nodes and omega-valency 1.

Source: https://oeis.org/A003120
Credit: @Solfanbtc

Claim in the entry: "The g.f. -(z-1)*(3*z**2+z-1)/(-1+3*z+z**2-7*z**3+3*z**4) conjectured by
Simon Plouffe in his 1992 dissertation is wrong (starting from index 11)."

Reading (offset 1, so the coefficient of `z^(n-1)` is compared with `a(n)`, as the g.f. starts
`1 + z + 2z^2 + ...` like the data `1, 1, 2, ...`): the g.f. coefficients agree with `a(n)` for
`1 ≤ n ≤ 10` and the first disagreement is at index 11. Python check: the coefficients are
`1, 1, 2, 3, 7, 13, 31, 66, 159, 365, 885, ...` against `a = 1, 1, 2, 3, 7, 13, 31, 66, 159, 365,
900, ...`. "Starting from index 11" only says where the first wrong term is, so nothing is claimed
about later indices.

Definitions:
* Unlabeled rooted trees are plane trees `RTree.node children` up to reordering children at every
  node: `Iso` relates `node l₁` and `node l₂` when some reordering of `l₂` matches `l₁` entrywise
  by `Iso`; counting is done in `Quot Iso`.
* Omega-valency (F. Chapoton, N. J. A. Sloane, in the entry): a leaf has omega-valency 1; any
  other vertex has `max(1, Σ (omega-valencies of its children) - 1)`. Over `ℤ` the leaf case is
  the same formula with an empty sum (`max 1 (0 - 1) = 1`). The tree's omega-valency is that of the
  root. A Python enumeration with this definition reproduces the data for `n ≤ 14`.
-/

namespace OMA.S_oeis_a003120

/-- Plane rooted trees: a root with an ordered list of subtrees. -/
inductive RTree where
  | node : List RTree → RTree

mutual
/-- Number of nodes. -/
def RTree.size : RTree → ℕ
  | .node l => 1 + RTree.sizeList l

/-- Total number of nodes of a list of trees. -/
def RTree.sizeList : List RTree → ℕ
  | [] => 0
  | t :: ts => RTree.size t + RTree.sizeList ts
end

mutual
/-- Omega-valency of the root. -/
def RTree.omega : RTree → ℤ
  | .node l => max 1 (RTree.omegaSum l - 1)

/-- Sum of the omega-valencies of a list of trees. -/
def RTree.omegaSum : List RTree → ℤ
  | [] => 0
  | t :: ts => RTree.omega t + RTree.omegaSum ts
end

/-- Rooted-tree isomorphism: children may be reordered at every node. -/
inductive Iso : RTree → RTree → Prop
  | node {l₁ l₂ l : List RTree} : l₂.Perm l → List.Forall₂ Iso l₁ l →
      Iso (.node l₁) (.node l₂)

/-- A003120: unlabeled rooted trees with `n` nodes and omega-valency 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Quot.mk Iso '' {t : RTree | t.size = n ∧ t.omega = 1}).ncard

open PowerSeries in
/-- Plouffe's conjectured g.f. `-(z-1)(3z^2+z-1) / (-1+3z+z^2-7z^3+3z^4)`. -/
noncomputable def plouffeGF : PowerSeries ℚ :=
  (-(X - 1) * (3 * X ^ 2 + X - 1)) * (-1 + 3 * X + X ^ 2 - 7 * X ^ 3 + 3 * X ^ 4)⁻¹

/-- Plouffe's g.f. matches A003120 up to index 10 and is wrong at index 11. -/
theorem main :
    (∀ n, 1 ≤ n → n ≤ 10 → PowerSeries.coeff (n - 1) plouffeGF = (a n : ℚ)) ∧
    PowerSeries.coeff 10 plouffeGF ≠ (a 11 : ℚ) := by
  sorry

end OMA.S_oeis_a003120

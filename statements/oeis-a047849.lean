import Mathlib

/-!
# A047849: a(n) = (4^n + 2)/3.

Source: https://oeis.org/A047849
Credit: @Solfanbtc

The OEIS entry records: "A. A. Ivanov conjectures that the dimension of the universal embedding
of the unitary dual polar space DSU(2n,4) is a(n)." (see also B. N. Cooperstein and E. E. Shult,
*A note on embedding and generating dual polar spaces*, Adv. Geom. 1 (2001), 37-48, Conjecture 5.5).
This was proved by P. Li, *On the universal embedding of the U_{2n}(2) dual polar space*,
J. Combin. Theory Ser. A 94 (2001), 100-117; we state it faithfully nevertheless.

## Model
* `F = GaloisField 2 2` is the field with 4 elements, with involution `x ↦ x ^ 2`.
* `V n = Fin (2n) → F` carries the non-degenerate Hermitian form `h x y = ∑ i, x i * (y i) ^ 2`
  (all non-degenerate Hermitian forms on `F^(2n)` are equivalent, so the choice does not matter).
* The dual polar space DSU(2n,4) = DU(2n-1,4): its points are the totally isotropic subspaces of
  dimension `n` (the maximal ones), its lines are the totally isotropic subspaces of dimension
  `n - 1`, a point lying on a line when it contains it. Each line has exactly `q + 1 = 3` points.
* For a point-line geometry with three points per line, the universal embedding (Ronan) is the
  `𝔽₂`-vector space spanned by the points subject to the relations `p + q + r = 0` for the three
  points `p, q, r` of each line; its dimension is the vector-space dimension of this quotient.
  We encode the relations as `single p + single q + single r` for pairwise distinct points
  `p, q, r` that contain a common line (exactly the three points of that line).

Sanity check (python, outside Lean): for `n = 1, 2, 3` the geometry has 3, 27, 891 points,
1, 45, 6237 lines, every line has 3 points, and the quotient has dimension 2, 6, 22 = a(n).
-/

namespace OMA.S_oeis_a047849

/-- The field with four elements. -/
abbrev F := GaloisField 2 2

/-- The ambient space `F^(2n)`. -/
abbrev V (n : ℕ) := Fin (2 * n) → F

/-- The standard non-degenerate Hermitian form on `F^(2n)` (conjugation is `x ↦ x ^ 2`). -/
noncomputable def herm {n : ℕ} (x y : V n) : F := ∑ i, x i * (y i) ^ 2

/-- A subspace is totally isotropic for `herm`. -/
def IsTotallyIsotropic {n : ℕ} (W : Submodule F (V n)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, herm x y = 0

/-- Points of the dual polar space DSU(2n,4): totally isotropic subspaces of dimension `n`. -/
def DPoint (n : ℕ) : Type :=
  {W : Submodule F (V n) // IsTotallyIsotropic W ∧ Module.finrank F W = n}

/-- Lines of the dual polar space DSU(2n,4): totally isotropic subspaces of dimension `n - 1`. -/
def DLine (n : ℕ) : Type :=
  {W : Submodule F (V n) // IsTotallyIsotropic W ∧ Module.finrank F W = n - 1}

/-- The relations of the universal embedding: the sum of the three points of a line. -/
def lineRelations (n : ℕ) : Set (DPoint n →₀ ZMod 2) :=
  {v | ∃ (L : DLine n) (p q r : DPoint n), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    L.1 ≤ p.1 ∧ L.1 ≤ q.1 ∧ L.1 ≤ r.1 ∧
    v = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1}

/-- The universal embedding module of DSU(2n,4) over `𝔽₂`. -/
abbrev UnivEmb (n : ℕ) : Type :=
  (DPoint n →₀ ZMod 2) ⧸ Submodule.span (ZMod 2) (lineRelations n)

/-- Ivanov's conjecture (proved by P. Li, 2001): the universal embedding of the unitary dual
polar space DSU(2n,4) has dimension `(4^n + 2)/3` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    Module.finrank (ZMod 2) (UnivEmb n) = (4 ^ n + 2) / 3 := by
  sorry

end OMA.S_oeis_a047849

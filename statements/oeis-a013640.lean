import Mathlib

/-!
# A013640: f-vector for 20-dimensional simplicial polytope providing counterexample to unimodality conjecture.

Source: https://oeis.org/A013640
Credit: @Solfanbtc

Claim (OEIS A013640, name and comment): the listed numbers are the f-vector of a
20-dimensional simplicial polytope, and this f-vector fails the unimodality conjecture because
a(11) > a(12) < a(13). Status: a known result, not open: this is the counterexample of
A. Björner (The unimodality conjecture for convex polytopes, Bull. AMS 4 (1981)), reproduced in
G. M. Ziegler, Lectures on Polytopes, Springer 1995, p. 272. It is stated faithfully here.

Conventions:
* The entry has offset -1: a(i) = f_i is the number of i-dimensional faces, for i = -1..19
  (f_{-1} = 1 counts the empty face; the polytope itself, of dimension 20, is not counted).
  `fvec` lists a(-1), a(0), ..., a(19), all 21 terms of %S/%T/%U, so a(i) = `fvec[i+1]`.
* A polytope is the convex hull of a finite set `V` in `ℝ^20` (`EuclideanSpace ℝ (Fin 20)`);
  it is 20-dimensional when its affine span is the whole space. Its nonempty faces are its
  nonempty exposed subsets (Mathlib's `IsExposed`: the maximizers over the polytope of a
  continuous linear functional; for polytopes these are exactly the faces, the zero functional
  giving the polytope itself). The dimension of a nonempty face is the dimension of its affine
  span.
* Simplicial: every nonempty proper face is a simplex, i.e. its extreme points (its vertices)
  are affinely independent.
* Checked in Python: the h-vector computed from this f-vector satisfies the Dehn-Sommerville
  relations h_k = h_{20-k}, and a(11) = 821976324224631043 > a(12) = 821976324224611712 <
  a(13) = 822000129478641948.
-/

namespace OMA.S_oeis_a013640

/-- `ℝ^20`. -/
abbrev E := EuclideanSpace ℝ (Fin 20)

/-- The listed terms a(-1), a(0), ..., a(19). -/
def fvec : List ℕ :=
  [1, 4203045807626, 84060916163336, 798578704207074, 4791472253296106, 20363758019368323,
    65164051780016980, 162910744316489788, 325834059588060117, 529707205213463823,
    709935971390166248, 805494832051588614, 821976324224631043, 821976324224611712,
    822000129478641948, 747383755288236256, 546761228419958342, 293715859557026466,
    106920718330384544, 23458617733909980, 2345861773390998]

/-- The number of `k`-dimensional faces of the polytope `P`. -/
noncomputable def numFaces (P : Set E) (k : ℕ) : ℕ :=
  {F : Set E | IsExposed ℝ P F ∧ F.Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

/-- The listed numbers are the f-vector of a simplicial 20-polytope, and they fail
unimodality: a(11) > a(12) < a(13). -/
theorem main :
    (fvec.getD 12 0 > fvec.getD 13 0 ∧ fvec.getD 13 0 < fvec.getD 14 0) ∧
    ∃ V : Finset E,
      affineSpan ℝ (convexHull ℝ (V : Set E)) = ⊤ ∧
      (∀ F : Set E, IsExposed ℝ (convexHull ℝ (V : Set E)) F → F.Nonempty →
        F ≠ convexHull ℝ (V : Set E) →
        AffineIndependent ℝ (Subtype.val : Set.extremePoints ℝ F → E)) ∧
      ∀ k : ℕ, k < 20 → numFaces (convexHull ℝ (V : Set E)) k = fvec.getD (k + 1) 0 := by
  sorry

end OMA.S_oeis_a013640

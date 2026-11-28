import Mathlib

/-!
# A049486: Maximum length of non-crossing path on n X n square lattice.

Source: https://oeis.org/A049486
Credit: @Solfanbtc

Conjectures (Colin Barker, May 02 2013, OEIS A049486):
1. a(n) = (9 + (-1)^n - 8n + 4n^2)/2 for n > 2;
2. a(n) = 2a(n-1) - 2a(n-3) + a(n-4) for n > 6;
3. G.f.: -x(x^5 - x^4 + 3x^3 + 2x^2 + 2x + 1)/((x-1)^3 (x+1)).
Status: the entry contains an informal argument for the values (Hugo van der Sanden, Sep 27 2005:
count edges, pair up the odd-degree vertices, and Fleury's algorithm), so 1 is believed known.

Translation.
* The lattice is the n X n grid of points, i.e. the box product of two paths on n vertices
  (a(2) = 4: the unit square; a(3) = 10: the 2 X 2 block of cells, 12 edges and 4 odd vertices).
  The entry's comment says "one can reuse a point, but not an edge": a path is a trail
  (`SimpleGraph.Walk.IsTrail`), its length the number of edges.
* 2 is a consequence of 1 (all indices > 2) and is included for completeness. 3 encodes 1 together
  with a(1) = 1 and a(2) = 4. The value a(1) = 1 is a convention of the entry (the one-point
  lattice has only the trail of length 0; van der Sanden's comment explains this convention), so
  it is left out: `main` states 1 and 2 for the trail maximum, and a(2) = 4.
Checked against all 41 listed terms (the formula gives 10, 21, 34, 53, ... for n = 3, 4, 5, 6, ...).
-/

namespace OMA.S_oeis_a049486

/-- The n X n square lattice of points. -/
abbrev grid (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.boxProd (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph n)

/-- `L` is the maximum length of a trail (no repeated edge) in the n X n lattice. -/
def IsMaxTrailLength (n L : ℕ) : Prop :=
  IsGreatest {k : ℕ | ∃ (u v : Fin n × Fin n) (w : (grid n).Walk u v), w.IsTrail ∧ w.length = k} L

theorem main :
    IsMaxTrailLength 2 4 ∧
    (∀ n : ℕ, 2 < n → ∀ L : ℕ, IsMaxTrailLength n L →
      2 * (L : ℤ) = 9 + (-1) ^ n - 8 * n + 4 * (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 6 < n → ∀ L L1 L3 L4 : ℕ, IsMaxTrailLength n L → IsMaxTrailLength (n - 1) L1 →
      IsMaxTrailLength (n - 3) L3 → IsMaxTrailLength (n - 4) L4 →
      (L : ℤ) = 2 * L1 - 2 * L3 + L4) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ L : ℕ, IsMaxTrailLength n L) := by
  sorry

end OMA.S_oeis_a049486

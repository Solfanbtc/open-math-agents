import Mathlib

/-!
# A063524: Characteristic function of 1.

Source: https://oeis.org/A063524
Credit: @Solfanbtc

Comment by Christopher Hunt Gribble (Jul 11 2013): `a(n)` (`= 1` if `n = 1`, else `0`) is, for
`1 ≤ n ≤ 4`, and conjecturally for `n > 4`, the number of Hamiltonian circuits in a `2n × 2n`
square lattice of nodes whose orbit under the symmetry group `D4` of the square has 1 element,
i.e. the Hamiltonian circuits fixed by all 8 symmetries of the square.

`main` states this for every `n ≥ 1`.

* The lattice is the grid graph `pathGraph (2n) □ pathGraph (2n)` on `Fin (2n) × Fin (2n)`.
* A Hamiltonian circuit is identified with its set of edges (a circuit has no start point or
  direction), i.e. the edge set of some closed walk that is a Hamiltonian cycle.
* The 8 symmetries of the square are the maps `(i, j) ↦ (i', j')` that optionally reverse each
  coordinate (`Fin.rev`) and optionally swap the two coordinates.

Checked by brute force in python3: the numbers of Hamiltonian circuits are 1, 6, 1072 for
`n = 1, 2, 3`, of which 1, 0, 0 are fixed by all of `D4`.
-/

namespace OMA.S_oeis_a063524

/-- The `2n × 2n` square lattice of nodes. -/
abbrev grid (n : ℕ) : SimpleGraph (Fin (2 * n) × Fin (2 * n)) :=
  SimpleGraph.pathGraph (2 * n) □ SimpleGraph.pathGraph (2 * n)

/-- Optionally reverse a coordinate. -/
def flip {m : ℕ} (b : Bool) (i : Fin m) : Fin m := if b then i.rev else i

/-- The symmetry of the square given by `(r₁, r₂, s)`: reverse the first coordinate if `r₁`,
the second if `r₂`, then swap the coordinates if `s`. These are the 8 elements of `D4`. -/
def symm {m : ℕ} (r₁ r₂ s : Bool) (p : Fin m × Fin m) : Fin m × Fin m :=
  if s then (flip r₂ p.2, flip r₁ p.1) else (flip r₁ p.1, flip r₂ p.2)

/-- `E` is the edge set of a Hamiltonian circuit of the `2n × 2n` lattice. -/
def IsHamiltonianCircuit (n : ℕ) (E : Set (Sym2 (Fin (2 * n) × Fin (2 * n)))) : Prop :=
  ∃ (u : Fin (2 * n) × Fin (2 * n)) (w : (grid n).Walk u u),
    w.IsHamiltonianCycle ∧ {e | e ∈ w.edges} = E

/-- Gribble: for every `n ≥ 1`, the number of Hamiltonian circuits of the `2n × 2n` lattice
fixed by all of `D4` is `A063524(n)`, i.e. `1` if `n = 1` and `0` otherwise. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    {E | IsHamiltonianCircuit n E ∧
        ∀ r₁ r₂ s : Bool, Sym2.map (symm r₁ r₂ s) '' E = E}.ncard =
      if n = 1 then 1 else 0 := by
  sorry

end OMA.S_oeis_a063524

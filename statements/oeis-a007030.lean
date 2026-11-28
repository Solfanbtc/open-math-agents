import Mathlib

/-!
# A007030: Non-Hamiltonian simplicial polyhedra with n nodes.

Source: https://oeis.org/A007030
Credit: @Solfanbtc

Claim (COMMENT): "a(18) = 1879665 was conjectured by Dillencourt and verified by direct
computation by Sean A. Irvine, Sep 26 2017." Stated here: a(18) = 1879665.

Conventions.
* By Steinitz's theorem (COMMENT of W. P. Orrick), simplicial polyhedra with n nodes, up to
  combinatorial equivalence, correspond to maximal planar graphs on n vertices up to graph
  isomorphism (for n ≥ 4 these are 3-connected, so their embedding is unique by Whitney).
  So a(n) is the number of isomorphism classes of non-Hamiltonian maximal planar graphs on
  n vertices; this reading gives a(11) = 1 (the Goldner–Harary graph, as in the EXAMPLE).
* Mathlib has no planarity, so it is defined combinatorially: a connected graph is planar iff
  it has a rotation system of genus 0 (Heffter–Edmonds–Ringel). A rotation system is a
  permutation `σ` of the darts that fixes the tail of each dart and cyclically permutes the darts
  leaving each vertex; its faces are the orbits of `d ↦ σ (reverse d)`, and it has genus 0 iff
  V - E + F = 2. (This definition is only used for connected graphs with at least one edge.)
* A graph is maximal planar if it is connected, planar, and adding any missing edge makes it
  non-planar (a maximal planar graph on n ≥ 3 vertices is connected anyway).
* Hamiltonian is Mathlib's `SimpleGraph.IsHamiltonian`.
-/

namespace OMA.S_oeis_a007030

open SimpleGraph

variable {n : ℕ}

/-- A rotation system of `G`: a permutation of the darts preserving the tail of each dart and
acting as a single cycle on the darts leaving each vertex. -/
def IsRotationSystem (G : SimpleGraph (Fin n)) (σ : Equiv.Perm G.Dart) : Prop :=
  (∀ d, (σ d).toProd.1 = d.toProd.1) ∧ ∀ v, σ.IsCycleOn {d : G.Dart | d.toProd.1 = v}

/-- The face permutation of a rotation system: traverse the dart backwards, then rotate. -/
def facePerm (G : SimpleGraph (Fin n)) (σ : Equiv.Perm G.Dart) : Equiv.Perm G.Dart :=
  (Equiv.mk Dart.symm Dart.symm Dart.symm_symm Dart.symm_symm).trans σ

/-- A connected graph is planar iff it has a rotation system satisfying Euler's formula
`V - E + F = 2`, where `F` is the number of orbits of the face permutation. -/
def IsPlanar (G : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm G.Dart, IsRotationSystem G σ ∧
    (n : ℤ) - Nat.card G.edgeSet + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (facePerm G σ)))
      = 2

/-- Maximal planar graphs: connected, planar, and no edge can be added keeping planarity. -/
def IsMaximalPlanar (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ IsPlanar G ∧ ∀ u v, u ≠ v → ¬ G.Adj u v → ¬ IsPlanar (G ⊔ edge u v)

/-- Non-Hamiltonian maximal planar graphs on `n` labelled vertices. -/
def NonHam (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // IsMaximalPlanar G ∧ ¬ G.IsHamiltonian}

/-- A007030: the number of non-Hamiltonian simplicial polyhedra with `n` nodes, i.e. of
isomorphism classes of non-Hamiltonian maximal planar graphs on `n` vertices. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card (Quot (fun G H : NonHam n => Nonempty (G.1 ≃g H.1)))

theorem main : a 18 = 1879665 := by
  sorry

end OMA.S_oeis_a007030

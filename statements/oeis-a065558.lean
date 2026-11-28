import Mathlib

/-!
# A065558: Maximal degree of an irreducible representation of GL(2, Z/nZ).

Source: https://oeis.org/A065558
Credit: @Solfanbtc

Let `G_n` be the group of invertible `2 × 2` matrices mod `n` (`n ≥ 1`; its order is A000252).
`a(n)` is the maximal degree of an irreducible (complex) representation of `G_n`.
Data: `1, 2, 4, 6, 6, 8, 8, 12, 12, 12, 12, 24, ...`.

Conjecture (Ralf Stephan, Mar 26 2004, in the entry): `a(2n) = 2 ψ(n)` for `n ≥ 1`, where
`ψ = A001615` is Dedekind's psi function, `ψ(n) = n ∏_{p | n} (1 + 1/p)`.

A python3 check: `2 ψ(n)` equals the listed `a(2n)` for all `1 ≤ n ≤ 12`.

Conventions: `G_n` is Mathlib's `GL (Fin 2) (ZMod n)`. A representation is a finite-dimensional
complex vector space `V` with `ρ : Representation ℂ G_n V`; it is irreducible when `V ≠ 0` and
its only `G_n`-stable subspaces are `⊥` and `⊤`. The vector spaces range over `Type` (every
finite-dimensional complex representation is isomorphic to one on `Fin d → ℂ`, so this loses
nothing). `ψ(n) = ∏_{p^k ∥ n} p^(k-1) (p+1)`.
-/

namespace OMA.S_oeis_a065558

/-- `ρ` is irreducible: `V ≠ 0` and the only invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The degrees of the finite-dimensional irreducible complex representations of `G`. -/
def irrDegrees (G : Type) [Group G] : Set ℕ :=
  {d | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), IsIrreducible ρ ∧ Module.finrank ℂ V = d}

/-- `a(n)`: the maximal degree of an irreducible representation of `GL(2, ℤ/nℤ)`. -/
noncomputable def a (n : ℕ) : ℕ := sSup (irrDegrees (GL (Fin 2) (ZMod n)))

/-- Dedekind's psi function `ψ(n) = n ∏_{p | n} (1 + 1/p)`. -/
def psi (n : ℕ) : ℕ := n.factorization.prod fun p k => p ^ (k - 1) * (p + 1)

/-- Stephan's conjecture: `a(2n) = 2 ψ(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (2 * n) = 2 * psi n := by
  sorry

end OMA.S_oeis_a065558

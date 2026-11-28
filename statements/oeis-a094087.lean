import Mathlib

/-!
# A094087: Domination number of the Cartesian product of two n-cycles.

Source: https://oeis.org/A094087
Credit: @Solfanbtc

Conjecture (Richard Bean, Sep 08 2006, in the entry): a(5n-1) = 5n^2 - n and
a(5n+1) = 5n^2 + 4n - 1 for n >= 1. (Assadian proves that both formulas are upper bounds,
per Andrei Zabolotskii's note in the entry; equality remains conjectural.)

Conventions.
* a(m) = γ(C_m □ C_m), the domination number of the Cartesian (box) product of two m-cycles,
  with Mathlib's `SimpleGraph.cycleGraph m` and `SimpleGraph.boxProd`. A set D of vertices is
  dominating if every vertex is in D or adjacent to a vertex of D; γ is the least size of a
  dominating set (a finite graph always has one, its whole vertex set).
* Only m = 5n ± 1 ≥ 4 occur, so the cycles are genuine cycles. The formulas agree with all
  listed terms: a(4) = 4, a(6) = 8, a(9) = 18, a(11) = 27, a(14) = 42, a(16) = 56,
  a(19) = 76, a(21) = 95, a(24) = 120, a(26) = 144, a(29) = 174.
-/

namespace OMA.S_oeis_a094087

/-- D dominates G. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- Domination number of a finite graph. -/
noncomputable def domNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, D.card = k ∧ IsDominating G D}

/-- The torus grid graph C_m □ C_m. -/
def torus (m : ℕ) : SimpleGraph (Fin m × Fin m) :=
  SimpleGraph.boxProd (SimpleGraph.cycleGraph m) (SimpleGraph.cycleGraph m)

theorem main : ∀ n : ℕ, 1 ≤ n →
    domNum (torus (5 * n - 1)) = 5 * n ^ 2 - n ∧
    domNum (torus (5 * n + 1)) = 5 * n ^ 2 + 4 * n - 1 := by
  sorry

end OMA.S_oeis_a094087

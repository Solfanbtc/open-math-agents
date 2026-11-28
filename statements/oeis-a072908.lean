import Mathlib

/-!
# A072908: Decimal expansion of the solution of equation log(2)-X*2^(-r)-exp(-X*r/(2^r-1)) = 0 for r = 4 . Solution is 9.96955802...

Source: https://oeis.org/A072908
Credit: @Solfanbtc

The constant `c = 9.96955802…` is the solution in `(9, 10)` of
`log 2 - X * 2^(-4) - exp(-X * 4 / (2^4 - 1)) = 0` (the PARI program solves on `[9, 10]`).
The function is strictly concave, negative at `0` and at `10` and positive at `9`, so this root
is unique in `(9, 10)` (checked with python3: `c ≈ 9.969558028877724`).

Conjecture (O. Dubois, 1993; see O. Dubois and J. Carlier, Probabilistic approach to the
satisfiability problem, Theoret. Comput. Sci. 81 (1991) 65-75): `c` is the exact value of the
satisfiability threshold for random 4-SAT (4-clause CNF formulas).

Model: a random 4-CNF formula on `n` variables with `m` clauses is a sequence of `m` clauses,
drawn independently and uniformly, each clause made of 4 literals on 4 distinct variables
(a literal `(v, s)` is satisfied by `a : Fin n → Bool` when `a v = s`). Stated with ordered
tuples of literals, the uniform distribution on clauses is the same as on unordered ones. "`c`
is the threshold" means: for every ratio `α < c`, a random formula with `m = ⌊α n⌋` clauses is
satisfiable with probability tending to 1 as `n → ∞`, and for every `α > c` with probability
tending to 0.

Status: open. The existence of a sharp threshold constant for `k = 4` is itself unproved (Ding,
Sly and Sun proved it only for large `k`), and the non-rigorous cavity-method prediction for
`k = 4` (Mertens, Mézard and Zecchina, 2006) is about `9.931`, which differs from this constant.
So this conjecture is widely believed to be false.
-/

namespace OMA.S_oeis_a072908

open Filter Topology Real

/-- A 4-clause on `n` variables: 4 literals on pairwise distinct variables. -/
abbrev Clause (n : ℕ) := {C : Fin 4 → Fin n × Bool // Function.Injective (fun i => (C i).1)}

/-- A formula (sequence of clauses) is satisfiable when some assignment satisfies a literal of
every clause. -/
def Satisfiable {n m : ℕ} (F : Fin m → Clause n) : Prop :=
  ∃ a : Fin n → Bool, ∀ j : Fin m, ∃ i : Fin 4, a ((F j).1 i).1 = ((F j).1 i).2

open Classical in
/-- Probability that a uniformly random 4-CNF formula with `m` clauses on `n` variables is
satisfiable. -/
noncomputable def probSat (n m : ℕ) : ℝ :=
  ((Finset.univ.filter (fun F : Fin m → Clause n => Satisfiable F)).card : ℝ) /
    (Fintype.card (Fin m → Clause n) : ℝ)

theorem main :
    ∃ c : ℝ, 9 < c ∧ c < 10 ∧
      log 2 - c * (2 : ℝ) ^ (-(4 : ℝ)) - exp (-c * 4 / ((2 : ℝ) ^ 4 - 1)) = 0 ∧
      (∀ α : ℝ, α < c →
        Tendsto (fun n : ℕ => probSat n ⌊α * n⌋₊) atTop (𝓝 1)) ∧
      (∀ α : ℝ, c < α →
        Tendsto (fun n : ℕ => probSat n ⌊α * n⌋₊) atTop (𝓝 0)) := by
  sorry

end OMA.S_oeis_a072908

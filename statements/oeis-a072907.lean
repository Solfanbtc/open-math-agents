import Mathlib

/-!
# A072907: Decimal expansion of the solution of equation log(2) - X/8 - exp(-3X/7) = 0 (4.251844....).

Source: https://oeis.org/A072907
Credit: @Solfanbtc

Claim (OEIS entry, %C): this constant `α = 4.251844…` was conjectured (Olivier Dubois, 1993) to be
the exact value of the 3-clause threshold in the satisfiability problem, i.e. of the threshold of
random 3-SAT: for clause density `c < α` a random 3-CNF formula with `n` variables and `⌊c n⌋`
clauses is satisfiable with probability tending to `1`, and for `c > α` with probability tending to
`0`. (The conjecture is historical; later numerical and statistical-physics work places the
threshold near 4.267, so it is widely believed false, but it has not been refuted by a proof.)

Conventions:
* `α` is the root of `log 2 - X/8 - exp(-3X/7) = 0` in `(4, 5)`. The function has exactly two
  positive roots, `≈ 1.724` and `≈ 4.2518` (checked numerically); the entry's constant is the
  larger one, the unique root in `(4, 5)` (sign change: `g(4) > 0 > g(5)`).
* Random 3-SAT model (the standard one): a formula with `n` variables and `m` clauses is a map
  `I : Fin m → Fin 3 → Fin n × Bool` (clause `j` is the disjunction of the literals `I j k`,
  where `(v, s)` is satisfied by `a : Fin n → Bool` when `a v = s`), each clause having three
  distinct variables; all such formulas are equally likely (clauses independent, uniform, with
  replacement). The probability of satisfiability is the proportion of satisfiable formulas.
-/

namespace OMA.S_oeis_a072907

open Filter Topology

/-- Formulas with `n` variables and `m` clauses, each clause on three distinct variables. -/
def Formula (n m : ℕ) : Type :=
  {I : Fin m → Fin 3 → Fin n × Bool // ∀ j, Function.Injective (fun k => (I j k).1)}

noncomputable instance (n m : ℕ) : Fintype (Formula n m) := by
  classical
  unfold Formula
  infer_instance

/-- `I` is satisfiable: some assignment satisfies a literal of every clause. -/
def Satisfiable {n m : ℕ} (I : Formula n m) : Prop :=
  ∃ a : Fin n → Bool, ∀ j : Fin m, ∃ k : Fin 3, a (I.1 j k).1 = (I.1 j k).2

open Classical in
/-- The probability that a uniformly random formula with `n` variables and `m` clauses is
satisfiable. -/
noncomputable def probSat (n m : ℕ) : ℝ :=
  ((Finset.univ.filter (fun I : Formula n m => Satisfiable I)).card : ℝ) /
    (Fintype.card (Formula n m) : ℝ)

/-- Dubois' conjecture: the random 3-SAT threshold is the root `α ∈ (4, 5)` of
`log 2 - X/8 - exp(-3X/7) = 0`. -/
theorem main : ∀ α : ℝ, 4 < α → α < 5 → Real.log 2 - α / 8 - Real.exp (-3 * α / 7) = 0 →
    ∀ c : ℝ, 0 < c →
      (c < α → Tendsto (fun n : ℕ => probSat n ⌊c * n⌋₊) atTop (𝓝 1)) ∧
      (α < c → Tendsto (fun n : ℕ => probSat n ⌊c * n⌋₊) atTop (𝓝 0)) := by
  sorry

end OMA.S_oeis_a072907

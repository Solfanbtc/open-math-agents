import Mathlib

/-!
# A094777: asymptotics of the number of legal Go positions on an n × n board

Source: https://oeis.org/A094777
Credit: @Solfanbtc

A094777 (offset 1): the number of legal positions in Go played on an `n × n` grid: assignments of
empty / black / white to the `n^2` points such that every group (maximal set of same-coloured
stones connected through orthogonally adjacent points) has at least one liberty (an empty point
adjacent to one of its stones). Data 1, 57, 12675, 24318165, …

The entry (C. R. Greathouse IV, citing Tromp and Farnebäck): "Tromp & Farnebäck prove that
a(n) = (1 + o(1)) * L^(n^2), and conjecture that a(n) ~ A * B^(2n) * L^(n^2) * (1 + O(n*p^n)) for
some constants A, B, L, and p < 1." (In their paper the proved statement is
`a(n)^(1/n^2) → L`.) `main` states the conjecture: there are constants `A, B, L > 0` and
`0 ≤ p < 1` with `a(n) / (A B^(2n) L^(n^2)) - 1 = O(n p^n)`.

Definitions. A board is `Fin n × Fin n → Fin 3` (`0` empty, `1` black, `2` white); two points
are adjacent if they differ by one in exactly one coordinate. A stone `s` is safe if some point
reachable from `s` through adjacent stones of its colour has an empty neighbour; a position is
legal if every stone is safe. Checked with python3: 1, 57, 12675 legal positions for
`n = 1, 2, 3`.
-/

namespace OMA.S_oeis_a094777

/-- Orthogonal adjacency on the `n × n` grid. -/
def Adj {n : ℕ} (u v : Fin n × Fin n) : Prop :=
  (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)) ∨
  (u.2 = v.2 ∧ ((u.1 : ℕ) + 1 = v.1 ∨ (v.1 : ℕ) + 1 = u.1))

/-- A legal position: every group of stones has a liberty. -/
def Legal {n : ℕ} (b : Fin n × Fin n → Fin 3) : Prop :=
  ∀ s, b s ≠ 0 → ∃ u e, Relation.ReflTransGen (fun x y => Adj x y ∧ b y = b s) s u ∧
    Adj u e ∧ b e = 0

/-- A094777: the number of legal positions on the `n × n` board. -/
noncomputable def a (n : ℕ) : ℕ := {b : Fin n × Fin n → Fin 3 | Legal b}.ncard

open Filter Asymptotics in
/-- Tromp and Farnebäck's conjecture. -/
theorem main : ∃ A B L p : ℝ, 0 < A ∧ 0 < B ∧ 0 < L ∧ 0 ≤ p ∧ p < 1 ∧
    (fun n : ℕ => (a n : ℝ) / (A * B ^ (2 * n) * L ^ (n ^ 2)) - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ) * p ^ n) := by
  sorry

end OMA.S_oeis_a094777

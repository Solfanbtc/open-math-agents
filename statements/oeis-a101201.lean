import Mathlib

/-!
# A101201: Maximal number of kings in the toroidal king's graph on an n X n board such that each king is attacking no more than four other kings.

Source: https://oeis.org/A101201
Credit: @Solfanbtc

Conjecture (entry formula): a(n) is approximately 3n^2/5.
The entry also says that the densities a(n)/n^2 have a limit (the supremum of the sequence) and
that a(n) ≤ 0.608956 n^2. Reference: E. J. Ionascu, D. Pritkin and S. E. Wright,
k-Dependence and Domination in Kings Graphs, Amer. Math. Monthly 115 (2008), 820-836.

Reading. "approximately 3n^2/5" is taken in the sense given by the entry's own comment about
the limit of the densities: a(n)/n^2 → 3/5. (Any toroidal or non-toroidal boundary convention
changes a(n) by O(n) only, so the limit does not depend on it.)

Definition. Cells are `(i, j)` with `i, j < n`. A king on `p` attacks along its 8 king moves on
the torus, `p + (dx, dy) mod n` with `(dx, dy) ∈ {-1,0,1}^2 \ {(0,0)}`; the number of kings it
attacks is the number of these 8 moves that land on an occupied cell (counted with
multiplicity, which only matters for n ≤ 2). This reproduces the data a(1) = 0, a(2) = 2
(the entry's example), a(3) = 5, a(4) = 9 (python3 brute force); on a 1 × 1 torus a king
attacks its own square 8 times, whence a(1) = 0.
In the encoding below the offset `d ∈ {0,1,2}` stands for `d - 1`.
-/

namespace OMA.S_oeis_a101201

/-- The 8 king moves, as offsets `(dx + 1, dy + 1)`. -/
def moves : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- Number of king moves from `p` on the `n × n` torus landing in `S`. -/
def attacks (n : ℕ) (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  (moves.filter fun d => ((p.1 + d.1 + n - 1) % n, (p.2 + d.2 + n - 1) % n) ∈ S).length

/-- `S` is a placement of kings on the `n × n` torus, each attacking at most four kings. -/
def Valid (n : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ Finset.range n ×ˢ Finset.range n ∧ ∀ p ∈ S, attacks n S p ≤ 4

/-- A101201(n). -/
noncomputable def a (n : ℕ) : ℕ := sSup {k : ℕ | ∃ S : Finset (ℕ × ℕ), Valid n S ∧ S.card = k}

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds (3 / 5)) := by
  sorry

end OMA.S_oeis_a101201

import Mathlib

/-!
# A127823: Weighted Catalan numbers: number of combinatorial types of plane Morse links of order n.

Source: https://oeis.org/A127823
Credit: @Solfanbtc

Claim (entry comment, a conjecture of Alexander Postnikov, settled by A. Postnikov and B. Sagan,
"What power of two divides a weighted Catalan number?", J. Combin. Theory Ser. A 114 (2007)):
a(n) has the same number of factors of 2 as the Catalan number C_n (A000108).

Definitions (quoted in the entry from Postnikov–Sagan). For weights b = (b_0, b_1, ...), a Dyck
path P of length 2n has weight b_(h_1) ⋯ b_(h_n), where h_i is the height of the i-th ascent
(the height at which that up step starts); C_n^b = Sum_P wt(P). A127823 is the case
b_i = (2i+1)^2. Dyck paths are words in U (`true`) and D (`false`) of length 2n whose prefixes
never have more D than U and which end at height 0. `#eval` reproduces the data
1, 1, 10, 325, 22150, 2586250 for n ≤ 5 (e.g. n = 2: UUDD has weight 1·9, UDUD weight 1·1).

Statement: for every n, the 2-adic valuations of a(n) and of C_n agree.
-/

namespace OMA.S_oeis_a127823

/-- Height after the first `i` steps (`true` = up). -/
def height (w : List Bool) (i : ℕ) : ℤ := ((w.take i).map fun s => if s then (1 : ℤ) else -1).sum

/-- `w` is a Dyck path. -/
def IsDyck (w : List Bool) : Prop :=
  (∀ i ∈ Finset.range (w.length + 1), 0 ≤ height w i) ∧ height w w.length = 0

instance : DecidablePred IsDyck := fun w => by unfold IsDyck; infer_instance

/-- Weight of a path: product of (2h+1)^2 over the up steps, h the height where the step starts. -/
def weight (w : List Bool) : ℕ :=
  ((List.range w.length).filter fun i => w.getD i false).foldl
    (fun acc i => acc * (2 * (height w i).toNat + 1) ^ 2) 1

/-- A127823(n). -/
def a (n : ℕ) : ℕ :=
  ∑ f ∈ (Finset.univ : Finset (Fin (2 * n) → Bool)).filter (fun f => IsDyck (List.ofFn f)),
    weight (List.ofFn f)

theorem main : ∀ n : ℕ, padicValNat 2 (a n) = padicValNat 2 (catalan n) := by
  sorry

end OMA.S_oeis_a127823

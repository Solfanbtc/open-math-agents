import Mathlib

/-!
# A100038: Positions of occurrences of the natural numbers as third subsequence in A100035.

Source: https://oeis.org/A100038
Credit: @Solfanbtc

A100035 (offset 1): `s(1) = 1`, and `s(k+1)` is chosen among the numbers `x ≥ 1` that have not yet
occurred as a neighbor of a term equal to `s(k)` (i.e. no earlier adjacent pair of terms is
`{s(k), x}`): it is the greatest such `x < s(k)` or, if there is none, the smallest such `x > s(k)`.
It begins 1, 2, 3, 1, 4, 3, 5, 4, 2, 5, 1, 6, 5, 7, ...

A100038 (offset 1), as characterized in the entry's comment: `a(1) = 11` is the position of the third
`1` in A100035 (the start of the third subsequence 1, 2, 3, ...), and for `n > 1`, `a(n)` is the
first position after `a(n-1)` where A100035 takes the value `n`. It begins 11, 20, 33, 50, 71, ...

Conjecture (R. Stephan, 2007): `a(n) = 2n² + 3n + 6` for all `n ≥ 1`.

python3: the simulated A100035 matches its data, the comment's characterization matches both the
data of A100038 and the greedy third disjoint subsequence of the example, and the formula holds for
`1 ≤ n ≤ 172`.
-/

namespace OMA.S_oeis_a100038

/-- Whether `v` and `x` already occur as adjacent terms (in either order) of the list `l`. -/
def adjacent (l : List ℕ) (v x : ℕ) : Bool :=
  (l.zip l.tail).any (fun p => (p.1 == v && p.2 == x) || (p.1 == x && p.2 == v))

/-- The term following `l` (whose last term is `v`): the greatest `x` with `1 ≤ x < v` not yet
adjacent to `v`, otherwise the smallest `x > v` not yet adjacent to `v`. At most `l.length` values
are adjacent to `v`, so the second search, up to `v + l.length + 1`, always succeeds. -/
def nextTerm (l : List ℕ) (v : ℕ) : ℕ :=
  match ((List.range v).reverse.filter (fun x => 0 < x && !adjacent l v x)).head? with
  | some x => x
  | none => ((List.range (v + l.length + 2)).filter (fun x => v < x && !adjacent l v x)).headD 0

/-- The first `k + 1` terms of A100035. -/
def init : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => let l := init k; l ++ [nextTerm l (l.getLastD 1)]

/-- A100035, offset 1 (`s 0 = 0` is a placeholder). -/
def s : ℕ → ℕ
  | 0 => 0
  | k + 1 => (init k).getLastD 0

/-- A100038, offset 1 (`a 0 = 0` is a placeholder): `a 1` is the position of the third `1` in
A100035, and `a (n + 1)` is the least position after `a n` holding the value `n + 1`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth (fun m => s m = 1) 2
  | n + 2 => sInf {m | a (n + 1) < m ∧ s m = n + 2}

theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * n ^ 2 + 3 * n + 6 := by
  sorry

end OMA.S_oeis_a100038

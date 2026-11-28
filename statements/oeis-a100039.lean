import Mathlib

/-!
# A100039: Positions of occurrences of the natural numbers as fourth subsequence in A100035.

Source: https://oeis.org/A100039
Credit: @Solfanbtc

Conjecture (Ralf Stephan, May 15 2007): a(n) = 2n^2 + 7n + 13.

The sequence A100035 (offset 1): a(1) = 1, and a(k+1) is a number that has not occurred
earlier as a neighbour of a term equal to a(k): the greatest such number < a(k) or, if none
exists, the smallest such number > a(k). Here "x has occurred as a neighbour of a term equal to
v" means that `x, v` or `v, x` are two consecutive terms among a(1), ..., a(k); candidates are
positive integers different from a(k). This reproduces all 88 data terms of A100035
(1, 2, 3, 1, 4, 3, 5, 4, 2, 5, 1, ...; `#eval` and python3).

A100039, the "fourth subsequence" (the fourth row of the example of A100035): it starts at the
fourth occurrence of 1 in A100035 (position 22), and, as in the comment of A100039 ("n>1:
A100035(a(n))=n and A100035(m)<>n for a(n-1)<=m<a(n)"), a(n) for n > 1 is the first position
after a(n-1) where A100035 takes the value n. This reproduces the 47 data terms 22, 35, 52,
73, 98, ... (python3), and the conjectured formula holds for n < 300 (python3).
-/

namespace OMA.S_oeis_a100039

/-- The values that occur next to a term equal to `v` in the list `L`. -/
def nbrs (L : List ℕ) (v : ℕ) : List ℕ :=
  (L.zip L.tail).flatMap fun p =>
    (if p.1 = v then [p.2] else []) ++ (if p.2 = v then [p.1] else [])

/-- The next term of A100035 after the terms `L`. -/
def next (L : List ℕ) : ℕ :=
  let v := L.getLastD 0
  let N := nbrs L v
  match ((List.range v).filter fun x => 0 < x ∧ x ∉ N).getLast? with
  | some x => x
  | none => ((List.range (v + N.length + 2)).filter fun x => v < x ∧ x ∉ N).headD 0

/-- `terms n = [A100035(1), ..., A100035(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) => let L := terms (n + 1); L ++ [next L]

/-- A100035(k), offset 1. -/
def A (k : ℕ) : ℕ := (terms k).getD (k - 1) 0

/-- A100039(n), offset 1: `a 1` is the position of the fourth occurrence of 1 in A100035,
and `a (n+1)` is the first position after `a n` where A100035 equals `n + 1`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth (fun k => 1 ≤ k ∧ A k = 1) 3
  | (n + 2) => sInf {m : ℕ | a (n + 1) < m ∧ A m = n + 2}

theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * n ^ 2 + 7 * n + 13 := by
  sorry

end OMA.S_oeis_a100039

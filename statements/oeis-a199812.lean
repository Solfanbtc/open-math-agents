import Mathlib

/-!
# A199812: Number of distinct values taken by w^w^...^w (with n w's and parentheses inserted in all possible ways) where w is the first transfinite ordinal omega.

Source: https://oeis.org/A199812 (and https://oeis.org/A255170, https://oeis.org/A000081)
Credit: @Solfanbtc

A parenthesization of `w^w^...^w` with `n` letters is a full binary tree with `n` leaves; a leaf
evaluates to `ω` and a node `(a, b)` to `(value a) ^ (value b)` (ordinal exponentiation).
`A199812(n)` (`n ≥ 1`) is the number of distinct ordinals obtained this way.

A255170 is `a(n) = 1 - n + Sum_{k=1..n} A000081(k)`, where A000081(k) is the number of
unlabeled rooted trees with `k` nodes, computed here by its standard recurrence
`t(1) = 1`, `t(m) = (1/(m-1)) Sum_{j=1..m-1} (Sum_{d | j} d t(d)) t(m-j)`.
(Since every `t(k) ≥ 1`, the natural-number subtraction below never truncates.)

Conjecture (A199812 and A255170 comments): A199812 is identical to A255170, i.e.
`A199812(n) = A255170(n)` for every `n ≥ 1`. The 20 known terms of A199812 agree.

(The entry also conjectures `a(n) ~ c d^n n^(-3/2)` with `c = 0.664861…`, `d = A051491`; that
asymptotic follows from the identity stated here and the known asymptotics of A000081.)
-/

namespace OMA.S_oeis_a199812

open Ordinal

/-- Parenthesizations of `w^w^...^w`: full binary trees. -/
inductive PTree
  | leaf : PTree
  | node : PTree → PTree → PTree

/-- Number of letters `w` (leaves). -/
def PTree.leaves : PTree → ℕ
  | .leaf => 1
  | .node a b => a.leaves + b.leaves

/-- The ordinal value, with every letter equal to `ω`. -/
noncomputable def PTree.value : PTree → Ordinal.{0}
  | .leaf => ω
  | .node a b => a.value ^ b.value

/-- A199812(n): the number of distinct values of the parenthesizations with `n` letters. -/
noncomputable def a199812 (n : ℕ) : ℕ :=
  Set.ncard {o : Ordinal.{0} | ∃ t : PTree, t.leaves = n ∧ t.value = o}

/-- `rootedList n = [t(1), …, t(n)]`, with `t` = A000081 given by its recurrence. -/
def rootedList : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let L := rootedList n
    let t := fun k => L.getD (k - 1) 0
    L ++ [if n = 0 then 1 else
      (∑ j ∈ Finset.Icc 1 n, (∑ d ∈ j.divisors, d * t d) * t (n + 1 - j)) / n]

/-- A000081(k) for `k ≥ 1`: the number of unlabeled rooted trees with `k` nodes. -/
def a000081 (k : ℕ) : ℕ := (rootedList k).getD (k - 1) 0

/-- A255170(n) = 1 - n + Sum_{k=1..n} A000081(k). -/
def a255170 (n : ℕ) : ℕ := (1 + ∑ k ∈ Finset.Icc 1 n, a000081 k) - n

/-- Conjecture (OEIS A199812 / A255170): the two sequences coincide for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a199812 n = a255170 n := by
  sorry

end OMA.S_oeis_a199812

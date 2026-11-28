import Mathlib

/-!
# A007857: Number of independent sets in rooted plane trees on n nodes.

Source: https://oeis.org/A007857
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Nov 26 2012, in the entry): for n ≥ 4,
`2n(n-1)(2n-3)(44n-69) a(n) + (n-1)(176n^3 - 9591n^2 + 38703n - 40640) a(n-1)
 + (-17479n^4 + 218005n^3 - 959616n^2 + 1797890n - 1221920) a(n-2)
 + 6(3n-10)(2n-7)(3n-11)(517n-1198) a(n-3) = 0`.

Status: PROVED by Petros Hadjicostas (Aug 06 2020, comment in the entry), from Paul Barry's
formula a(n+1) = A007226(n) - A000108(n), by checking the recurrence separately on both terms.

Conventions.
* a(n) is the total, over all rooted plane (ordered) trees T with n nodes, of the number of
  NONEMPTY independent sets of T (sets of nodes with no parent-child pair). The data force
  "nonempty": a(1) = 1 for the one-node tree, and a brute-force count including the empty set
  gives 2,3,10,42,198,... = data + Catalan(n-1); excluding it gives 1,2,8,37,184,959,5172,28641,
  162008,932503, matching the data.
* Plane trees are `PlaneTree.node cs` with an ordered list of subtrees. For a tree,
  `indep T = (o, i)` counts all independent sets with the root out (`o`) and with the root in
  (`i`): `o = ∏ (o_c + i_c)`, `i = ∏ o_c` over the children `c` (the standard recursion: a set
  is independent iff its restriction to each subtree is, and the root is not chosen together
  with a child). The number of nonempty independent sets is `o + i - 1`.
* There are finitely many plane trees with n nodes (Catalan(n-1)), so the `finsum` below is
  the finite sum over them.
* The recurrence is checked numerically on all 22 listed terms (n = 4..22).
-/

namespace OMA.S_oeis_a007857

/-- Rooted plane trees: a root with an ordered list of subtrees. -/
inductive PlaneTree where
  | node : List PlaneTree → PlaneTree

namespace PlaneTree

/-- Number of nodes. -/
def size : PlaneTree → ℕ
  | node cs => 1 + (cs.attach.map fun c => size c.1).sum
decreasing_by have := List.sizeOf_lt_of_mem c.2; simp_wf; omega

/-- `(number of independent sets not containing the root, number containing the root)`. -/
def indep : PlaneTree → ℕ × ℕ
  | node cs =>
    ((cs.attach.map fun c => (indep c.1).1 + (indep c.1).2).prod,
     (cs.attach.map fun c => (indep c.1).1).prod)
decreasing_by all_goals (have := List.sizeOf_lt_of_mem c.2; simp_wf; omega)

end PlaneTree

/-- A007857: total number of nonempty independent sets over the plane trees with `n` nodes. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ᶠ (T : PlaneTree) (_ : T.size = n), ((T.indep).1 + (T.indep).2 - 1)

theorem main : ∀ n : ℕ, 4 ≤ n →
    2 * (n : ℤ) * (n - 1) * (2 * n - 3) * (44 * n - 69) * a n
      + ((n : ℤ) - 1) * (176 * n ^ 3 - 9591 * n ^ 2 + 38703 * n - 40640) * a (n - 1)
      + (-17479 * (n : ℤ) ^ 4 + 218005 * n ^ 3 - 959616 * n ^ 2 + 1797890 * n - 1221920)
          * a (n - 2)
      + 6 * (3 * (n : ℤ) - 10) * (2 * n - 7) * (3 * n - 11) * (517 * n - 1198) * a (n - 3)
      = 0 := by
  sorry

end OMA.S_oeis_a007857

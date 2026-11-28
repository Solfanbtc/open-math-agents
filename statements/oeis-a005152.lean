import Mathlib

/-!
# A005152: Rotation distance between binary trees on n nodes.

Source: https://oeis.org/A005152
Credit: @Solfanbtc

$a(n)$ is the maximum, over all pairs of binary trees with $n$ (internal) nodes, of the
rotation distance between them, i.e. the diameter of the rotation graph on binary trees
with $n$ nodes (equivalently, of the 1-skeleton of the $(n-1)$-dimensional associahedron).

Conjecture (Sleator, Tarjan and Thurston, as quoted in the OEIS entry): $a(n) = 2n - 6$
for all $n \ge 11$. (Pournin, "The diameter of associahedra", Adv. Math. 2014, proved that
the $d$-dimensional associahedron has diameter $2d - 4$ for $d > 9$, which is this claim.)

Conventions.
* Binary trees with $n$ nodes are `BinaryTree Unit` with `numNodes = n` (Mathlib's `BinaryTree`:
  `nil` is the empty tree, `node () l r` an internal node).
* A rotation is the local move `node (node x y) z ↔ node x (node y z)` applied at any node
  (both directions: right and left rotation). Rotations preserve the number of nodes.
* The rotation distance is the graph distance in the simple graph whose vertices are the
  trees with $n$ nodes and whose edges are single rotations; $a(n)$ is its diameter
  `SimpleGraph.diam` (the graph is finite and connected).
* A brute-force BFS (python) gives $a(1), \dots, a(8) = 0, 1, 2, 4, 5, 7, 9, 11$, matching
  the OEIS data.
-/

namespace OMA.S_oeis_a005152

/-- One rotation, in one direction: right rotation at the root
`node (node x y) z ↦ node x (node y z)`, or at a node inside the tree. -/
inductive RotStep : BinaryTree Unit → BinaryTree Unit → Prop
  | root (x y z : BinaryTree Unit) :
      RotStep (BinaryTree.node () (BinaryTree.node () x y) z)
        (BinaryTree.node () x (BinaryTree.node () y z))
  | left {l l' : BinaryTree Unit} (r : BinaryTree Unit) :
      RotStep l l' → RotStep (BinaryTree.node () l r) (BinaryTree.node () l' r)
  | right (l : BinaryTree Unit) {r r' : BinaryTree Unit} :
      RotStep r r' → RotStep (BinaryTree.node () l r) (BinaryTree.node () l r')

/-- The rotation graph on binary trees with `n` nodes: two trees are adjacent iff one is
obtained from the other by a single (right or left) rotation. -/
def rotationGraph (n : ℕ) : SimpleGraph {t : BinaryTree Unit // t.numNodes = n} :=
  SimpleGraph.fromRel fun s t => RotStep s.1 t.1

/-- $a(n)$: the maximum rotation distance between two binary trees with `n` nodes. -/
noncomputable def a (n : ℕ) : ℕ := (rotationGraph n).diam

theorem main : ∀ n ≥ 11, a n = 2 * n - 6 := by
  sorry

end OMA.S_oeis_a005152

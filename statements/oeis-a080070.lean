import Mathlib

/-!
# A080070: Decimal encoding of parenthesizations produced by simple iteration starting from empty parentheses and where each successive parenthesization is obtained from the previous by reflecting it as a general tree/parenthesization, then adding an extra stem below the root and then reflecting the underlying binary tree.

Source: https://oeis.org/A080070
Credit: @Solfanbtc

Conjecture (Antti Karttunen, OEIS A080070): only the terms in positions 0, 1, 2 and 4 are
symmetric, i.e. A057164(A080068(n)) = A080068(n) only when n is one of {0, 1, 2, 4}
(checked by the author up to n = 404631).

Model (standard Karttunen correspondence, as in A014486 and the example of the entry):
* a binary tree (`Tree Unit`) t is a parenthesization `word t` (a Dyck word, `true` = "(",
  `false` = ")"): word(leaf) = empty, word(node l r) = "(" word(l) ")" word(r);
  this is the general tree / forest whose root's subtrees are read from the word;
* A057164, reflection of the general tree, acts on words as reverse-and-swap-parentheses
  (`reflectWord`); a tree is symmetric when its word is fixed by it;
* A057548, adding a stem below the root, sends the forest of t to the single tree with that forest
  as children: t ↦ node t leaf;
* A057163, reflection of the underlying binary tree: `Tree.mirror`-like swap of l and r at every
  node (`mirrorBin`);
* `parse` reads a Dyck word back as a binary tree (fuel = length + 1 is enough).
The iteration starts from the empty parenthesization (the leaf). Checked numerically: the words of
terms 0..7 are 0, 10, 1010, 101100, 10110010, 1011100100, 101100110100, 10111001001100 as listed,
and among the first 400 terms the symmetric ones are exactly at positions 0, 1, 2, 4.
-/

namespace OMA.S_oeis_a080070

/-- The parenthesization of a binary tree. -/
def word : Tree Unit → List Bool
  | .nil => []
  | .node _ l r => true :: word l ++ false :: word r

/-- Reflection of the general tree, on words: reverse and swap the parentheses (A057164). -/
def reflectWord (w : List Bool) : List Bool := (w.reverse).map not

/-- Reflection of the underlying binary tree (A057163). -/
def mirrorBin : Tree Unit → Tree Unit
  | .nil => .nil
  | .node u l r => .node u (mirrorBin r) (mirrorBin l)

/-- Reads a forest from a word, stopping at an unmatched `false` or at the end. -/
def parseAux : ℕ → List Bool → Tree Unit × List Bool
  | 0, w => (.nil, w)
  | _ + 1, [] => (.nil, [])
  | _ + 1, false :: w => (.nil, false :: w)
  | fuel + 1, true :: w =>
    match parseAux fuel w with
    | (l, false :: w') =>
      match parseAux fuel w' with
      | (r, w'') => (.node () l r, w'')
    | (_, w') => (.nil, w')

/-- The binary tree of a Dyck word. -/
def parse (w : List Bool) : Tree Unit := (parseAux (w.length + 1) w).1

/-- One step: reflect the general tree, add a stem below the root, reflect the binary tree. -/
def stepTree (t : Tree Unit) : Tree Unit := mirrorBin (.node () (parse (reflectWord (word t))) .nil)

/-- The n-th tree of the iteration (A080068), starting from the empty parenthesization. -/
def term (n : ℕ) : Tree Unit := stepTree^[n] .nil

/-- The n-th term is symmetric as a general tree. -/
def IsSymmetric (n : ℕ) : Prop := reflectWord (word (term n)) = word (term n)

theorem main : ∀ n : ℕ, IsSymmetric n ↔ n ∈ ({0, 1, 2, 4} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a080070

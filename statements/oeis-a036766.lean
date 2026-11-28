import Mathlib

/-!
# A036766: Number of ordered rooted trees with n non-root nodes and all outdegrees <= four

Source: https://oeis.org/A036766
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Aug 04 2015, in the entry): the sequence satisfies the holonomic
recurrence
`-3(3n+2)(133n-347)(3n+4)(n+1) a(n) + (111457n⁴-364730n³+228995n²+19310n-33312) a(n-1)
 + 5(-68503n⁴+346618n³-590627n²+397748n-90564) a(n-2) - 25(n-2)(1933n³-9435n²+14354n-7518) a(n-3)
 - 125(n-2)(n-3)(1333n²-4384n+2718) a(n-4) - 625(733n-400)(n-2)(n-3)(n-4) a(n-5) = 0`.

Conventions:
* An ordered (plane) rooted tree is a root with an ordered list of subtrees (`PlaneTree`).
  `a n` counts those with `n` non-root nodes in which every node has at most four children
  (offset 0, `a 0 = 1`: the root alone).
* The entry gives no range. With `a(k) = 0` for `k < 0` the recurrence fails at `n = 0` and
  `n = 1` and holds for every `n ≥ 2` (checked in Python for `n ≤ 80`, computing `a` from the
  entry's functional equation `A = 1 + xA + x²A² + x³A³ + x⁴A⁴`, which reproduces the listed
  data). So it is stated for `n ≥ 2`. For `2 ≤ n ≤ 4` the terms whose index `n - k` would be
  negative carry a vanishing factor `(n-2)`, `(n-3)` or `(n-4)`, so natural-number subtraction
  in the indices is harmless.
* The equation is stated in `ℤ`.
-/

namespace OMA.S_oeis_a036766

/-- Ordered (plane) rooted trees: a root with an ordered list of subtrees. -/
inductive PlaneTree : Type
  | node : List PlaneTree → PlaneTree

mutual
/-- Number of nodes of a tree. -/
def PlaneTree.size : PlaneTree → ℕ
  | .node cs => 1 + PlaneTree.forestSize cs
/-- Total number of nodes of a list of trees. -/
def PlaneTree.forestSize : List PlaneTree → ℕ
  | [] => 0
  | t :: ts => t.size + PlaneTree.forestSize ts
end

/-- Every node has at most `4` children. -/
inductive PlaneTree.OutdegLeFour : PlaneTree → Prop
  | node (cs : List PlaneTree) :
      cs.length ≤ 4 → (∀ c ∈ cs, c.OutdegLeFour) → (PlaneTree.node cs).OutdegLeFour

/-- OEIS A036766: ordered rooted trees with `n` non-root nodes and all outdegrees `≤ 4`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {t : PlaneTree // t.size = n + 1 ∧ t.OutdegLeFour}

/-- Mathar's conjectured recurrence for A036766, for every `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -3 * (3 * (n : ℤ) + 2) * (133 * n - 347) * (3 * n + 4) * (n + 1) * a n
      + (111457 * (n : ℤ) ^ 4 - 364730 * n ^ 3 + 228995 * n ^ 2 + 19310 * n - 33312) * a (n - 1)
      + 5 * (-68503 * (n : ℤ) ^ 4 + 346618 * n ^ 3 - 590627 * n ^ 2 + 397748 * n - 90564)
          * a (n - 2)
      - 25 * ((n : ℤ) - 2) * (1933 * n ^ 3 - 9435 * n ^ 2 + 14354 * n - 7518) * a (n - 3)
      - 125 * ((n : ℤ) - 2) * (n - 3) * (1333 * n ^ 2 - 4384 * n + 2718) * a (n - 4)
      - 625 * (733 * (n : ℤ) - 400) * (n - 2) * (n - 3) * (n - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a036766

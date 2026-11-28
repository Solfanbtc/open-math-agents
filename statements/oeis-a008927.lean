import Mathlib

/-!
# A008927: Number of increasing sequences of star chain type with maximal element n.

Source: https://oeis.org/A008927
Credit: @Solfanbtc

A star (Brauer) addition chain is a sequence `1 = c₀ < c₁ < ... < c_r` in which every element
after the first is the sum of the immediately previous element and some earlier element (possibly
itself): `c_{i+1} = c_i + c_j` with `j ≤ i`. `a(n)` counts all increasing star chains ending in `n`
(not only the minimal ones). Example: `a(5) = 3` (1,2,3,4,5; 1,2,3,5; 1,2,4,5), `a(1) = 1` (the chain
`1`). Offset 1: 1, 1, 1, 2, 3, 6, 10, 20, 36, 70, ...

Since the chain is strictly increasing, `c_{i+1} = c_i + c_j` for some `j ≤ i` is the same as
`c_{i+1} - c_i ∈ {c₀, ..., c_i}`; this is how `IsStarChain` encodes it.

Conjecture (Martin Fuller, Apr 29 2025): `a(n) ~ 2^n / n`.

Sanity check: a python enumeration of star chains gives the first 26 listed terms; evaluating
`IsStarChain` in Lean (`#eval`, over the sorted subsets of `[1, n]`) gives the first 14 terms and
rejects `1, 2, 4, 5, 8`; `a(n) n / 2^n` is 0.68, 0.88, 0.93 at `n = 10, 20, 26`.
-/

namespace OMA.S_oeis_a008927

/-- `l` is an increasing star addition chain: it starts with `1`, is strictly increasing, and each
element after the first is the previous element plus some element at or before it. -/
def IsStarChain (l : List ℕ) : Prop :=
  l.head? = some 1 ∧ l.Pairwise (· < ·) ∧
    ∀ i, i + 1 < l.length → l.getD (i + 1) 0 - l.getD i 0 ∈ l.take (i + 1)

/-- `a(n)`: the number of increasing star chains ending in `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {l : List ℕ | IsStarChain l ∧ l.getLast? = some n}.ncard

/-- Fuller's conjecture: `a(n) ~ 2^n / n`. -/
theorem main :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n => 2 ^ n / n) := by
  sorry

end OMA.S_oeis_a008927

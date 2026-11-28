import Mathlib

/-!
# A134664: Number of 3-stack sortable permutations on n letters.

Source: https://oeis.org/A134664
Credit: @Solfanbtc

Conjecture (Defant, Elvey Price and Guttmann, Counting 3-stack-sortable permutations, 2020;
OEIS A134664, comment by Vaclav Kotesovec, Jun 12 2021):
lim_{n -> infinity} a(n)^(1/n) = 9.69963634535...
(The same comment gives the rigorous lower bound 9.4854...; not restated here.)

Conventions:
* West's stack-sorting map `s`: read the word from left to right; before pushing each letter,
  pop to the output every letter on top of the stack smaller than it; at the end pop the whole
  stack. A permutation `π` of `{0, ..., n-1}` (as the word `π 0, ..., π (n-1)`) is 3-stack
  sortable if `s (s (s π))` is the identity word `0, 1, ..., n-1`.
* The value is given only by its first digits, so "lim = 9.69963634535..." is stated as: the
  limit `L` of `a(n)^(1/n)` (in ℝ) exists and `|L - 9.69963634535| ≤ 10^(-11)`. This covers the
  value truncated or rounded to 11 decimals. The limit is taken along n → ∞ (offset 1; the
  value at n = 0 does not matter).
* Checked in Python with the same algorithm: a(1..9) = 1, 2, 6, 24, 114, 606, 3494, 21426,
  137901, as in %S; checked in Lean (`#eval`) for n ≤ 6.
-/

namespace OMA.S_oeis_a134664

open Filter Topology

/-- One pass of the stack (input, stack with its top first); returns the output word. -/
def pass : List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, st => (st.takeWhile (· < x)) ++ pass xs (x :: st.dropWhile (· < x))

/-- West's stack-sorting map. -/
def stackSort (w : List ℕ) : List ℕ := pass w []

/-- A134664: the number of 3-stack-sortable permutations of `n` letters. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ =>
    stackSort^[3] (List.ofFn fun i => (σ i : ℕ)) = List.range n).card

/-- The growth constant of 3-stack-sortable permutations is `9.69963634535...`. -/
theorem main :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧
      |L - 9.69963634535| ≤ (10 : ℝ) ^ (-11 : ℤ) := by
  sorry

end OMA.S_oeis_a134664

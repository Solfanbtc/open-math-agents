import Mathlib

/-!
# A079559: Number of partitions of n into distinct parts of the form 2^j-1, j=1,2,....

Source: https://oeis.org/A079559
Credit: @Solfanbtc

Comment on the entry (M. F. Hasler, Dec 19 2007):

  A006697(k) gives number of distinct subwords of length k, conjectured to be equal to
  A094913(k)+1.

Here the subwords are those of the infinite 0/1 word A079559 itself, `a 0, a 1, a 2, …`
(by the entry's comments it is the fixed point of `0 ↦ 0, 1 ↦ 110`, i.e. of `a ↦ aab, b ↦ b`,
the word whose factor complexity is A006697). A094913(k) is the maximal number of distinct
nonempty substrings (contiguous factors) of a binary string of length `k`.

The conjecture is stated for all `k ≥ 0`: at `k = 0` both sides are `1`
(A006697(0) = 1, A094913(0) = 0). Data: A006697 = 1, 2, 4, 6, 9, 13, 17, 22, …,
A094913 = 0, 1, 3, 5, 8, 12, 16, 21, ….

* `a n` is A079559 by its name: the number of sets of distinct parts, each of the form
  `2^j - 1` with `j ≥ 1`, summing to `n` (all such parts `≤ n` are among `2^j - 1`, `1 ≤ j ≤ n+1`).
* `subwordCount k` is the number of distinct words `u` of length `k` occurring as
  `a i, a (i+1), …, a (i+k-1)` for some `i`.
* `maxSubstrings k` is A094913(k): the maximum, over binary strings `s` of length `k`, of the
  number of distinct nonempty contiguous substrings (`List.IsInfix`) of `s`.
-/

namespace OMA.S_oeis_a079559

/-- The admissible parts `2^j - 1` (`1 ≤ j ≤ n + 1`), which include every such part `≤ n`. -/
def parts (n : ℕ) : Finset ℕ := (Finset.Icc 1 (n + 1)).image fun j => 2 ^ j - 1

/-- A079559: the number of partitions of `n` into distinct parts of the form `2^j - 1`,
`j = 1, 2, …`. -/
def a (n : ℕ) : ℕ := ((parts n).powerset.filter fun S => S.sum id = n).card

/-- The number of distinct subwords (factors) of length `k` of the infinite word `a`. -/
noncomputable def subwordCount (k : ℕ) : ℕ :=
  Set.ncard {u : Fin k → ℕ | ∃ i : ℕ, ∀ j : Fin k, a (i + j) = u j}

/-- The number of distinct nonempty contiguous substrings of a list. -/
noncomputable def substringCount (l : List Bool) : ℕ :=
  Set.ncard {u : List Bool | u ≠ [] ∧ u <:+: l}

/-- A094913: the maximal number of distinct nonempty substrings of a binary string of
length `k`. -/
noncomputable def maxSubstrings (k : ℕ) : ℕ :=
  Finset.univ.sup fun s : Fin k → Bool => substringCount (List.ofFn s)

/-- Hasler's conjecture: the number of distinct subwords of length `k` of A079559
(that is, A006697(k)) equals A094913(k) + 1, for every `k`. -/
theorem main : ∀ k : ℕ, subwordCount k = maxSubstrings k + 1 := by
  sorry

end OMA.S_oeis_a079559

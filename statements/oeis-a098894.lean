import Mathlib

/-!
# A098894: Values of k such that {s(1),...,s(k)} is a palindrome, where {s(1),s(2),...} is the fixed point of the substitutions 0->1 and 1->110.

Source: https://oeis.org/A098894
Credit: @Solfanbtc

Conjecture (Sean A. Irvine, Jul 14 2022): A098894 is the sequence of partial sums of A152113.

Definitions.
* `σ` is the substitution 0 ↦ 1, 1 ↦ 110 on binary words; starting from the word 1, the words
  `σ^m(1)` (1, 110, 1101101, ...) are successive prefixes of one another (σ(1) begins with 1),
  and `s` is their limit, the fixed point of `σ` starting with 1. `σ^m(1)` has at least `m + 1`
  letters, so `s(i) = (σ^i(1))[i-1]` (offset 1).
* `IsPalPrefix k` : `k ≥ 1` and `s(1), ..., s(k)` is a palindrome; A098894(n) is the n-th such
  `k` (offset 1).
* A152113 is A001333 with terms repeated (offset 1): A152113(i) = A001333(⌊(i+1)/2⌋), where
  A001333(0) = A001333(1) = 1 and A001333(n) = 2 A001333(n-1) + A001333(n-2); the data
  1, 1, 3, 3, 7, 7, 17, ... come out right.
* Statement: for every n ≥ 1, A098894(n) = A152113(1) + ... + A152113(n).
Checked with python3: the palindromic prefixes of `s` up to length 3880899 are exactly the data
terms up to 3880897, and the partial sums of A152113 reproduce all 35 data terms.
-/

namespace OMA.S_oeis_a098894

/-- The substitution 0 ↦ 1, 1 ↦ 110, applied letterwise. -/
def σ (w : List ℕ) : List ℕ := w.flatMap fun c => if c = 0 then [1] else [1, 1, 0]

/-- `s i` (offset 1): the `i`-th letter of the fixed point of `σ` starting with 1. -/
def s (i : ℕ) : ℕ := (σ^[i] [1]).getD (i - 1) 0

/-- `s(1), ..., s(k)` is a palindrome, `k ≥ 1`. -/
def IsPalPrefix (k : ℕ) : Prop :=
  1 ≤ k ∧ ((List.range k).map fun i => s (i + 1)).reverse = (List.range k).map fun i => s (i + 1)

/-- A098894(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsPalPrefix (n - 1)

/-- A001333: 1, 1, 3, 7, 17, 41, ... -/
def A001333 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * A001333 (n + 1) + A001333 n

/-- A152113(i), offset 1: A001333 with terms repeated. -/
def A152113 (i : ℕ) : ℕ := A001333 ((i + 1) / 2)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ i ∈ Finset.Icc 1 n, A152113 i := by
  sorry

end OMA.S_oeis_a098894

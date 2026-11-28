import Mathlib

/-!
# A113918: Cardinality of Image^inf({ 2 }) under repeated base-n zero-split squaring.

Source: https://oeis.org/A113918
Credit: @Solfanbtc

Conjecture (entry comment): a(n) is finite for all n.

Definitions (entry comment): "Define f_b(x) to be the set of base b numbers left after splitting
x^2 at its zero digits and Image_b(S) = union_{x in S}{ { x } union f_b(S) }, then
a(n) = | Image_n^inf({ 2 }) |." Example: f_10(29648) = {4, 39, 879} since
29648^2 = 879003904.
* `zeroSplit b x`: write `x^2` in base `b`, cut the digit string at every zero digit, discard
  empty pieces, and read each remaining block of nonzero digits as a base-`b` number.
  (`Nat.digits` is little-endian; a little-endian block read with `Nat.ofDigits` is the number
  written by that block.)
* `Reach b y`: `y` lies in Image_b^inf({2}), the least set containing 2 and closed under
  `x ↦ zeroSplit b x`.
* Statement: for every base `n ≥ 2` (offset 2) this set is finite, i.e. a(n) is finite.
Checked with python3: the sizes for n = 2..8 are the data 2, 18, 2, 3050, 34762, 3087549, 2.
-/

namespace OMA.S_oeis_a113918

/-- The numbers obtained by splitting `x^2`, written in base `b`, at its zero digits. -/
def zeroSplit (b x : ℕ) : List ℕ :=
  (((Nat.digits b (x ^ 2)).splitOn 0).filter fun l => l ≠ []).map (Nat.ofDigits b)

/-- `y ∈ Image_b^inf({2})`. -/
inductive Reach (b : ℕ) : ℕ → Prop
  | base : Reach b 2
  | step {x y : ℕ} : Reach b x → y ∈ zeroSplit b x → Reach b y

theorem main : ∀ n : ℕ, 2 ≤ n → {y : ℕ | Reach n y}.Finite := by
  sorry

end OMA.S_oeis_a113918

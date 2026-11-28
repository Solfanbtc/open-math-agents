import Mathlib

/-!
# A125758: Numbers congruent to 4 or 7 (mod 9).

Source: https://oeis.org/A125758
Credit: @Solfanbtc

Conjecture (N. J. A. Sloane and David Applegate, OEIS A125758, %C line): for a given integer
`m`, write its binary representation in reverse order (as in A125626, A125754); let a 0 mean
"halving" and a 1 mean "k ↦ 3k+1". Then `m` specifies an operation on real numbers
`k ↦ f_m(k)`. If the equation `f_m(k) = k` has a positive integer solution for some `m`, then
the values of `k` are precisely the terms of this sequence, the numbers `≡ 4` or `7 (mod 9)`;
i.e. A125757, sorted and with duplicates removed, coincides with A125758.

Formalization.
* `Nat.digits 2 m` lists the binary digits of `m` least significant first, i.e. the reversed
  binary representation, all digits included (the last one is the leading 1). As in the
  A125626 example (`200 = 11001000₂`, reversed `00010011`: three halvings, `3k+1`, two halvings,
  `3k+1`, `3k+1`, fixed point `k = 40`), these operations are applied in that order.
* `f m` acts on `ℚ` (each `f_m` is affine with rational coefficients, so a real solution of
  `f_m(k) = k` with `k` a positive integer is the same as a rational one).
* `m ≥ 1` (`m = 0` has no binary digits and would give the identity map).
* The conjecture: for every positive integer `k`, `f_m(k) = k` for some `m ≥ 1` iff
  `k % 9 = 4` or `k % 9 = 7`.

Checked with python3: the positive integer fixed points of `f_m`, `1 ≤ m < 2^20`, in order of
`m`, begin `4, 4, 16, 13, 40, ...` (all listed terms of A125757); every one of them `≤ 300` is
`≡ 4, 7 (mod 9)`, and 28 of the 66 such numbers `≤ 300` already occur (the others, such as
`25`, need longer words; the entry exhibits a 21-step cycle through `25`).
-/

namespace OMA.S_oeis_a125758

/-- The operation coded by `m`: halve for a binary digit 0, `x ↦ 3x + 1` for a digit 1, the
digits of `m` being read from the least significant one. -/
def f (m : ℕ) (x : ℚ) : ℚ :=
  (Nat.digits 2 m).foldl (fun y b => if b = 0 then y / 2 else 3 * y + 1) x

/-- The positive integers fixed by some `f_m` are exactly those `≡ 4, 7 (mod 9)`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    ((∃ m : ℕ, 1 ≤ m ∧ f m k = k) ↔ k % 9 = 4 ∨ k % 9 = 7) := by
  sorry

end OMA.S_oeis_a125758

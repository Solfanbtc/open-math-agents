import Mathlib

/-!
# A072217: Consider the Reverse and Add! problem (cf. A001127); of all the n-digit numbers N which eventually reach a palindrome, pick that number N which takes the greatest number of steps to converge (in case of a tie, pick the smallest N); sequence gives number of steps N takes to converge.

Source: https://oeis.org/A072217
Credit: @Solfanbtc

The entry lists `a(1), …, a(18) = 2, 24, 23, 21, 55, 64, 96, 96, 98, 109, 149, 149, 188, 186, 201,
197, 236, 232` and says (%C): "Since we do not even know if 196 eventually converges (see A006960,
A023108) for n >= 3 these values are only conjectures." We state that all 18 listed values are
correct. (`a(1)` and `a(2)` are finite checks; for `n ≥ 3` the claim includes, e.g., that no
3-digit number such as 196 reaches a palindrome after more than 23 steps.)

Conventions:
* One step is `x ↦ x + rev(x)` (base-10 digit reversal). The number of steps `N` takes to converge
  is the least `k ≥ 1` such that the `k`-th iterate is a palindrome: at least one step is taken
  (otherwise every 1-digit number would take 0 steps, whereas `a(1) = 2`, attained by `5 → 10 → 11`).
* `N` is `n`-digit when `(Nat.digits 10 N).length = n` (so `N ≥ 1`; including `0` for `n = 1`
  would not change `a(1)`, since `0` takes one step).
* `a(n)` is the largest number of steps among the `n`-digit numbers that reach a palindrome
  (the tie-breaking rule only selects `N`, not the value). The set is finite, so `sSup` is its
  maximum.
* Checked in Python (iterating up to 400 steps): `a(1), …, a(4) = 2, 24, 23, 21`, attained by
  `5, 89, 187, 1297`.
-/

namespace OMA.S_oeis_a072217

/-- Reverse the base-10 digits. -/
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Reverse-and-add. -/
def T (x : ℕ) : ℕ := x + rev x

/-- `x` is a base-10 palindrome. -/
def IsPalindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- `N` eventually reaches a palindrome (after at least one step). -/
def Converges (N : ℕ) : Prop := ∃ k, 1 ≤ k ∧ IsPalindrome (T^[k] N)

/-- The number of steps `N` takes to reach a palindrome. -/
noncomputable def steps (N : ℕ) : ℕ := sInf {k | 1 ≤ k ∧ IsPalindrome (T^[k] N)}

/-- `a(n)`: the greatest number of steps among the `n`-digit numbers reaching a palindrome. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {s | ∃ N, (Nat.digits 10 N).length = n ∧ Converges N ∧ steps N = s}

/-- The listed values of A072217 are correct. -/
theorem main :
    (List.range 18).map (fun i => a (i + 1)) =
      [2, 24, 23, 21, 55, 64, 96, 96, 98, 109, 149, 149, 188, 186, 201, 197, 236, 232] := by
  sorry

end OMA.S_oeis_a072217

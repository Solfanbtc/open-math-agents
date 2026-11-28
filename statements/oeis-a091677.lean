import Mathlib

/-!
# A091677: a(n) = smallest non-palindromic k such that the base-4 Reverse and Add! trajectory of k is palindrome-free and joins the trajectory of A091675(n).

Source: https://oeis.org/A091677
Credit: @Solfanbtc

Base-4 Reverse and Add!: `R(x) = x + rev₄(x)`, `rev₄(x)` the number whose base-4 digits are
those of `x` reversed. The trajectory of `x` is `x, R(x), R(R(x)), ...`. Two trajectories join
when they have a common value. A091675 lists the positive `n` whose trajectory joins the
trajectory of no `m` with `1 ≤ m < n`.

The 1-1 property of the mapping of the entry rests on the following conjecture, stated in the
entry: the base-4 Reverse and Add! trajectory of each term of A091675 contains only a finite
number of palindromes (cf. A091680). Since `R(x) > x` for `x ≥ 1`, the values on a trajectory
are distinct, so this is finiteness of the set of steps `i` with `R^i(n)` a base-4 palindrome.
-/

namespace OMA.S_oeis_a091677

/-- Reverse the base-4 digits. -/
def rev4 (x : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 4 x).reverse

/-- One base-4 Reverse and Add! step. -/
def R (x : ℕ) : ℕ := x + rev4 x

/-- `x` is a base-4 palindrome. -/
def IsPal4 (x : ℕ) : Prop := (Nat.digits 4 x).reverse = Nat.digits 4 x

/-- `n` is a term of A091675. -/
def IsA091675 (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → ∀ i j : ℕ, R^[i] n ≠ R^[j] m

/-- The trajectory of each term of A091675 contains only finitely many palindromes. -/
theorem main : ∀ n : ℕ, IsA091675 n → {i : ℕ | IsPal4 (R^[i] n)}.Finite := by
  sorry

end OMA.S_oeis_a091677

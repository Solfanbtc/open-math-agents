import Mathlib

/-!
# A135507: a(1) = 1; for n > 1, a(n) = 2*a(n-1) + lcm(a(n-1),n).

Source: https://oeis.org/A135507
Credit: @Solfanbtc

Conjecture (Bill McEachen, Apr 04 2024, in the entry): Let p = a(n+1)/a(n) - 2. If p is prime
then p = A140460(m) or p = A140460(m) + 2 for some m.

Conventions.
* `a` is 1-indexed as in the entry (`a 0` is an unused placeholder); the statement is for every
  index `n ≥ 1`. `a(n)` divides `a(n+1) = 2 a(n) + lcm(a(n), n+1)`, so the quotient is an exact
  natural number `≥ 3` and `a(n+1)/a(n) - 2 = (n+1)/gcd(a(n), n+1)`; ℕ division and
  subtraction are therefore exact here.
* A140460: a(0) = 2; thereafter a(n) = smallest integer not a multiple of an earlier term nor a
  sum of two earlier terms. Following the entry's programs (Mathematica `Subsets[s, {2}]`, and the
  C sieve with `j < i`), "sum of two earlier terms" means two distinct earlier terms (a sum `x + x`
  is a multiple of `x` anyway). Equivalently, as a set: `m ≥ 2` is a term iff no smaller term
  divides `m` and `m` is not the sum of two distinct smaller terms. "For some m" ranges over all
  indices, so the conclusion is: `p` is a term of A140460, or `p - 2` is.
* Checked with python3: the sieve reproduces all 51 listed terms of A140460, the recursion
  reproduces all 23 listed terms of A135507, and the conjecture holds for all n ≤ 5000.
-/

namespace OMA.S_oeis_a135507

/-- A135507, 1-indexed: `a 1 = 1`, `a n = 2 a(n-1) + lcm(a(n-1), n)` (`a 0 = 0` unused). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * a (n + 1) + Nat.lcm (a (n + 1)) (n + 2)

/-- `m` may join A140460 given the list `L` of the terms below `m`: `m ≥ 2`, no term of `L`
divides `m`, and `m` is not the sum of two distinct terms of `L`. -/
def admissible (m : ℕ) (L : List ℕ) : Prop :=
  2 ≤ m ∧ (∀ x ∈ L, ¬ x ∣ m) ∧ ∀ x ∈ L, ∀ y ∈ L, x ≠ y → x + y ≠ m

instance (m : ℕ) (L : List ℕ) : Decidable (admissible m L) := by
  unfold admissible; infer_instance

/-- The terms of A140460 that are `< m`, in increasing order. -/
def termsBelow : ℕ → List ℕ
  | 0 => []
  | m + 1 => if admissible m (termsBelow m) then termsBelow m ++ [m] else termsBelow m

/-- `q` is a term of A140460. -/
def InA140460 (q : ℕ) : Prop := q ∈ termsBelow (q + 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a (n + 1) / a n - 2).Prime →
      InA140460 (a (n + 1) / a n - 2) ∨
        ∃ q : ℕ, InA140460 q ∧ a (n + 1) / a n - 2 = q + 2 := by
  sorry

end OMA.S_oeis_a135507

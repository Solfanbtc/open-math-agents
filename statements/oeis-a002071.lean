import Mathlib

/-!
# A002071: Number of pairs of consecutive integers x, x+1 such that all prime factors of both x and x+1 are at most the n-th prime.

Source: https://oeis.org/A002071
Credit: @Solfanbtc

Two comments of the entry state: assuming an effective abc conjecture (`c < rad(abc)^2`),
a(20)-a(33) is (4839, 6040, 7441, 9179, 11134, 13374, 16167, 19507, 23367, 27949, 33233, 39283,
46166, 54150), and a(34)-a(36) is (63428, 74007, 86125). Both are stated together below as one
implication: the effective abc conjecture implies these seventeen values.

Conventions:
* `a n` counts the integers `x ≥ 1` such that every prime factor of `x` and of `x + 1` is at
  most the n-th prime `Nat.nth Nat.Prime (n - 1)` (n ≥ 1; the 1st prime is 2). This gives
  a(1..5) = 1, 4, 10, 23, 40, as in the entry. By Størmer's theorem the set is finite, so
  `Set.ncard` is its size.
* The effective abc conjecture is read in its standard form: for all coprime positive integers
  `a, b` with `a + b = c`, `c < rad(abc)^2`, where `rad` is the product of the distinct prime
  factors (coprimality of `a, b` with `a + b = c` makes `a, b, c` pairwise coprime).

A further comment says a(22) and a(23) were also computed unconditionally and agree with these
values; that is a computation, not part of the conditional claim, and is not stated here.
-/

namespace OMA.S_oeis_a002071

/-- The radical of `n`: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- A002071: the number of `x ≥ 1` with all prime factors of `x` and `x + 1` at most the
n-th prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ | 0 < x ∧ (∀ p ∈ x.primeFactors, p ≤ Nat.nth Nat.Prime (n - 1)) ∧
    ∀ p ∈ (x + 1).primeFactors, p ≤ Nat.nth Nat.Prime (n - 1)}

/-- The effective abc conjecture `c < rad(abc)^2`. -/
def EffectiveABC : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c → c < rad (a * b * c) ^ 2

/-- Assuming the effective abc conjecture `c < rad(abc)^2`, the values a(20), ..., a(36) of
A002071 are as listed in the entry. -/
theorem main : EffectiveABC →
    (List.range 17).map (fun i => a (20 + i)) =
      [4839, 6040, 7441, 9179, 11134, 13374, 16167, 19507, 23367, 27949, 33233, 39283,
        46166, 54150, 63428, 74007, 86125] := by
  sorry

end OMA.S_oeis_a002071

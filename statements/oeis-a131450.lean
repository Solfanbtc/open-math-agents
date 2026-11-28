import Mathlib

/-!
# A131450: a(n) is the number of integers x that can be written x = (2^c(1) - 2^c(2) - 3*2^c(3) - 3^2*2^c(4) - ... - 3^(m-2)*2^c(m) - 3^(m-1)) / 3^m for integers c(1), c(2), ..., c(m) such that n = c(1) > c(2) > ... > c(m) > 0 and c(1) - c(2) != 2 if m >= 2.

Source: https://oeis.org/A131450
Credit: @Solfanbtc

Claim (entry comment): lim_{n→∞} a(n)/a(n-1) = 4/3.

Definition, following the name literally. A choice of c(1) = n > c(2) > ... > c(m) > 0 is a subset
S ⊆ {1, ..., n-1} (the values c(2), ..., c(m), listed in decreasing order as l), with m = |S| + 1,
subject to n - c(2) ≠ 2 when S is nonempty. The value is
x = (2^n - Σ_{t<|S|} 3^t·2^(l_t) - 3^|S|) / 3^(|S|+1) (for m = 1 this is (2^n - 1)/3), and a(n)
counts the distinct integers obtained (the choices whose numerator is divisible by 3^(|S|+1)).
A brute-force python check with exactly this definition gives the listed terms
0, 1, 0, 1, 1, 1, 1, 1, 2, 4, 6, 6, 7, 8, 11, 18, 23, 29, 39, 52 for n = 1..20 (every integer
obtained there is positive, so "integers" and "positive integers" give the same counts).
Offset 1: the ratio a(n)/a(n-1) is taken as n → ∞ (a(n) > 0 for n ≥ 4, so it is eventually
defined; Lean's x/0 = 0 at small n does not affect the limit).
-/

namespace OMA.S_oeis_a131450

/-- Numerator 2^n - Σ_t 3^t·2^(l_t) - 3^|S|, with l = S in decreasing order. -/
def num (n : ℕ) (S : Finset ℕ) : ℤ :=
  let l := (S.sort (· ≤ ·)).reverse
  2 ^ n - (((List.range l.length).map fun t => (3 : ℤ) ^ t * 2 ^ (l.getD t 0)).sum) - 3 ^ S.card

/-- Admissible choices c(2) > ... > c(m) > 0 below c(1) = n, with n - c(2) ≠ 2. -/
def admissible (n : ℕ) (S : Finset ℕ) : Prop :=
  0 ∉ S ∧ (∀ c ∈ S, n - c ≠ 2 ∨ ∃ d ∈ S, c < d)

instance (n : ℕ) : DecidablePred (admissible n) := fun S => by unfold admissible; infer_instance

/-- A131450(n): number of distinct integers x so obtained. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range n).powerset.filter fun S =>
      admissible n S ∧ (3 : ℤ) ^ (S.card + 1) ∣ num n S).image
    fun S => num n S / 3 ^ (S.card + 1)).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) Filter.atTop (nhds (4 / 3)) := by
  sorry

end OMA.S_oeis_a131450

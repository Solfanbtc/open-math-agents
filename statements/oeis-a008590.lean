import Mathlib

/-!
# A008590: Multiples of 8.

Source: https://oeis.org/A008590
Credit: @Solfanbtc

Conjecture (Lechoslaw Ratajczak, Sep 03 2017, in the entry): let gcd2(b,c) be the second
greatest common divisor and lcd2(b,c) the second least common divisor of non-coprime integers
b and c. The positive terms of this sequence are exactly the integers m for which both
Sum_{k=1..m, gcd(k,m) <> 1} gcd2(k,m) and Sum_{k=1..m, gcd(k,m) <> 1} lcd2(k,m) are even.
(Checked by him for 5*10^4 consecutive integers.)

Conventions.
* The common divisors of k and m are the divisors of g = gcd(k, m). For g > 1 the least one
  is 1 and the second least is the smallest prime factor `g.minFac`; the greatest is g and the
  second greatest is g / g.minFac. So gcd2(k,m) = g / g.minFac and lcd2(k,m) = g.minFac.
  This reproduces the entry's examples: for m = 8 the sums are 1+2+1+4 = 8 and 2+2+2+2 = 8;
  for m = 16 they are 20 and 16; for m = 24 they are 44 and 36.
* Range. At m = 1 both sums are empty (= 0, even) but 1 is not a multiple of 8, so the claim
  fails at this trivial value; the minimal fix states it for m ≥ 2. (python3: for
  2 ≤ m ≤ 6000, "both sums even" holds iff 8 ∣ m.)
-/

namespace OMA.S_oeis_a008590

/-- Sum over 1 ≤ k ≤ m with gcd(k,m) ≠ 1 of gcd2(k,m) = g / minFac g, g = gcd(k,m). -/
def sumGcd2 (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1),
    Nat.gcd k m / (Nat.gcd k m).minFac

/-- Sum over 1 ≤ k ≤ m with gcd(k,m) ≠ 1 of lcd2(k,m) = minFac g, g = gcd(k,m). -/
def sumLcd2 (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), (Nat.gcd k m).minFac

theorem main : ∀ m : ℕ, 2 ≤ m → (Even (sumGcd2 m) ∧ Even (sumLcd2 m) ↔ 8 ∣ m) := by
  sorry

end OMA.S_oeis_a008590

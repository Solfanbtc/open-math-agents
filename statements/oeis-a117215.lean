import Mathlib

/-!
# A117215: odd squarefree n have a unique divisor of x^n - 1 of maximal height

Source: https://oeis.org/A117215 (with https://oeis.org/A114536)
The height of a polynomial is the largest absolute value of its coefficients. The (monic)
divisors of `x^n - 1` in `ℤ[x]` are the products `∏_{d ∈ S} Φ_d` over subsets `S` of the
divisors of `n` (`Φ_d` the cyclotomic polynomials; distinct `S` give distinct products), and
A114536(n) is the maximal height of such a divisor. A117215(n) (offset 1) is the number of
divisors of `x^n - 1` having this maximal height: 2, 4, 4, 8, 4, 2, ...
The entry's comment states "Conjectures: if n is odd and squarefree, then a(n)=1; if n/2^k is
odd and squarefree for k>0, then a(n)=2", and adds that for `n` a product of distinct odd primes
"it appears that each cyclotomic index has the form d=p1^e1...pk^ek, where the ei are either 0
or 1 and sum(ei) is odd".

What is stated. The first conjecture with the minimal fix: for every odd squarefree `n` with at
least two prime factors, exactly one divisor of `x^n - 1` has the maximal height. The fix is
forced by the entry itself: `a(1) = 2` and `a(p) = 4` for every odd prime `p` (comment and data),
so `n = 1` and odd primes must be excluded; the same comment's examples (`a(pq) = 1`) are about
products of at least two primes.

What is not stated, and why (python3, exact integer arithmetic with cyclotomic polynomials;
the program reproduces A114536(1..60) and A117215(1..60)):
* the second conjecture is contradicted by the entry's own data: `24 / 2^3 = 3` is odd and
  squarefree, but `a(24) = 20` (also `a(80) = 4`, `a(96) = 32`, `a(112) = 18`);
* the third remark fails at `n = 195 = 3·5·13`: the unique divisor of maximal height 57 is
  `Φ_1 Φ_15 Φ_39 Φ_65`, whose indices all have an even number of prime factors (the product
  `Φ_3 Φ_5 Φ_13 Φ_195` has height 50).
The stated conjecture holds for every odd squarefree `n < 400` with at least two prime factors
and at most 16 divisors (python3, all subsets checked).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a117215

open Polynomial

/-- The height of an integer polynomial: the largest absolute value of a coefficient. -/
def height (f : ℤ[X]) : ℕ := f.support.sup fun i => (f.coeff i).natAbs

/-- The divisor `∏_{d ∈ S} Φ_d` of `x^n - 1` attached to a set `S` of divisors of `n`. -/
noncomputable def divisorOf (S : Finset ℕ) : ℤ[X] := ∏ d ∈ S, cyclotomic d ℤ

/-- A114536: the maximal height of a divisor of `x^n - 1`. -/
noncomputable def maxHeight (n : ℕ) : ℕ :=
  n.divisors.powerset.sup fun S => height (divisorOf S)

/-- A117215: the number of divisors of `x^n - 1` of maximal height. -/
noncomputable def a (n : ℕ) : ℕ :=
  (n.divisors.powerset.filter fun S => height (divisorOf S) = maxHeight n).card

theorem main : ∀ n : ℕ, Odd n → Squarefree n → 2 ≤ n.primeFactors.card → a n = 1 := by
  sorry

end OMA.S_oeis_a117215

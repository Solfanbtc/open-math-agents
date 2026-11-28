import Mathlib

/-!
# A064377: Numbers n such that sigma_4(n) > phi(n)^5.

Source: https://oeis.org/A064377
Credit: @Solfanbtc

"It is conjectured that there are no other solutions" (than the 111 listed terms 2, 3, 4, ...,
1680, 2310). The sequence is known to be finite (Charles R Greathouse IV, 2015, via Grönwall's
theorem); the conjecture is that the list is complete. Stated as an equality of sets with all
terms of %S, %T, %U.

Conventions.
* sigma_4 = `ArithmeticFunction.sigma 4`, phi = `Nat.totient`; n ranges over positive integers
  (n = 0 gives 0 > 0, false, so it needs no exclusion).
* python3: the n < 3·10^5 with sigma_4(n) > phi(n)^5 are exactly the listed 111 terms.
-/

namespace OMA.S_oeis_a064377

/-- The listed terms of A064377. -/
def listed : Finset ℕ :=
  {2, 3, 4, 6, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44,
    48, 50, 54, 56, 60, 66, 70, 72, 78, 80, 84, 90, 96, 100, 102, 108, 110, 114, 120, 126,
    130, 132, 138, 140, 144, 150, 156, 162, 168, 174, 180, 186, 192, 198, 204, 210, 216, 222,
    228, 234, 240, 246, 252, 258, 264, 270, 276, 282, 294, 300, 306, 312, 330, 336, 342, 360,
    378, 390, 396, 420, 450, 462, 480, 504, 510, 540, 546, 570, 600, 630, 660, 690, 714, 720,
    750, 780, 840, 870, 930, 990, 1020, 1050, 1170, 1260, 1470, 1680, 2310}

theorem main :
    {n : ℕ | Nat.totient n ^ 5 < ArithmeticFunction.sigma 4 n} = ↑listed := by
  sorry

end OMA.S_oeis_a064377

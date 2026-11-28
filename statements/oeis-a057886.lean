import Mathlib

/-!
# A057886: Number of integer 4-tuples that give the lengths of the sides of a nondegenerate quadrilateral with perimeter n.

Source: https://oeis.org/A057886
Credit: @Solfanbtc

Conjectures (OEIS A057886, %F):
1. a(1) = 0 and, for n > 1, a(n) = a(n-1) + d(n-1), where d(n) = floor(n/4)*floor((n-2)/4)
   if n is even and d(n) = floor((n+1)/4) if n is odd.
2. (Colin Barker, Oct 27 2013) a(n) = ((n-1)*((n-2)*n+18) + 6 sin(Pi n/2) + 18 cos(Pi n/2))/96
   for n even; a(n) = (n^3 - 7n + 6 sin(Pi n/2) + 18 cos(Pi n/2))/96 for n odd.
3. (Colin Barker) G.f.: x^4*(x^3-x^2+1) / ((x-1)^4*(x+1)^3*(x^2+1)).
4. (Luce Etienne, Nov 06 2014) a(n) = (2n^3 - 3n^2 + 13n - 18 - 3(n^2-9n+6)(-1)^n
   + 12(2+(-1)^n)(-1)^((2n+(-1)^n-1)/4))/192.
`main` is the conjunction of 1-4.

Conventions:
* A quadrilateral is given by its cyclic sequence of side lengths (x1, x2, x3, x4), positive
  integers with sum n; it is nondegenerate iff every side is less than the sum of the other
  three, i.e. 2 * max < n. Two sequences give the same quadrilateral when they differ by a
  rotation or a reflection (dihedral group of order 8): the example counts (1,2,2,3) and
  (1,2,3,2) as different but not (1,2,2,3) and (3,2,2,1), giving a(8) = 5. `a n` counts the
  sequences that are lexicographically least in their dihedral orbit (comparing the key
  x1 B^3 + x2 B^2 + x3 B + x4 with B = n + 1).
* Offset 1; `a 0 = 0` (no positive 4-tuple has sum 0), as the g.f. requires.
* In 2, sin and cos are real; in 4 the exponent (2n+(-1)^n-1)/4 is an integer (it is floor(n/2)).
  2 and 4 are stated for n ≥ 1; 1 for n ≥ 2.
* Checked in Python: `a` reproduces every term of %S, %T, %U; 1, 2 and 4 hold for n < 90; the
  product of the g.f. of a(0..89) with the denominator of 3 is x^4 - x^6 + x^7 up to x^79.
-/

namespace OMA.S_oeis_a057886

open PowerSeries

/-- Lexicographic key of a 4-tuple, base `B`. -/
def key (B : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : ℕ := ((t.1 * B + t.2.1) * B + t.2.2.1) * B + t.2.2.2

/-- The 8 images of `(a, b, c, d)` under rotations and reflections. -/
def dihedral (t : ℕ × ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let (a, b, c, d) := t
  [(a, b, c, d), (b, c, d, a), (c, d, a, b), (d, a, b, c),
    (d, c, b, a), (a, d, c, b), (b, a, d, c), (c, b, a, d)]

/-- A057886: nondegenerate integer quadrilaterals of perimeter `n`, up to rotation and
reflection. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t =>
    t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = n ∧
    2 * max (max t.1 t.2.1) (max t.2.2.1 t.2.2.2) < n ∧
    ∀ s ∈ dihedral t, key (n + 1) t ≤ key (n + 1) s).card

/-- The increment `d(n)` of conjecture 1. -/
def d (n : ℕ) : ℕ := if n % 2 = 0 then (n / 4) * ((n - 2) / 4) else (n + 1) / 4

/-- The four conjectured formulas. -/
theorem main :
    (a 1 = 0 ∧ ∀ n : ℕ, 2 ≤ n → a n = a (n - 1) + d (n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (if n % 2 = 0 then
          ((n - 1 : ℝ) * ((n - 2) * n + 18) + 6 * Real.sin (Real.pi * n / 2)
            + 18 * Real.cos (Real.pi * n / 2)) / 96
        else
          ((n : ℝ) ^ 3 - 7 * n + 6 * Real.sin (Real.pi * n / 2)
            + 18 * Real.cos (Real.pi * n / 2)) / 96)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 4 * (X + 1) ^ 3 * (X ^ 2 + 1)) =
      X ^ 4 * (X ^ 3 - X ^ 2 + 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (2 * (n : ℚ) ^ 3 - 3 * n ^ 2 + 13 * n - 18 - 3 * (n ^ 2 - 9 * n + 6) * (-1) ^ n
        + 12 * (2 + (-1) ^ n) * (-1 : ℚ) ^ ((2 * (n : ℤ) + (-1) ^ n - 1) / 4)) / 192) := by
  sorry

end OMA.S_oeis_a057886

import Mathlib

/-!
# A005598: a(n) = 1 + Sum_{i=1..n} (n-i+1)*phi(i).

Source: https://oeis.org/A005598 (see also https://oeis.org/A360042)
Credit: @Solfanbtc

The source's claim: a(n) is conjectured to be the number of regions in a Farey fan of order n.

The Farey fan of order n (McIlroy, A Note on Discrete Representation of Lines, AT&T Technical
Journal 64 (1985); OEIS A360042, A360043): in the unit square of parameters (m, b),
0 ≤ m ≤ 1, 0 ≤ b ≤ 1 (lines y = m*x + b), draw every line m*x + b = y with x an integer,
1 ≤ x ≤ n, and y an integer. Its vertices along each side of the square are the Farey
fractions of order n (A005728(n) of them). A region is a connected component of the open
square minus the drawn lines.

Check by computation (exact rational arithmetic, Euler's formula), for 1 ≤ n ≤ 8: this
arrangement has 4, 6, 11, 17, 29, 39, 59, 79 vertices (= A360042) and 2, 4, 8, 14, 24, 36,
54, 76 regions (= A005598). The range 1 ≤ n is the offset of A360042 (fans start at order 1).
-/

namespace OMA.S_oeis_a005598

/-- The lines `m * x + b = y` of the Farey fan of order `n`, as a subset of the `(m, b)`
plane: `x` an integer with `1 ≤ x ≤ n`, `y` any integer. -/
def fanLines (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ ∃ y : ℤ, (x : ℝ) * p.1 + p.2 = y}

/-- The open unit square with the lines of the Farey fan of order `n` removed;
its connected components are the regions of the fan. -/
def fanComplement (n : ℕ) : Set (ℝ × ℝ) :=
  (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) \ fanLines n

/-- A005598(n) = 1 + Sum_{i=1..n} (n-i+1)*phi(i). -/
def a (n : ℕ) : ℕ := 1 + ∑ i ∈ Finset.Icc 1 n, (n - i + 1) * Nat.totient i

theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.card (ConnectedComponents (fanComplement n)) = a n := by
  sorry

end OMA.S_oeis_a005598

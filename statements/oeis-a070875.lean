import Mathlib

/-!
# A070875: Binary expansion is 1x100...0 where x = 0 or 1.

Source: https://oeis.org/A070875
Credit: @Solfanbtc

Conjecture (George Beck, Mar 26 2022, OEIS A070875): "a(n) = -1 + positions of the ones in
A309019(n+2) - A002487(n+2)", i.e. the ones of the difference sequence A309019 - A002487 occur
exactly at the terms of A070875.

Index convention. Read literally, the shifts are ambiguous; the reading that matches the data is:
writing the difference d(m) = A309019(m) - A002487(m) for m = 0, 1, 2, ... (both sequences have
offset 0) as a list whose positions are counted from 1, the ones are at positions a(n) + 1, so
d(m) = 1 exactly for m = 5, 7, 10, 14, 20, 28, ... = the terms of A070875. `main` states this:
d(m) = 1 iff m is a term. (With other readings of "n+2" the positions are shifted and do not give
the terms.)

Definitions.
* Terms of A070875 (from the name): the binary expansion is 1x1 followed by zeros, i.e.
  m = 5 * 2^k or m = 7 * 2^k for some k >= 0.
* A309019: b(0) = 0, b(1) = 1, b(2n) = b(n), b(2n+1) = b(n-1) + b(n) + b(n+1) (entry formula; it
  is the expansion of x Π_{k>=0} (1 + x^(2^k) + x^(2^(k+1)) + x^(2^(k+2)))).
* A002487 (Stern's diatomic sequence): s(0) = 0, s(1) = 1, s(2n) = s(n), s(2n+1) = s(n) + s(n+1).
Checked numerically for m < 40000.
-/

namespace OMA.S_oeis_a070875

/-- A309019. -/
def b (m : ℕ) : ℕ :=
  if h : m < 2 then m
  else if m % 2 = 0 then b (m / 2)
  else b (m / 2 - 1) + b (m / 2) + b (m / 2 + 1)
termination_by m
decreasing_by all_goals omega

/-- Stern's diatomic sequence A002487. -/
def stern (m : ℕ) : ℕ :=
  if h : m < 2 then m
  else if m % 2 = 0 then stern (m / 2)
  else stern (m / 2) + stern (m / 2 + 1)
termination_by m
decreasing_by all_goals omega

/-- `m` is a term of A070875: binary expansion 1x100…0. -/
def IsTerm (m : ℕ) : Prop := ∃ k : ℕ, m = 5 * 2 ^ k ∨ m = 7 * 2 ^ k

theorem main : ∀ m : ℕ, (b m : ℤ) - stern m = 1 ↔ IsTerm m := by
  sorry

end OMA.S_oeis_a070875

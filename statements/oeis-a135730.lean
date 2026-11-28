import Mathlib

/-!
# A135730: Number of steps to reach the minimum of the final cycle under iterations of the map A001281: x->3x-1 if x odd, x/2 otherwise.

Source: https://oeis.org/A135730
Credit: @Solfanbtc

Claim (entry comment, N. J. A. Sloane, Sep 04 2015; the 3x-1 problem in the odd-number form of
A261671): the trajectory of any odd number eventually reaches 1, 9 or 33, and so enters one of
the loops (1, 3), (9, 27, 13, 39, 19) or (33, 99, 49, ..., 135, 67).

The map (A261671), on odd x: subtract 1 and divide by 2; if the result is odd, that is the next
term, otherwise the next term is 3x. So h(x) = (x-1)/2 when (x-1)/2 is odd, and h(x) = 3x
otherwise; it maps odd numbers to odd numbers. "Odd number" means a positive odd integer
(x : ℕ odd). Reaching at time 0 counts, as in the sequence (a(1) = 0 for x = 1). A python check:
the number of steps from 2n-1 to the first of 1, 9, 33 reproduces all 80 listed terms of A135730,
and every odd x < 2·10^5 reaches {1, 9, 33}.
-/

namespace OMA.S_oeis_a135730

/-- The map of A261671 on odd numbers. -/
def h (x : ℕ) : ℕ := if ((x - 1) / 2) % 2 = 1 then (x - 1) / 2 else 3 * x

theorem main : ∀ x : ℕ, Odd x → ∃ k : ℕ, h^[k] x = 1 ∨ h^[k] x = 9 ∨ h^[k] x = 33 := by
  sorry

end OMA.S_oeis_a135730

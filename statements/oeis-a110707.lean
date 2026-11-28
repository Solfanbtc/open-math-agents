import Mathlib

/-!
# A110707: Number of linear arrangements of n blue, n red and n green items such that there are no adjacent items of the same color (first and last elements considered as adjacent).

Source: https://oeis.org/A110707
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jul 26 2014):
  n^2*a(n) - 3*n*(2*n-1)*a(n-1) - 3*(n-1)*(5*n-12)*a(n-2) - 8*(n-3)^2*a(n-3) = 0.

Definitions.
* An arrangement is a word `f : Fin (3n) → Fin 3` (colours 0, 1, 2) using each colour exactly
  `n` times; it is counted when no two cyclically adjacent positions (`i` and `i + 1 mod 3n`,
  so the last and the first are adjacent) have the same colour. This reproduces the data
  6, 24, 132, 804, ... (`#eval` for n ≤ 3, python3 brute force for n ≤ 11).
* Range: the offset is 1 and the recurrence uses a(n-3), so it is stated for n ≥ 4 (it also
  holds at n = 3, where the coefficient (n-3)^2 vanishes). Arithmetic in `ℤ`.
* python3: with a(n) = 2*A000172(n-1) + 2*A000172(n) (Mark van Hoeij's formula in the entry,
  which reproduces the 20 data terms), the recurrence holds for 4 ≤ n < 200.
-/

namespace OMA.S_oeis_a110707

/-- A110707(n): cyclic-adjacency-free words with `n` letters of each of 3 colours. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (3 * n) → Fin 3)).filter fun f =>
    (∀ c : Fin 3, (Finset.univ.filter fun i => f i = c).card = n) ∧
      ∀ i : Fin (3 * n), f i ≠ f ⟨(i.val + 1) % (3 * n), Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩).card

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) ^ 2 * a n - 3 * n * (2 * n - 1) * a (n - 1)
        - 3 * ((n : ℤ) - 1) * (5 * n - 12) * a (n - 2) - 8 * ((n : ℤ) - 3) ^ 2 * a (n - 3)) = 0 := by
  sorry

end OMA.S_oeis_a110707

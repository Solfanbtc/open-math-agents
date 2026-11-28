import Mathlib

/-!
# A078132: Primes which can be written as sum of cubes > 1.

Source: https://oeis.org/A078132
Credit: @Solfanbtc

The entry quotes H. Mikawa and T. Peneva (Sums of five cubes of primes in short intervals):
"One of the famous and still unsettled problems in additive prime number theory is the
conjecture that every sufficiently large integer satisfying some natural congruence conditions,
can be written as the sum of four cubes of primes."

"Natural congruence conditions" is read as the absence of a local obstruction (the usual
convention for the Waring–Goldbach problem). For every modulus `q ≥ 1`, `n` must be a sum of
four cubes of units modulo `q`, as `p1^3 + ⋯ + p4^3` is for large primes `p_i ∤ q`.
Check of this reading: with five cubes it gives exactly the conditions quoted for Hua's
five-cube result (`n` odd, `n ≢ 0, ±2 (mod 9)`, `n ≢ 0 (mod 7)`). For four cubes it amounts to
`n` even, `n ≢ ±1, ±3 (mod 9)` and `n ≢ ±1 (mod 7)`. Python3, over moduli up to 49: the only
obstructions come from 2, 9 and 7, and moduli 4, 8, 16, 27 and 49 add none.

`main`: there is `N` such that every integer `n ≥ N` with no local obstruction is
`p1^3 + p2^3 + p3^3 + p4^3` for some primes `p1, …, p4`. This is open; Hua proved the
analogue with nine cubes of primes for all large odd integers.
-/

namespace OMA.S_oeis_a078132

/-- `n` is a sum of four cubes of units modulo every `q ≥ 1` (no local obstruction). -/
def NoLocalObstruction (n : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → ∃ x : Fin 4 → ZMod q, (∀ i, IsUnit (x i)) ∧ ∑ i, x i ^ 3 = (n : ZMod q)

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → NoLocalObstruction n →
      ∃ p : Fin 4 → ℕ, (∀ i, (p i).Prime) ∧ n = ∑ i, p i ^ 3 := by
  sorry

end OMA.S_oeis_a078132

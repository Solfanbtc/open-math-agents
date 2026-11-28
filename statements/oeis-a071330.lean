import Mathlib

/-!
# A071330: Number of decompositions of n into sum of two prime powers.

Source: https://oeis.org/A071330
Credit: @Solfanbtc

`a(n)` (offset 1) counts the unordered decompositions `n = x + y`, `x ≤ y`, with `x` and `y`
prime powers in the sense of A000961, which counts `1 = p⁰` as a prime power (examples:
`10 = 1 + 3² = 2 + 2³ = 3 + 7 = 5 + 5`, so `a(10) = 4`; `12 = 1 + 11 = ...`; the PARI program uses
`omega(n) == 1 || n == 1`). So `a(n) = #{x : 1 ≤ x ≤ n/2, x and n - x prime powers}`.

The entry states `a(2n) > 0`, labelled "(Goldbach's conjecture)": every even positive integer is
a sum of two such prime powers. We state exactly this claim (for every `n ≥ 1`, the offset of the
sequence). It follows from Goldbach's conjecture (and `2 = 1 + 1`), but with `1` and higher prime
powers allowed it is weaker than Goldbach; it is open as far as we know.

A line-by-line python3 mirror of `a` reproduces all 95 OEIS data terms
(`0,1,1,2,2,3,2,3,3,4,...`), gives `a(149) = 0` as in the example, and `a(2n) > 0` for `n < 20000`.
`n - x` never truncates since `x ≤ n / 2`.
-/

namespace OMA.S_oeis_a071330

/-- Prime power in the sense of A000961: `1` or `p ^ k` with `p` prime, `k ≥ 1`. -/
def IsPP (k : ℕ) : Prop := k = 1 ∨ IsPrimePow k

instance : DecidablePred IsPP := fun k => inferInstanceAs (Decidable (k = 1 ∨ IsPrimePow k))

/-- `A071330(n)`: number of `x` with `1 ≤ x ≤ n / 2` such that `x` and `n - x` are prime powers. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 (n / 2)).filter fun x => IsPP x ∧ IsPP (n - x)).card

/-- `a(2n) > 0` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a (2 * n) := by
  sorry

end OMA.S_oeis_a071330

import Mathlib

/-!
# A124690: Position of the first n in the decimal expansion of Pi^n, or -1 if the digits of n never appear.

Source: https://oeis.org/A124690
Credit: @Solfanbtc

Conjecture (Cino Hilliard, OEIS A124690, %C line): `-1` only occurs in the first entry of the
sequence, i.e. for every `n ≥ 1` the digits of `n` appear in the decimal expansion of `π^n`.
(`a(0) = -1`: `π^0 = 1` has no digit 0.)

Formalization.
* `L` is the number of decimal digits of `n` (`n ≥ 1`, so its leading digit is nonzero).
* As in the entry's PARI program, which searches the string of `π^n` (with its decimal point),
  an occurrence lies either within the integer part, a block of `L` consecutive digits of
  `⌊π^n⌋`: `⌊π^n⌋ / 10^i ≡ n (mod 10^L)` for some `i`; or within the fractional part, the `L`
  digits ending at the `j`-th digit after the point with `j ≥ L`:
  `⌊π^n 10^j⌋ ≡ n (mod 10^L)`. (A block straddling the decimal point is not a match.) Since the
  leading digit of `n` is nonzero, a congruence of this kind can only be met by actual digits,
  not by leading zeros.

Checked with python3 (3000 digits of `π^n`): these positions reproduce all listed %S/%T/%U terms
(`n ≤ 79`, all found within the first 420 positions).
-/

namespace OMA.S_oeis_a124690

/-- For every `n ≥ 1`, the decimal digits of `n` occur in the decimal expansion of `π^n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    let L := (Nat.digits 10 n).length
    (∃ i : ℕ, ⌊Real.pi ^ n⌋₊ / 10 ^ i % 10 ^ L = n) ∨
      (∃ j : ℕ, L ≤ j ∧ ⌊Real.pi ^ n * 10 ^ j⌋₊ % 10 ^ L = n) := by
  sorry

end OMA.S_oeis_a124690

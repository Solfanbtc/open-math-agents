import Mathlib

/-!
# A030700: Decimal expansion of 3^n contains no zeros (probably finite).

Source: https://oeis.org/A030700
Credit: @Solfanbtc

A030700 lists the `n` such that the decimal expansion of `3ⁿ` contains no zero digit:
`0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 19, 23, 24, 26, 27, 28, 31, 34, 68` (the full data;
the name says the sequence is probably finite).

Conjecture (the entry): `3⁶⁸ = 278128389443693511257285776231761` is the largest power of 3 that
does not contain a zero. Stated as: `68` is the greatest `k` such that `0` is not a decimal digit
of `3ᵏ` (in the same form as the statements for the other digits of powers of 3, A131613 ff.).

A python3 check: `3⁶⁸` is the printed number and has no zero digit, and every `3ᵏ` with
`68 < k < 20000` contains a zero.

Conventions: decimal digits are `Nat.digits 10` (no leading zeros).
-/

namespace OMA.S_oeis_a030700

/-- Conjecture: `3⁶⁸` is the largest power of 3 with no zero digit. -/
theorem main : IsGreatest {k : ℕ | 0 ∉ Nat.digits 10 (3 ^ k)} 68 := by
  sorry

end OMA.S_oeis_a030700

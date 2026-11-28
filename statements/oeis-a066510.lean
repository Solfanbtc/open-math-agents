import Mathlib

/-!
# A066510: positive numbers not of the form r^i - s^j (conjectured list)

Source: https://oeis.org/A066510
Credit: @Solfanbtc

A066510 is the "conjectured list of positive numbers which are not of the form r^i-s^j, where
r,s,i,j are integers with i>1, j>1": 6, 14, 34, 42, 58, ..., 450, 454 (51 terms shown).
"This is a famous hard problem and the terms shown are only conjectured values." `r` and `s` may
be negative (the entry's examples include `50 = 7^2 - (-1)^3` and `246 = 11^2 - (-5)^3`).
D. Reble and M. Fiorentini checked that the terms shown are not differences of two powers below
`10^19`, resp. `10^27`.

Conjecture (the entry): the list is correct, i.e. the positive integers up to the last shown
term 454 that are not of the form `r^i - s^j` are exactly the 51 listed numbers. (The direction
"every unlisted number in that range is such a difference" is witnessed by explicit
representations; the conjectural content is that the listed numbers have none.)

Sanity check (python): using all powers `r^i` with `|r^i| ≤ 10^12`, every unlisted `m ≤ 454` is
such a difference and no listed one is.
-/

namespace OMA.S_oeis_a066510

/-- `m` is a difference `r^i - s^j` of two integer powers with exponents `i, j ≥ 2`. -/
def IsPowerDifference (m : ℤ) : Prop :=
  ∃ (r s : ℤ) (i j : ℕ), 2 ≤ i ∧ 2 ≤ j ∧ m = r ^ i - s ^ j

/-- The 51 listed terms of A066510. -/
def listed : Finset ℕ :=
  {6, 14, 34, 42, 58, 62, 66, 70, 78, 86, 90, 102, 110, 114, 130, 158, 178, 182, 202, 210,
   230, 238, 254, 258, 266, 274, 278, 302, 306, 310, 314, 322, 326, 330, 358, 374, 378,
   390, 394, 398, 402, 410, 418, 422, 426, 430, 434, 438, 446, 450, 454}

/-- The conjectured list is correct up to 454. -/
theorem main :
    {m : ℕ | 1 ≤ m ∧ m ≤ 454 ∧ ¬ IsPowerDifference m} = (listed : Set ℕ) := by
  sorry

end OMA.S_oeis_a066510

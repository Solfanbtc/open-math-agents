import Mathlib

/-!
# A071825: Largest prime factor 4k+3 count minus largest prime factor 4k+1 count, up to n.

Source: https://oeis.org/A071825
Credit: @Solfanbtc

`a(n) = #{x ≤ n : P(x) ≡ 3 (mod 4)} - #{x ≤ n : P(x) ≡ 1 (mod 4)}` for `n ≥ 1`, where
`P(x) = A006530(x)` is the largest prime factor of `x` (`x = 1`, with no prime factor, counts in
neither set). Data: `0, 0, 1, 1, 0, 1, 2, 2, 3, 2, ...`.

Conjectures (Benoit Cloitre, in the entry): weak: the sequence gives positive values only;
strong: for `n` large enough, `a(n) > 2 √n`.

Minimal fix, explained: the weak conjecture fails literally at the first values,
`a(1) = a(2) = a(5) = 0` (all in the data); it is stated for `n ≥ 6`.
Both conjectures are stated, as a conjunction.

A python3 check (sieve to `2·10^7`): `a(n) ≤ 0` only for `n ∈ {1, 2, 5}`; `a(n) ≤ 2 √n` last
happens at `n = 485`; `a(2·10^7) = 163535`.

Conventions: `P(x)` is `x.primeFactors.sup id` (`0` for `x = 1`, which has residue `0 mod 4`).
-/

namespace OMA.S_oeis_a071825

open Filter

/-- The largest prime factor of `x` (`0` if `x = 1`). -/
def P (x : ℕ) : ℕ := x.primeFactors.sup id

/-- `a(n) = #{x ≤ n : P(x) ≡ 3 mod 4} - #{x ≤ n : P(x) ≡ 1 mod 4}`. -/
def a (n : ℕ) : ℤ :=
  (((Finset.Icc 1 n).filter fun x => P x % 4 = 3).card : ℤ) -
    (((Finset.Icc 1 n).filter fun x => P x % 4 = 1).card : ℤ)

/-- Cloitre's conjectures: `a(n) > 0` for `n ≥ 6`, and `a(n) > 2 √n` for all large `n`. -/
theorem main : (∀ n : ℕ, 6 ≤ n → 0 < a n) ∧
    (∀ᶠ n : ℕ in atTop, 2 * Real.sqrt n < (a n : ℝ)) := by
  sorry

end OMA.S_oeis_a071825

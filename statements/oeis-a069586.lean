import Mathlib

/-!
# A069586: Smallest prime power p^k (k >= 2) such that there is a difference of exactly n between p^k and some other prime power q^m (m >= 2)

Source: https://oeis.org/A069586
Credit: @Solfanbtc

Full name: smallest prime power `p^k` (`k ≥ 2`) such that there is a difference of exactly `n`
between `p^k` and some other prime power `q^m` (`m ≥ 2`); or `0` if no such `q^m` exists.

Claim (OEIS entry, %C, Michel Marcus 2023): "The nonzero terms are sure terms, only the zero terms
are conjectured" (Larry Reeves: any solution for the zero terms is `> 10^14`). We state, with the
same strength as the data, that all 85 listed terms (%S, %T, %U) are correct; the open content is
that for each `n` with listed value `0` no two prime powers with exponents `≥ 2` differ by `n`.

Conventions:
* A prime power with exponent `≥ 2` is `p^k` with `p` prime and `k ≥ 2` (A025475 without 1).
* If `x` and `y` are such prime powers with `|x - y| = n > 0`, then the smaller one is again a
  candidate, so `a(n)` is the least `x` such that `x` and `x + n` are both such prime powers
  (this is how the entry's PARI program computes it). If no such `x` exists, `a(n) = 0`, which is
  exactly the value of `sInf ∅` in `ℕ`.
* Checked in Python with all prime powers up to `10^9`: this reproduces all 85 listed terms.
-/

namespace OMA.S_oeis_a069586

/-- `x = p^k` for a prime `p` and `k ≥ 2`. -/
def IsHighPrimePow (x : ℕ) : Prop := ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ x = p ^ k

/-- `a(n)`: the least `x` with `x` and `x + n` prime powers with exponent `≥ 2`, or `0` if none. -/
noncomputable def a (n : ℕ) : ℕ := sInf {x | IsHighPrimePow x ∧ IsHighPrimePow (x + n)}

/-- All 85 listed terms of A069586 are correct (in particular the zero terms). -/
theorem main :
    (List.range 85).map (fun i => a (i + 1)) =
      [8, 25, 125, 4, 4, 0, 9, 8, 16, 2187, 16, 4, 243, 0, 49, 9, 8, 9, 8, 0, 4, 27, 4, 8, 0, 0, 0,
        4, 0, 6859, 0, 32, 16, 0, 0, 0, 27, 1331, 25, 9, 8, 0, 0, 81, 4, 243, 81, 16, 32, 0, 0, 0,
        0, 27, 9, 8, 64, 0, 0, 4, 64, 0, 961, 64, 16, 0, 0, 0, 0, 0, 0, 9, 8, 169, 0, 49, 4, 0, 49,
        0, 0, 0, 0, 0, 0] := by
  sorry

end OMA.S_oeis_a069586

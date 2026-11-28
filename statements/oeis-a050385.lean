import Mathlib

/-!
# A050385: Reversion of Moebius function A008683.

Source: https://oeis.org/A050385
Credit: @Solfanbtc

`A050385(n)` is the coefficient of `x^n` in the compositional inverse (reversion) `A(x)` of the
Möbius series `M(x) = ∑_{k ≥ 1} μ(k) x^k`, i.e. the power series with `A(0) = 0` and
`M(A(x)) = x`: `1, 1, 3, 10, 39, 160, 691, ...` (offset 1).

Conjecture (David W. Wilson, May 17 2017, as recorded in the entry): `A050385(n)` equals the number
of ways to partition `ℤ` into `n` residue classes, for every `n ≥ 1` (e.g. `a(4) = 10`).

Status: REFUTED. The entry says (Jeffrey Shallit, Nov 19 2017) that the conjecture fails at `a(13)`;
the correct statement, proved by Goulden, Granville, Richmond and Shallit ("Natural exact covering
systems and the reversion of the Möbius series", Ramanujan J. 50 (2019) 211-235,
arXiv:1711.04109), counts only *natural* exact covering systems. The conjecture is stated here
exactly as Wilson wrote it, so that it can be disproved. A python3 check (exact covers by
backtracking, reversion by the coefficient recurrence) gives `1, 1, 3, 10, 39, 160` for both sides
at `n = 1, ..., 6`.

Conventions:
* A residue class `r (mod m)` is a pair `(m, r) : ℕ × ℕ` with `0 < m` and `r < m`, standing for
  `{x : ℤ | x ≡ r [ZMOD m]}`; distinct such pairs are distinct classes. A partition of `ℤ` into
  `n` residue classes is an (unordered) set of `n` such classes, every integer lying in exactly
  one of them (Wilson's 10 partitions for `n = 4` are unordered).
* The reversion is characterized rather than constructed: for every power series `A` over `ℤ` with
  zero constant term and `M.subst A = X` (i.e. `M(A(x)) = x`; such `A` exists and is unique,
  `PowerSeries.substInv`), the coefficients of `A` are the claimed counts.
-/

namespace OMA.S_oeis_a050385

/-- The Möbius series `M(x) = ∑_{k ≥ 1} μ(k) x^k` (`μ 0 = 0` in Mathlib). -/
noncomputable def M : PowerSeries ℤ := PowerSeries.mk fun k => ArithmeticFunction.moebius k

/-- Sets of `n` residue classes `r (mod m)` (`0 < m`, `r < m`) partitioning `ℤ`. -/
def partitions (n : ℕ) : Set (Finset (ℕ × ℕ)) :=
  {S | S.card = n ∧ (∀ c ∈ S, 0 < c.1 ∧ c.2 < c.1) ∧
    ∀ x : ℤ, ∃! c, c ∈ S ∧ x ≡ (c.2 : ℤ) [ZMOD (c.1 : ℤ)]}

/-- Wilson's conjecture (refuted at `n = 13`): the number of partitions of `ℤ` into `n` residue
classes is the `n`-th coefficient of the reversion of the Möbius series, for all `n ≥ 1`. -/
theorem main : ∀ A : PowerSeries ℤ, PowerSeries.constantCoeff A = 0 →
    M.subst A = PowerSeries.X →
    ∀ n : ℕ, 1 ≤ n → ((partitions n).ncard : ℤ) = PowerSeries.coeff n A := by
  sorry

end OMA.S_oeis_a050385

import Mathlib

/-!
# A007491: Smallest prime > n^2.

Source: https://oeis.org/A007491
Credit: @Solfanbtc

The entry lists conjectures of Jaroslav Krizek (Apr 02 2016):
1. there is always a prime between `n^2` and `n^2 + n`;
2. `a(n) < n^2 + n`;
3. for every `k ≥ 1` there is a smallest number `m > 2(k+1)` such that for all `n ≥ m` there is
   always a prime `p` between `n^2` and `n^2 + n - 2k`; the sequence of these `m` for `k ≥ 1` is
   `6, 8, 12, 13, 14, 24, 24, 24, 30, 30, 30, 31, 33, 35, 43, ...`, and `lim_{k→∞} m/(2k) = 1`.

Conjectures 1 and 2 (and Legendre's conjecture `a(n) < (n+1)^2`, also mentioned) are already
stated upstream: `Oppermann.oppermann_conjecture.parts.ii` (for `n ≥ 2`; at `n = 1` there is
no prime in `(1, 2)`) and `LegendreConjecture`. This file states conjecture 3 in full: the
existence of `m` for every `k ≥ 1`, the fifteen listed values, and the limit.

"Between" is read strictly, `n^2 < p < n^2 + n - 2k`. For `n > 2k` the upper end
`n^2 + n - 2k` is even and greater than 2, so it is never prime, and the strict and inclusive
readings agree. A python check of all `n ≤ 20000` gives exactly the listed values for
`k = 1, …, 15` (then `45, 47, 47, 47, 50` for `k = 16, …, 20`), and `m/(2k)` equal to
`1.135, 1.034, 1.020, 1.008` for `k = 100, 500, 1000, 3000`.

Since `n ≥ m > 2(k+1)`, the natural-number subtraction in `n^2 + n - 2k` never truncates.
The property "for all `n ≥ m` there is a prime" is upward closed in `m`, so `m k` below, the
infimum of the admissible `m`, is the smallest one as soon as one exists.
-/

namespace OMA.S_oeis_a007491

open Filter

/-- For every `n ≥ m` there is a prime `p` with `n^2 < p < n^2 + n - 2k`. -/
def PrimeAfterSquares (k m : ℕ) : Prop :=
  ∀ n ≥ m, ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < n ^ 2 + n - 2 * k

/-- Krizek's `m(k)`: the smallest `m > 2(k+1)` such that `PrimeAfterSquares k m`. -/
noncomputable def m (k : ℕ) : ℕ :=
  sInf {m : ℕ | 2 * (k + 1) < m ∧ PrimeAfterSquares k m}

/-- Krizek's conjecture 3 on A007491. -/
theorem main :
    (∀ k ≥ 1, ∃ m₀ : ℕ, 2 * (k + 1) < m₀ ∧ PrimeAfterSquares k m₀) ∧
    (∀ i : Fin 15, m ((i : ℕ) + 1) = ![6, 8, 12, 13, 14, 24, 24, 24, 30, 30, 30, 31, 33, 35, 43] i) ∧
    Tendsto (fun k : ℕ => (m k : ℝ) / (2 * k)) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a007491

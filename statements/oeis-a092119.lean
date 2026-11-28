import Mathlib

/-!
# A092119: Euler transform of the ruler sequence A001511

Source: https://oeis.org/A092119 (with https://oeis.org/A173238)
`a = A092119` is the Euler transform of the ruler sequence `b(k) = A001511(k) = ν₂(k) + 1`:
`a(0) = 1` and `n a(n) = ∑_{k=1}^{n} c(k) a(n-k)` with `c(k) = ∑_{d ∣ k} d b(d)` (the Euler
transform as defined in Sloane's transforms.txt). Data: 1, 1, 3, 4, 10, 13, 26, 35, 66, ...

The entry's comment (Gary W. Adamson, Feb 13 2010): "Let M = triangle A173238 as an infinite
lower triangular matrix. Then A092119 = lim_{n->infinity} M^n. Let P(x) = polcoeff A000041 =
(1 + x + 2x^2 + 3x^3 + ...), and A(x) = polcoeff A092119. Then P(x) = A(x) / A(x^2), an example of
a conjectured infinite set of operations (cf. A173238)."

We state both claims, as a conjunction:
1. `M` is the matrix of A173238, `M i j = p(i - 2j)` for `2j ≤ i` and `0` otherwise
   (`p = A000041`, the partition numbers). Being lower triangular, its powers are well defined,
   and the limit is entrywise (A173238: "Lim_{n->inf} M^n = (1, 1, 3, 4, 10, 13, 26, ...)", the
   vector read down the columns): for every `i`, the entry `(M^n) i 0` is eventually `a(i)`.
   `col n i` below is `(M^n) i 0`, computed as `M^(n+1) e₀ = M (M^n e₀)`.
2. `P(x) = A(x) / A(x^2)`, stated as `P(x) * A(x^2) = A(x)` (equivalent, since `A(x^2)` has
   constant term 1, hence is invertible).

Status: the identity `P(x) = A(x)/A(x^t)` for the Euler transform of the `t`-ary ruler function
was proved by Helmut Prodinger (Feb 2010, communicated in A173238). Claim 2 is that proof's case
`t = 2`; it is stated here faithfully anyway.

Checked with python3: the recurrence gives all 42 listed terms, claim 2 holds for the
coefficients of `x^0..x^41`, and `(M^n) i 0 = a(i)` for all `i ≤ 41` once `n ≥ 6`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a092119

/-- A000041: the number of partitions of `n`. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- A001511, the ruler function: `ν₂(k) + 1`. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The auxiliary sequence of the Euler transform of `ruler`. -/
def c (k : ℕ) : ℕ := ∑ d ∈ k.divisors, d * ruler d

/-- The list `[a 0, ..., a n]` of the Euler transform of `ruler`. -/
def aList : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
    aList n ++ [(∑ k ∈ Finset.Icc 1 (n + 1), c k * (aList n).getD (n + 1 - k) 0) / (n + 1)]

/-- A092119, the Euler transform of the ruler sequence A001511. -/
def a (n : ℕ) : ℕ := (aList n).getD n 0

/-- The triangle A173238 as an infinite lower triangular matrix. -/
def M (i j : ℕ) : ℕ := if 2 * j ≤ i then p (i - 2 * j) else 0

/-- `col n i` is the entry `(M^n) i 0`. -/
def col : ℕ → ℕ → ℕ
  | 0, i => if i = 0 then 1 else 0
  | n + 1, i => ∑ j ∈ Finset.range (i + 1), M i j * col n j

theorem main :
    (∀ i : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → col n i = a i) ∧
    PowerSeries.mk (fun n => p n) * PowerSeries.mk (fun n => if 2 ∣ n then a (n / 2) else 0) =
      PowerSeries.mk (fun n => a n) := by
  sorry

end OMA.S_oeis_a092119

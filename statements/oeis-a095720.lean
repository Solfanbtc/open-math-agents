import Mathlib

/-!
# A095720: a(1)=1 and, for n>1, a(n)=a(n-1)+Floor(3n/4) if n is even, else a(n)=smallest positive integer which has not yet appeared in the sequence.

Source: https://oeis.org/A095720
Credit: @Solfanbtc

Conjecture (J. W. Layman, OEIS %C): for even `n`, the ratio `a(n)/a(n-1)` is asymptotic to 2
as `n` becomes large (at `n = 3000` the ratio is 2.0004446). Stated as
`a(2m+2) / a(2m+1) → 2` as `m → ∞`.

Discrepancy between the name and the data. With `Floor(3n/4)` the recursion gives
`a(2) = 1 + 1 = 2`, but the OEIS data has `a(2) = 3` (also `a(10) = 15`, `a(34) = 51`, ...).
All 71 listed terms are reproduced exactly when `Floor(3n/4)` is replaced by `3n/4` rounded to
the nearest integer with ties to even (Mathematica's `Round`, presumably what produced the data
and the ratio quoted in the comment; `Floor` reproduces only part of it). We therefore follow the
data and use round-half-to-even, `roundHalfEven34 n`. (Both variants give the ratio
2.000444... at `n = 3000`.) The definitions below were checked in Lean (`decide`) to give
the first 20 listed terms.
The smallest positive integer which has not yet appeared among `a(1), ..., a(n-1)`: this lies
in `1, ..., n`, so `firstMissing` searches `List.range (l.length + 2)`.
-/

namespace OMA.S_oeis_a095720

/-- `3n/4` rounded to the nearest integer, ties to even. -/
def roundHalfEven34 (n : ℕ) : ℕ :=
  let q := 3 * n / 4
  let r := 3 * n % 4
  if r = 3 ∨ (r = 2 ∧ q % 2 = 1) then q + 1 else q

/-- The smallest positive integer not in `l`. -/
def firstMissing (l : List ℕ) : ℕ :=
  ((List.range (l.length + 2)).filter (fun v => 0 < v ∧ v ∉ l)).headD 0

/-- `terms k = [a(k+1), a(k), ..., a(1)]`, most recent first. -/
def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 =>
    let l := terms k
    (if (k + 2) % 2 = 0 then l.headD 0 + roundHalfEven34 (k + 2) else firstMissing l) :: l

/-- `a n` is A095720(n) for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (terms (n - 1)).headD 0

theorem main :
    Filter.Tendsto (fun m : ℕ => (a (2 * m + 2) : ℝ) / (a (2 * m + 1) : ℝ)) Filter.atTop
      (nhds 2) := by
  sorry

end OMA.S_oeis_a095720

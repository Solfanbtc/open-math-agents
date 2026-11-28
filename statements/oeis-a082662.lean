import Mathlib

/-!
# A082662: odd part of k less than sqrt(2k) iff the widths of the symmetric representation of sigma(k) are unimodal

Source: https://oeis.org/A082662
Credit: @Solfanbtc

A082662 lists the numbers `k` such that the odd part of `k` (A000265) is less than `sqrt(2k)`
(property (P1) of the entry). The entry states:

  (P9) These are the numbers k such that the sequence of successive widths in the symmetric
  representation of sigma(k) is unimodal.
  "A further equivalent property, (P9), follows at once from (P4). This was conjectured by
  Omar E. Pol, Apr 18 2017."

So the entry presents (P9) as a conjecture of O. E. Pol that follows from its theorem (P1) ⟺ (P4);
`main` states (P1) ⟺ (P9) for every `k ≥ 1` (the sequence has offset 1).

The successive widths of the symmetric representation of sigma(n) form row `n` of A249351
(length `2n - 1`). We build them with the explicit OEIS formulas:
* `A003056(n)`: the largest `r` with `r(r+1)/2 ≤ n`.
* A237048: for `1 ≤ i ≤ A003056(n)`, `T(n,i) = 1` if `i ∣ n - i(i+1)/2`, else `0`.
* A249223: the width on the `k`-th leg is `W(n,k) = Sum_{i=1..k} (-1)^(i+1) T(n,i)`.
* A235791: `S(n,k) = Sum_{j=1..n} T(j,k)` (with `T(j,k) = 0` when `k(k+1)/2 > j`);
  A237591: the `k`-th leg has length `S(n,k) - S(n,k+1)`, for `1 ≤ k ≤ A003056(n)`.
* The first `n` widths repeat `W(n,k)` along leg `k`; row `n` of A249351 is these `n` widths
  followed by the mirror image of the first `n - 1` of them.
Checked with python3: this reproduces all 100 listed terms of A249351, and (P1) ⟺ (P9) holds
for `1 ≤ k < 3000` (covering all listed terms of A082662). "Unimodal" is read in the weak sense
(weakly increasing, then weakly decreasing), since the rows contain long runs of equal widths.
-/

namespace OMA.S_oeis_a082662

/-- `A003056(n)`: the largest `r` with `r(r+1)/2 ≤ n`. -/
def rowLen (n : ℕ) : ℕ := ((List.range (n + 1)).filter (fun r => r * (r + 1) / 2 ≤ n)).length - 1

/-- A237048 `T(n,i)`: `1` if `i ≥ 1`, `i(i+1)/2 ≤ n` and `i ∣ n - i(i+1)/2`, else `0`. -/
def t (n i : ℕ) : ℤ :=
  if 1 ≤ i ∧ i * (i + 1) / 2 ≤ n ∧ i ∣ n - i * (i + 1) / 2 then 1 else 0

/-- A249223: the width on the `k`-th leg, `Sum_{i=1..k} (-1)^(i+1) T(n,i)`. -/
def width (n k : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 k, (-1) ^ (i + 1) * t n i

/-- A235791 `S(n,k) = Sum_{j=1..n} T(j,k)`. -/
def s (n k : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 n, t j k

/-- A237591: the length of the `k`-th leg, `S(n,k) - S(n,k+1)`. -/
def leg (n k : ℕ) : ℕ := (s n k - s n (k + 1)).toNat

/-- The first `n` successive widths: `W(n,k)` repeated along the `k`-th leg. -/
def halfWidths (n : ℕ) : List ℤ :=
  (List.range' 1 (rowLen n)).flatMap (fun k => List.replicate (leg n k) (width n k))

/-- Row `n` of A249351: the `2n - 1` successive widths of the symmetric representation of
sigma(n). -/
def widths (n : ℕ) : List ℤ := halfWidths n ++ (halfWidths n).dropLast.reverse

/-- A list is unimodal: weakly increasing up to some point, weakly decreasing after it. -/
def Unimodal (l : List ℤ) : Prop :=
  ∃ m ≤ l.length, (l.take m).Pairwise (· ≤ ·) ∧ (l.drop m).Pairwise (· ≥ ·)

/-- The odd part of `k` (A000265). -/
def oddPart (k : ℕ) : ℕ := k / 2 ^ (k.factorization 2)

/-- (P1) ⟺ (P9): the odd part of `k` is less than `sqrt(2k)` iff the successive widths of the
symmetric representation of sigma(k) are unimodal. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    ((oddPart k : ℝ) < Real.sqrt (2 * k) ↔ Unimodal (widths k)) := by
  sorry

end OMA.S_oeis_a082662

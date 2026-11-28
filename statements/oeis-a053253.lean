import Mathlib

/-!
# A053253: Coefficients of the '3rd-order' mock theta function omega(q).

Source: https://oeis.org/A053253
Credit: @Solfanbtc

The entry records two conjectures about a(n), the coefficient of q^n in
omega(q) = Sum_{k>=0} q^(2k(k+1)) / ((1-q)(1-q^3)...(1-q^(2k+1)))^2:
1. (John M. Campbell, Apr 24 2020, "Empirical"; Gus Wiseman, Jun 26 2022, calls it Campbell's
   conjecture) a(n) is the number of integer partitions mu of 2n+1 whose diagram has an odd
   number of cells in each row and in each column, i.e. all parts of mu and all parts of the
   conjugate of mu are odd.
2. (Peter Bala, Nov 18 2024, "Conjectural g.f.") the generating function is also
   1/(1-x) * (1 + Sum_{k>=0} x^(3k+1) / ((1-x)(1-x^3)...(1-x^(2k+1)))).
`main` is the conjunction of 1 and 2, for every n ≥ 0.

Conventions:
* `oddParts m M` is the number of partitions of `m` into odd parts `≤ M`; it is the coefficient
  of x^m in 1/((1-x)(1-x^3)...(1-x^M)) for odd M. Expanding the k-th summand of omega(q) gives
  `a n = Σ_{k, 2k(k+1) ≤ n} Σ_{i+j = n-2k(k+1)} oddParts i (2k+1) * oddParts j (2k+1)`; the
  index k is bounded by `n` since `2k(k+1) ≤ n` forces `k ≤ n`.
* The parts of the conjugate of mu are the column lengths #{parts of mu ≥ j}, for
  1 ≤ j ≤ (largest part); "each column odd" is stated as: for every `j ≥ 1`, the number of
  parts `≥ j` is `0` or odd.
* Bala's series: the coefficient of x^i in the bracket is `[i = 0] + Σ_{k, 3k+1 ≤ i}
  oddParts (i-3k-1) (2k+1)`, and the factor 1/(1-x) takes partial sums over `i ≤ n`.
* Checked in Python: `a` reproduces every term of %S, %T, %U (n ≤ 49); Campbell's count agrees
  for n ≤ 17 and Bala's coefficients for n < 200.
-/

namespace OMA.S_oeis_a053253

/-- Number of partitions of `m` into odd parts, each at most `M`. -/
def oddParts (m M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition m)).filter fun μ =>
    ∀ i ∈ μ.parts, Odd i ∧ i ≤ M).card

/-- A053253: coefficient of `q^n` in Ramanujan's mock theta function `omega(q)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * k * (k + 1) ≤ n),
    ∑ i ∈ Finset.range (n - 2 * k * (k + 1) + 1),
      oddParts i (2 * k + 1) * oddParts (n - 2 * k * (k + 1) - i) (2 * k + 1)

/-- Partitions of `2n+1` with every part odd and every part of the conjugate odd. -/
def campbell (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition (2 * n + 1))).filter fun μ =>
    (∀ i ∈ μ.parts, Odd i) ∧
      ∀ j ∈ Finset.Icc 1 (2 * n + 1),
        (μ.parts.filter (j ≤ ·)).card = 0 ∨ Odd (μ.parts.filter (j ≤ ·)).card).card

/-- Coefficient of `x^n` in Bala's conjectural generating function. -/
def bala (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1),
    ((if i = 0 then 1 else 0) +
      ∑ k ∈ (Finset.range (i + 1)).filter (fun k => 3 * k + 1 ≤ i),
        oddParts (i - (3 * k + 1)) (2 * k + 1))

/-- Campbell's conjecture and Bala's conjectural generating function for `omega(q)`. -/
theorem main : (∀ n : ℕ, a n = campbell n) ∧ (∀ n : ℕ, a n = bala n) := by
  sorry

end OMA.S_oeis_a053253

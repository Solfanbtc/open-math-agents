import Mathlib

/-!
# A000185: a(n) = A058087(n,n-5).

Source: https://oeis.org/A000185
Credit: @Solfanbtc

A000185 is a diagonal of A058087: `a(n) = T(n, n-5)` (offset 5), the coefficient of `t^5` in the
ménage hit polynomial (Kaplansky and Riordan, as in A058087)
`U_n(t) = Sum_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`.
Since `[t^5] (t-1)^k = binomial(k, 5) * (-1)^(k-5)`, this gives the explicit sum `a` below.
Checked with python3: it gives `2, 24, 140, 1232, 11268, ...`, all 19 listed terms (n = 5..23);
a brute-force count of permutations of n with exactly 5 ménage hits (`p(i) ≡ i` or `i+1 mod n`)
agrees for n = 5..9.

The entry states two conjectures (R. J. Mathar, Nov 02 2015), both linear recurrences:
1. an order-6 recurrence (involving a(n-6)); with offset 5 it is stated for n ≥ 11, where all
   indices are in the domain;
2. an order-4 recurrence (involving a(n-4)); stated for n ≥ 9.
Both checked numerically for all n up to 59. (They also hold from n = 6, resp. n = 5, when
a(n) = 0 for n < 5, which is what the formula gives; the statement uses the in-domain ranges.)

`main` is the conjunction of the two conjectures.
-/

namespace OMA.S_oeis_a000185

/-- A000185(n): the coefficient of `t^5` in the ménage hit polynomial
`U_n(t) = Sum_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1) ^ (k - 5) * (k.choose 5 : ℚ) * ((2 * n : ℚ) / (2 * n - k)) * ((2 * n - k).choose k : ℚ) *
      ((n - k).factorial : ℚ)

theorem main :
    (∀ n : ℕ, 11 ≤ n →
      let m : ℚ := n
      4 * (210968408 * m ^ 2 - 1603518486 * m + 2343057493) * a n
      + (-843873632 * m ^ 3 - 4039256254 * m ^ 2 + 144382575631 * m - 553812368850) * a (n - 1)
      + (10453330198 * m ^ 3 - 175111274403 * m ^ 2 + 798927275864 * m - 639098546595) * a (n - 2)
      + (10059264970 * m ^ 3 - 98879552663 * m ^ 2 + 170576803994 * m - 134993524720) * a (n - 3)
      + (470894110 * m ^ 3 - 5178116941 * m ^ 2 + 108179055193 * m - 215961878286) * a (n - 4)
      + (1708832970 * m ^ 3 - 29554327949 * m ^ 2 + 137453332457 * m - 152801514054) * a (n - 5)
      + 3 * (569610990 * m ^ 2 - 3742686463 * m + 4740040723) * a (n - 6) = 0) ∧
    (∀ n : ℕ, 9 ≤ n →
      let m : ℚ := n
      (241 * m - 1066) * (2 * m - 11) * (-5 + m) ^ 2 * a n
      + (-482 * m ^ 5 + 10099 * m ^ 4 - 79756 * m ^ 3 + 285961 * m ^ 2 - 426904 * m + 149292)
          * a (n - 1)
      - (2 * m - 9) * (m - 3) * (248 * m ^ 3 - 2229 * m ^ 2 + 5065 * m - 7134) * a (n - 2)
      + (-14 * m ^ 5 - 49 * m ^ 4 - 619 * m ^ 3 + 13174 * m ^ 2 - 51690 * m + 61248) * a (n - 3)
      - (m - 3) * (m - 4) * (7 * m - 87) * (2 * m - 7) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a000185

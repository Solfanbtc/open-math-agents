import Mathlib

/-!
# A008780: a(n) = (n-dimensional partitions of 6) + C(n,4) + C(n,3).

Source: https://oeis.org/A008780
Credit: @Solfanbtc

A008780 lists the values at `m = 6` of MacMahon's (incorrect) conjectured formula for the number
of `d`-dimensional partitions of `m`. The entry's comment (Michel Marcus, Aug 16 2013) says:
"for n=6, MacMahon's formula coincides for d < 3 with the first three terms of A042984",
where A042984 is the number of `d`-dimensional partitions of 6 (offset 0: 1, 11, 48, 140, ...).

Formalized:
* `macMahon d` is the `d`-th term of A008780, given by the formula of the entry
  (`%p`/`%t` lines, binomial transform of row 6 of A116672):
  `1 + 10 d + 27 C(d,2) + 29 C(d,3) + 12 C(d,4) + C(d,5)`.
  For `d ≥ 1` this equals the coefficient of `x^6` in MacMahon's generating function
  `∏_{k ≥ 1} (1 - x^k)^(-C(k+d-2, d-1))` (checked numerically for `d = 1..7`); for `d = 0` it
  is `1`. Values: 1, 11, 48, 141, 331, 672, ... (the entry's data).
* A `d`-dimensional partition of `6`, in the OEIS convention of A042984 (1-dimensional =
  ordinary partitions, 2-dimensional = plane partitions), is a finitely supported array
  `f : (Fin d → ℕ) →₀ ℕ`, weakly decreasing in every coordinate (`Antitone` for the product
  order), whose entries sum to `6`. For `d = 0` there is one such array (the single entry 6).
  Brute force gives 1, 11, 48, 140 for `d = 0, 1, 2, 3`.

`main` states the comment's claim: for every `d < 3`, MacMahon's value equals the number of
`d`-dimensional partitions of 6. (At `d = 3` it fails: 141 vs 140.)
-/

namespace OMA.S_oeis_a008780

/-- A008780(d): MacMahon's conjectured number of `d`-dimensional partitions of 6. -/
def macMahon (d : ℕ) : ℕ :=
  1 + 10 * d + 27 * d.choose 2 + 29 * d.choose 3 + 12 * d.choose 4 + d.choose 5

/-- The set of `d`-dimensional partitions of `m`: finitely supported arrays indexed by `ℕ^d`,
weakly decreasing in each coordinate, with entries summing to `m`. -/
def dimPartitions (d m : ℕ) : Set ((Fin d → ℕ) →₀ ℕ) :=
  {f | Antitone ⇑f ∧ (f.sum fun _ v => v) = m}

theorem main : ∀ d : ℕ, d < 3 → macMahon d = (dimPartitions d 6).ncard := by
  sorry

end OMA.S_oeis_a008780

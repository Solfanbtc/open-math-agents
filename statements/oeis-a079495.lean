import Mathlib

/-!
# A079495: Numbers k such that the sum of the squares of the digits of k in base 3 is 0 (mod 3).

Source: https://oeis.org/A079495
Credit: @Solfanbtc

Conjecture (OEIS A079495): "In base 2 this gives the Evil Numbers (cf. A001969) and slope 2. One
may conjecture that in base b the asymptotic slope will be b and might suspect asymptotic density
1/b for each result (mod b)."

`main` states the density form for every base b >= 2 and every residue r < b: the set of k >= 0
whose base-b digit-square sum is ≡ r (mod b) has natural density 1/b, i.e. the proportion of such
k below N tends to 1/b. For r = 0 this is the claimed asymptotic slope b (the n-th such k is
~ b n, equivalent to density 1/b). For b = 3, r = 0 it is the statement about A079495.
Digits are those of `Nat.digits b k` (k = 0 has digit-square sum 0).
Checked numerically for k < 10^6 and 2 <= b <= 10: all proportions are within 17% of 1/b,
within 0.3% for prime b (the entry warns that nonprime b shows larger variations).
-/

namespace OMA.S_oeis_a079495

open Filter

/-- Sum of the squares of the base-`b` digits of `k`. -/
def digitSqSum (b k : ℕ) : ℕ := ((Nat.digits b k).map fun d => d ^ 2).sum

theorem main : ∀ b : ℕ, 2 ≤ b → ∀ r : ℕ, r < b →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun k => digitSqSum b k % b = r).card : ℝ) / N)
      atTop (nhds (1 / (b : ℝ))) := by
  sorry

end OMA.S_oeis_a079495

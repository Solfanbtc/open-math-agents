import Mathlib

/-!
# A080333: Partial sums of A080278.

Source: https://oeis.org/A080333
Credit: @Solfanbtc

Conjecture (Klaus Brockhaus, Mar 23 2003, OEIS A080333): a(n) is asymptotic to n log(n) / log(3).
Status: the entry notes that this follows from the asymptotics of A333979 (Pontus von Brömssen,
Sep 06 2020); A080278 also records Sum_{k<=n} A080278(k) ~ n log_3(n) + O(n) (Amiram Eldar). It
is a known result, stated faithfully.

Definitions: A080278(n) = (3^(v_3(n) + 1) - 1)/2 for n >= 1, where v_3 is the 3-adic valuation
(`padicValNat 3`); a(n) = Σ_{k=1..n} A080278(k) (offset 1: 1, 2, 6, 7, 8, 12, ...).
"Asymptotic to" means a(n) / (n log n / log 3) → 1.
-/

namespace OMA.S_oeis_a080333

open Filter

/-- A080278(n) = (3^(v_3(n)+1) - 1)/2. -/
def A080278 (n : ℕ) : ℕ := (3 ^ (padicValNat 3 n + 1) - 1) / 2

/-- a(n) = Σ_{k=1..n} A080278(k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A080278 k

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) * Real.log n / Real.log 3)) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a080333

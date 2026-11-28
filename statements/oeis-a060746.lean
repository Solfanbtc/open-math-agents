import Mathlib

/-!
# A060746: Numerator of the non-Euler-constant term of the Laurent expansion of Gamma at s = -n

Source: https://oeis.org/A060746
Credit: @Solfanbtc

At `s = -n` (`n ≥ 0`) the Gamma function has a simple pole with residue `(-1)^n/n!`; the constant
term of its Laurent expansion has the form `r + q γ` (`γ` the Euler–Mascheroni constant), e.g.
`Γ(s) = (1/24)(s+4)^(-1) + (25/288 - γ/24) + O(s+4)` at `s = -4`; `a(n)` (offset 0) is the absolute
value of the numerator of the rational, non-Euler-constant part `r`: `0, 1, 3, 11, 25, 137, …`.
The coefficient of `γ` is `q = (-1)^(n+1)/n!` (as in the entry's examples); with it fixed, `r` is
determined by the constant term (no irrationality of `γ` is needed). Below, the constant term is the
limit of `Γ(s) - (-1)^n/(n! (s+n))` as `s → -n`, `s ≠ -n`.

Conjectures recorded in the entry, stated as the parts of `main`:
1. (Vladeta Jovovic, May 20 2004) `a(n) = lcm(Wolstenholme(n), n!)/n!`. Here "Wolstenholme(n)" is
   the numerator of the harmonic number `H(n)` (A001008; with A007406, the numerator of
   `∑ 1/k^2`, the formula fails already at `n = 4`: `205 ≠ 25`); this reading reproduces all 31
   data terms. (Luschny's "equivalent conjecture" `a(n) = num(H(n)/(n-1)!)` is not stated
   separately.)
2. (Gary Detlefs, Sep 09 2010) for `n ≥ 2`, `a(n)` is the numerator of `H(n)/((n-1)! H(n-1))`.
Status: PROVED. Natalia L. Skirrow (Jun 07 2026, OEIS formula) shows "both conjectures are true",
via the reflection formula: the constant term is `(-1)^n (H(n) - γ)/n!`.
-/

namespace OMA.S_oeis_a060746

open Filter Topology

/-- Jovovic's and Detlefs' formulas for the numerator of the rational part `r` of the constant
term of the Laurent expansion of `Γ` at `-n`. -/
theorem main : ∀ n : ℕ, ∃ r : ℚ,
    Tendsto (fun s : ℝ => Real.Gamma s - (-1) ^ n / ((n.factorial : ℝ) * (s + n)))
      (𝓝[≠] (-(n : ℝ)))
      (𝓝 ((r : ℝ) + (-1) ^ (n + 1) / (n.factorial : ℝ) * Real.eulerMascheroniConstant)) ∧
    r.num.natAbs = Nat.lcm (harmonic n).num.natAbs n.factorial / n.factorial ∧
    (2 ≤ n → r.num.natAbs =
      (harmonic n / ((n - 1).factorial * harmonic (n - 1))).num.natAbs) := by
  sorry

end OMA.S_oeis_a060746

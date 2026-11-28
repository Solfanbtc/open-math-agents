import Mathlib

/-!
# A121082: primitive solutions of a^2 + b^2 = c^2 - 1 with c ≤ 10^n have density 1/8

Source: https://oeis.org/A121082
`a(n)` (offset 1) is the number of primitive Pythagorean-like triples `a^2 + b^2 = c^2 + k` for
`k = -1` with `c ≤ 10^n`: 2, 14, 126, 1238, 12517, 124973, ... (`a(1) = 2`, from `(2,2,3)` and
`(4,8,9)`). Conjecture of the entry (Tito Piezas III): `a(n)/10^n → 1/8` as `n → ∞`.

Conventions. Triples are counted with `1 ≤ a ≤ b` (unordered, as in the example: `(2,2,3)` is
counted once), and `c ≥ 1`. Primitive means `gcd(a, b, c) = 1`; this is automatic here, since a
common divisor `d` would give `d^2 ∣ c^2 - a^2 - b^2 = 1`, but it is kept to match the name.
`a = 0` never occurs (`c^2 - 1` is a square only for `c = 1`, giving `b = 0`), and `a, b < c`,
so the search box `[1, 10^n]^3` loses nothing.
Checked with python3: this count gives `a(1..3) = 2, 14, 126`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a121082

open Filter Topology

/-- A121082: the number of `(a, b, c)` with `1 ≤ a ≤ b`, `c ≤ 10^n`, `gcd(a,b,c) = 1` and
`a^2 + b^2 = c^2 - 1`. -/
def A (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (10 ^ n) ×ˢ Finset.Icc 1 (10 ^ n) ×ˢ Finset.Icc 1 (10 ^ n)).filter
    (fun t => t.1 ≤ t.2.1 ∧ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 ∧
      t.1 ^ 2 + t.2.1 ^ 2 + 1 = t.2.2 ^ 2)).card

theorem main :
    Tendsto (fun n : ℕ => (A n : ℝ) / (10 : ℝ) ^ n) atTop (𝓝 (1 / 8)) := by
  sorry

end OMA.S_oeis_a121082

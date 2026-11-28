import Mathlib

/-!
# A121087: Number of primitive Pythagorean-like triples a^2+b^2=c^2+k for k=-5 with 0<c<=10^n.

Source: https://oeis.org/A121087
Credit: @Solfanbtc

Claim (entry comment, conjectured by Tito Piezas III): a(n)/10^n → 1/(2√5) = 0.22360... as n → ∞.

Conventions. a(n) counts triples (a, b, c) of positive integers with a ≤ b (unordered pairs),
a^2 + b^2 = c^2 - 5, 0 < c ≤ 10^n and gcd(a, b, c) = 1 ("primitive"). The gcd condition is
automatic here (a common divisor d gives d^2 ∣ 5), but it is kept as in the name. This matches
the entry: a(1) = 1, from (2, 4, 5) only, and a brute-force python count with exactly these
conditions gives 1, 22, 223, 2217 for n = 1..4, the first four listed terms (the entry's
Mathematica program also counts unordered representations of c^2 - 5 with both squares
positive). The offset is 1; the limit statement does not depend on that.
-/

namespace OMA.S_oeis_a121087

/-- A121087(n): primitive triples with 1 ≤ a ≤ b, a^2 + b^2 + 5 = c^2, 1 ≤ c ≤ 10^n
(necessarily a, b < c ≤ 10^n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (10 ^ n) ×ˢ Finset.Icc 1 (10 ^ n) ×ˢ Finset.Icc 1 (10 ^ n)).filter
    fun t : ℕ × ℕ × ℕ =>
      t.1 ≤ t.2.1 ∧ t.1 ^ 2 + t.2.1 ^ 2 + 5 = t.2.2 ^ 2 ∧
        Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / 10 ^ n) Filter.atTop
      (nhds (1 / (2 * Real.sqrt 5))) := by
  sorry

end OMA.S_oeis_a121087

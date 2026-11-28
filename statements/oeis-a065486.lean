import Mathlib

/-!
# A065486: Decimal expansion of Product_{p prime} (1 + 1/(p+1)^2).

Source: https://oeis.org/A065486
Credit: @Solfanbtc

The constant c = Product_{p prime} (1 + 1/(p+1)^2) = 1.2665584156... is "the constant c in the
conjectured formula Sum_{a,b <= x} f(a,b) ~ c * x^2, where f(a, b) = gcd(ab, a + b)/gcd(a, b)
(Tóth, 2026, p. 5, eq. (11))" (Amiram Eldar, in the entry). Stated: that conjectured formula.

Conventions.
* a, b range over positive integers ≤ x; f(a,b) = gcd(ab, a+b)/gcd(a,b) is an integer (gcd(a,b)
  divides both ab and a+b, hence their gcd). It is enough to let x run over the natural numbers
  (the sum only changes at integers, and (⌊x⌋/x)^2 → 1).
* The product converges absolutely (Σ 1/(p+1)^2 < ∞); it is `tprod` over `Nat.Primes`.
  "~ c x^2" (c > 0) is stated as Sum / x^2 → c.
* python3: the product over p < 10^6 is 1.26655841...; Sum/x^2 = 1.2489, 1.2535, 1.2573 for
  x = 500, 1000, 2000 (slowly increasing towards c).
-/

namespace OMA.S_oeis_a065486

/-- f(a, b) = gcd(ab, a+b) / gcd(a, b). -/
def f (a b : ℕ) : ℕ := Nat.gcd (a * b) (a + b) / Nat.gcd a b

/-- Σ_{1 ≤ a, b ≤ x} f(a, b). -/
def S (x : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x, f a b

/-- c = ∏_p (1 + 1/(p+1)^2). -/
noncomputable def c : ℝ := ∏' p : Nat.Primes, (1 + 1 / ((p : ℝ) + 1) ^ 2)

theorem main :
    Filter.Tendsto (fun x : ℕ => (S x : ℝ) / (x : ℝ) ^ 2) Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a065486

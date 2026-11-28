import Mathlib

/-!
# A123725: Numerators of fractional partial quotients appearing in a continued fraction for the power series Sum_{n>=0} x^(2^n - 1)/(n+1)^s.

Source: https://oeis.org/A123725
Credit: @Solfanbtc

Conjecture (Paul D. Hanna, example section): Z(x,s) = Sum_{n>=0} x^(2^n-1)/(n+1)^s "may be
expressed by the continued fraction Z(x,s) = [1; f(1)^s/x, -f(2)^s/x, -f(3)^s/x, ...,
f(n)^s*(-1)^e(n)/x, ...] such that the (2^n-1)-th convergent = Sum_{k=0..n} x^(2^k-1)/(k+1)^s,
where f(n) = (b(n)+2)/(b(n)+1)^2 and e(n) = A073089(n+1) for n>=1, and b(n) = A007814(n)";
this is shown for s = 1, 2, 3, and "It is conjectured that these patterns continue for all s."

Formalization.
* `b n = A007814(n)`, the 2-adic valuation; `e n = A073089(n)` (offset 1) by its recurrence:
  a(1) = a(4m+2) = a(8m+7) = a(16m+13) = 0, a(4m) = a(8m+3) = a(16m+5) = 1, a(8m+1) = a(4m+1).
  (This reproduces the data of A073089, and the numerators (b(n)+2)(-1)^e(n+1) reproduce the
  data of A123725; python3.)
* The continued fraction [b_0; b_1, b_2, ...] = b_0 + 1/(b_1 + 1/(b_2 + ...)) with b_0 = 1 and
  b_m = (-1)^e(m+1) f(m)^s / x, in the field `ℚ(x)` of rational functions; its m-th convergent
  is h_m / k_m with h_(-1) = 1, h_0 = 1, k_(-1) = 0, k_0 = 1, h_m = b_m h_(m-1) + h_(m-2),
  k_m = b_m k_(m-1) + k_(m-2).
* Statement: for every positive integer s and every n ≥ 0 the (2^n - 1)-th convergent equals
  Sum_{k=0..n} x^(2^k-1)/(k+1)^s in `ℚ(x)`. (s ranges over the positive integers, as in the
  examples s = 1, 2, 3.)
python3 (exact rationals at x = 3/7, -5/2, 11/13): holds for 1 ≤ s ≤ 6 and n ≤ 6. (The displayed
expansion for s = 2 shows +(16/81)/x at position 20 where the formula and the case s = 1 give
a minus sign; the formula, which is what the conjecture asserts, is the one used here.)
-/

namespace OMA.S_oeis_a123725

/-- A073089(n), offset 1, by its recurrence. -/
def e (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else if n % 4 = 2 ∨ n % 8 = 7 ∨ n % 16 = 13 then 0
  else if n % 4 = 0 ∨ n % 8 = 3 ∨ n % 16 = 5 then 1
  else e ((n - 1) / 2 + 1)
termination_by n
decreasing_by omega

/-- The partial quotient b_m (m ≥ 1) for the exponent `s`. -/
noncomputable def q (s m : ℕ) : RatFunc ℚ :=
  algebraMap ℚ (RatFunc ℚ)
      ((-1) ^ e (m + 1) * (((padicValNat 2 m : ℚ) + 2) / ((padicValNat 2 m : ℚ) + 1) ^ 2) ^ s) /
    RatFunc.X

/-- `(h_(m-1), h_m, k_(m-1), k_m)` for the continued fraction [1; b_1, b_2, ...]. -/
noncomputable def hk (s : ℕ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ × RatFunc ℚ
  | 0 => (1, 1, 0, 1)
  | m + 1 =>
    let t := hk s m
    (t.2.1, q s (m + 1) * t.2.1 + t.1, t.2.2.2, q s (m + 1) * t.2.2.2 + t.2.2.1)

/-- The m-th convergent h_m / k_m. -/
noncomputable def convergent (s m : ℕ) : RatFunc ℚ := (hk s m).2.1 / (hk s m).2.2.2

theorem main :
    ∀ s : ℕ, 1 ≤ s → ∀ n : ℕ,
      convergent s (2 ^ n - 1) =
        ∑ k ∈ Finset.range (n + 1),
          RatFunc.X ^ (2 ^ k - 1) / algebraMap ℚ (RatFunc ℚ) (((k : ℚ) + 1) ^ s) := by
  sorry

end OMA.S_oeis_a123725

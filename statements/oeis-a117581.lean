import Mathlib

/-!
# A117581: For each successive prime p, the largest integer n such that both n and n-1 factor into primes less than or equal to p.

Source: https://oeis.org/A117581
Credit: @Solfanbtc

Claim (Lucas A. Brown, Oct 16 2022): "An effective abc conjecture (c < rad(abc)^2) would imply
that a(21) = 2286831727304145 and a(22) = ... = a(26) = 9591468737351909376 and
a(27) = ... = a(32) = 19316158377073923834001 and a(33) = 124225935845233319439174."

Formalization.
* `a n` (offset 1): with `p` the n-th prime, the largest `m` such that `m` and `m - 1` have all
  their prime factors `≤ p` (finite by Størmer's theorem; `sSup` of that set). The pair
  (m, m-1) = (2, 1) shows the set is nonempty.
* The effective abc conjecture: for all coprime positive integers `a, b` with `c = a + b`,
  `c < rad(abc)^2`, where `rad` is the product of the distinct prime factors.
* Statement: the effective abc conjecture implies all the listed values (a(21), a(22..26),
  a(27..32), a(33)).
Sanity check (python3): each listed value m and m - 1 are p-smooth for the corresponding prime p
(e.g. the largest prime factor occurring for a(33) is 137 = p_33), and the values for
n = 21..27 agree with the data of the entry (extended from A002072).
-/

namespace OMA.S_oeis_a117581

/-- All prime factors of `m` are at most `p`. -/
def Smooth (p m : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ m → q ≤ p

/-- A117581(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m : ℕ | 2 ≤ m ∧ Smooth (Nat.nth Nat.Prime (n - 1)) m ∧
    Smooth (Nat.nth Nat.Prime (n - 1)) (m - 1)}

/-- The radical: product of the distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ q ∈ n.primeFactors, q

/-- The effective abc conjecture `c < rad(abc)^2`. -/
def EffectiveABC : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y → x + y < rad (x * y * (x + y)) ^ 2

theorem main :
    EffectiveABC →
      a 21 = 2286831727304145 ∧
      (∀ n : ℕ, 22 ≤ n → n ≤ 26 → a n = 9591468737351909376) ∧
      (∀ n : ℕ, 27 ≤ n → n ≤ 32 → a n = 19316158377073923834001) ∧
      a 33 = 124225935845233319439174 := by
  sorry

end OMA.S_oeis_a117581

import Mathlib

/-!
# A057778: a(n) is the least odd k such that k*2^n + 1 is prime.

Source: https://oeis.org/A057778
Credit: @Solfanbtc

Two conjectures of Thomas Ordowski in the entry; `main` is their conjunction:
1. (Apr 13 2019) for n > 0, a(n) = k < 2^n, so k*2^n + 1 is a Proth prime (A080076);
2. (Oct 16 2014) a(n) = O(n*log(n)).

Conventions.
* a(n) = least odd k with k·2^n + 1 prime (offset 0); such k exist by Dirichlet's theorem
  (the entry also notes a(n) << 19^n via Linnik's theorem), so `sInf` is the minimum.
  Data: 1, 1, 1, 5, 1, 3, 3, 5, 1, 15, ...
* Conjecture 2 is `Asymptotics.IsBigO` along n → ∞ of a(n) against n·log n.
-/

namespace OMA.S_oeis_a057778

/-- A057778: least odd k with k·2^n + 1 prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | Odd k ∧ (k * 2 ^ n + 1).Prime}

theorem main :
    (∀ n : ℕ, 0 < n → a n < 2 ^ n) ∧
    (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a057778

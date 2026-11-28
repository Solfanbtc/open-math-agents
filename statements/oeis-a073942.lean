import Mathlib

/-!
# A073942: Numbers k such that A002977(k) - A002977(k-1) = 1.

Source: https://oeis.org/A073942
Credit: @Solfanbtc

Conjecture (OEIS A073942): a(n) is asymptotic to c n, where c is around 3.8...

Reading: a(n)/n converges to a positive constant c. The value "around 3.8..." is only a numerical
estimate, not a precise claim, so c is existentially quantified. (Numerically a(n)/n = 4.03, 4.07,
4.08, 4.09 at n = 10^3, 10^4, 10^5, 393724, still slowly increasing.)

Definitions. A002977 is the Klarner-Rado sequence: the increasing enumeration of the least set S of
positive integers with 1 ∈ S and m ∈ S → 2m + 1 ∈ S and 3m + 1 ∈ S (offset 1: 1, 3, 4, 7, 9, 10,
...); A002977(k) is `Nat.nth` of S at k - 1. a(n) is the n-th k >= 2 with
A002977(k) - A002977(k-1) = 1 (offset 1: 3, 6, 11, 13, ...).
-/

namespace OMA.S_oeis_a073942

open Filter

/-- Membership in the Klarner-Rado set: the least set containing 1 and closed under
`m ↦ 2m + 1`, `m ↦ 3m + 1`. -/
def InKR (x : ℕ) : Prop :=
  ∀ S : Set ℕ, 1 ∈ S → (∀ m ∈ S, 2 * m + 1 ∈ S ∧ 3 * m + 1 ∈ S) → x ∈ S

/-- A002977(k), for k ≥ 1. -/
noncomputable def kr (k : ℕ) : ℕ := Nat.nth InKR (k - 1)

/-- `k ≥ 2` with `A002977(k) - A002977(k-1) = 1`. -/
def IsTerm (k : ℕ) : Prop := 2 ≤ k ∧ kr k = kr (k - 1) + 1

/-- a(n), the n-th such k (n ≥ 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

theorem main : ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds c) := by
  sorry

end OMA.S_oeis_a073942

import Mathlib

/-!
# A078719: Number of odd terms in the Collatz trajectory of n until it reaches 1.

Source: https://oeis.org/A078719
Credit: @Solfanbtc

a(n) = number of odd terms among n, f(n), f(f(n)), ..., 1 for the Collatz function
f(n) = n/2 (n even), 3n + 1 (n odd), counted until reaching 1 for the first time, or -1 if 1 is
never reached (offset 1).

Conjecture (in the entry): there are no fixed points (a(n) = n) other than 1, 3 and 41.
Stated as: for n ≥ 1, a(n) = n iff n ∈ {1, 3, 41}.

Conventions.
* If the trajectory of n never reaches 1 then a(n) = -1 ≠ n, so "a(n) = n" means: some iterate
  f^[k](n) equals 1 and, with K the least such k, the number of i ≤ K with f^[i](n) odd is n.
* python3: for 1 ≤ n < 10^6 the fixed points are exactly 1, 3, 41.
-/

namespace OMA.S_oeis_a078719

/-- The Collatz function. -/
def f (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- First time the trajectory of n reaches 1 (meaningful when it does). -/
noncomputable def firstOne (n : ℕ) : ℕ := sInf {k : ℕ | f^[k] n = 1}

/-- Number of odd terms among f^[0] n, ..., f^[firstOne n] n. -/
noncomputable def oddCount (n : ℕ) : ℕ :=
  ((Finset.range (firstOne n + 1)).filter (fun i => f^[i] n % 2 = 1)).card

/-- a(n) = n (A078719 has a fixed point at n). -/
def IsFixed (n : ℕ) : Prop := (∃ k : ℕ, f^[k] n = 1) ∧ oddCount n = n

theorem main : ∀ n : ℕ, 1 ≤ n → (IsFixed n ↔ n = 1 ∨ n = 3 ∨ n = 41) := by
  sorry

end OMA.S_oeis_a078719

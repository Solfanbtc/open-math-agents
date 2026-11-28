import Mathlib

/-!
# A088126: Let f(n, x) = x+3x^2+6x^3+...+(n(n+1)/2)x^n; then a(n) = least x such that f(n, x) is a triangular number, or 0 if no such x exists.

Source: https://oeis.org/A088126
Credit: @Solfanbtc

`f(n, x) = Σ_{k=1..n} (k(k+1)/2) x^k`; `x` ranges over positive integers (`x = 0` would give the
triangular number 0). `m` is triangular when `m = k(k+1)/2` for some `k` (necessarily `k ≤ m`).
The data %S, %T, %U lists a(1..104): a(1) = 1, a(2) = 18, a(3) = 1, a(8) = 1, a(20) = 1,
a(34) = 1, and a(n) = 0 for all other `n ≤ 104` (we checked the nonzero values by computer).

The entry says the zero values are conjectures (D. Wasserman searched a(4) up to x = 10^7,
a(5) up to 10^6 and the others up to 10^4). `main` states all listed terms: for `n ≤ 104`
with a listed nonzero value `v`, `v` is the least `x ≥ 1` with `f(n, x)` triangular, and for
the other `n ≤ 104`, `f(n, x)` is triangular for no `x ≥ 1`.
-/

namespace OMA.S_oeis_a088126

/-- `f(n, x) = x + 3x^2 + 6x^3 + ... + (n(n+1)/2) x^n`. -/
def f (n x : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, k * (k + 1) / 2 * x ^ k

/-- `m` is a triangular number. -/
def IsTriangular (m : ℕ) : Prop := ∃ k ≤ m, 2 * m = k * (k + 1)

/-- The listed nonzero terms. -/
def listed : ℕ → ℕ
  | 1 => 1
  | 2 => 18
  | 3 => 1
  | 8 => 1
  | 20 => 1
  | 34 => 1
  | _ => 0

/-- The terms a(1..104) of the entry, zero values included. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 104 →
    (listed n ≠ 0 → IsLeast {x : ℕ | 1 ≤ x ∧ IsTriangular (f n x)} (listed n)) ∧
    (listed n = 0 → ∀ x : ℕ, 1 ≤ x → ¬ IsTriangular (f n x)) := by
  sorry

end OMA.S_oeis_a088126

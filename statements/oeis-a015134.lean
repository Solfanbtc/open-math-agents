import Mathlib

/-!
# A015134: number of cycles of Fibonacci-type sequences mod n; Bartell's and Nutt's conjectures

Source: https://oeis.org/A015134
Credit: @Solfanbtc

A015134 (offset 1): consider the Fibonacci-type sequences `b(0) = X`, `b(1) = Y`,
`b(k) = b(k-1) + b(k-2) mod n`; all are periodic, and `a(n)` is the number of distinct periods,
i.e. of distinct cycles of the map `T(x, y) = (y, x + y)` on `(ℤ/n)^2` (data 1, 2, 2, 4, 3, 4,
…; e.g. `a(2) = 2`: the fixed point `(0,0)` and one cycle of length 3). `T` is a bijection of a
finite set, so every point is periodic, and the number of cycles is
`Sum_{s} 1/(minimal period of s)`; this is our definition (`Fin n` with its addition mod `n`).

The entry's conjectures, all stated in `main` (as a conjunction, in the order of the entry):
* S. Bartell, Aug 20 2023: `a(3·2^n) = 3(3·2^n - 14)` (n ≥ 3); `a(3^n) = (3^n + 1)/2` (n ≥ 0);
  `a(2·3^n) = 2(3^n - 1)` (n ≥ 1); `a(5·3^n) = (3^(n+2) - 3)/2` (n ≥ 0);
  `a(10·3^n) = 6(3^(n+1) - 5)` (n ≥ 1); `a(5^n) = (5^n + 1)/2`; `a(2·5^n) = 5^n + 1`;
  `a(3·5^n) = (5^(n+1) - 1)/2`; `a(4·5^n) = 3·5^n + 1`; `a(6·5^n) = 5^(n+1) - 1`;
  `a(7^n) = (7^n + 1)/2`; `a(2·7^n) = 7^n + 1` (all n ≥ 0).
* S. Bartell, Aug 16 2024: `a(11^n) = (6·11^n - 1)/5 + n`; `a(13^n) = (13^n + 1)/2`;
  `a(17^n) = (17^n + 1)/2`; `a(19^n) = (10·19^n - 1)/9 + n`; `a(23^n) = (23^n + 1)/2`;
  `a(29^n) = (15·29^n - 8)/7 + 2n` (all n ≥ 0); for a prime `p` not in A053032,
  `a(p^n) = 1 + (p+1)(p^n - 1)/A001175(p)` (except for `p = 5`); for a prime `p` in A053032,
  `a(p^n) = 1 + ((p+1)(p^n - 1) + n(p-1))/A001175(p)`. Here A001175(p) is the Pisano period
  (the minimal period of `(0, 1)` under `T` mod `p`), and A053032 is the set of odd primes `p`
  with exactly one zero among `F_0, …, F_{A001175(p)-1}` mod `p`. The second family is read for
  all `n ≥ 0`, like the explicit cases it generalizes.
* E. Nutt, Dec 24 2025: `a(n) ≥ (n+1)/2` (n ≥ 1).

All values and divisions are taken in `ℚ`, so each formula claims in particular that its right
side is the integer `a(n)`. Checked with python3: the definition reproduces the first 38 terms;
each explicit formula holds on the ranges tested (up to `3·2^8`, `3^7`, `2·3^6`, `5·3^5`,
`10·3^4`, `5^4`, `2·5^3`, …, `7^4`, `11^3`, `13^2`, …, `29^2`); the two general formulas hold for
every prime `p < 60` (`p ≠ 5`) and `n ≤ 2` (`n ≤ 1` for `p > 45`); Nutt's bound holds for
`1 ≤ n < 250`. (For `p = 5` the general formula fails, e.g. at `n = 1`, which is why the source
excludes it.)
-/

namespace OMA.S_oeis_a015134

/-- The Fibonacci step `T(x, y) = (y, x + y)` mod `n`. -/
def T (n : ℕ) (s : Fin n × Fin n) : Fin n × Fin n := (s.2, s.1 + s.2)

/-- A015134: the number of cycles of `T` on `(ℤ/n)^2`, as `Sum_s 1/(minimal period of s)`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∑ s : Fin n × Fin n, 1 / (Function.minimalPeriod (T n) s : ℚ)

/-- A001175: the Pisano period of `p` (for `p ≥ 2`). -/
noncomputable def pisano (p : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ p ∣ Nat.fib k ∧ p ∣ Nat.fib (k + 1) - 1}

/-- A053032: `p` is an odd prime with exactly one zero among `F_0, …, F_{π(p)-1}` mod `p`. -/
def InA053032 (p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ ((Finset.range (pisano p)).filter (fun k => p ∣ Nat.fib k)).card = 1

/-- The conjectures of Bartell (2023, 2024) and Nutt (2025) recorded in A015134. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a (3 * 2 ^ n) = 3 * (3 * 2 ^ n - 14)) ∧
    (∀ n : ℕ, a (3 ^ n) = (3 ^ n + 1) / 2) ∧
    (∀ n : ℕ, 1 ≤ n → a (2 * 3 ^ n) = 2 * (3 ^ n - 1)) ∧
    (∀ n : ℕ, a (5 * 3 ^ n) = (3 ^ (n + 2) - 3) / 2) ∧
    (∀ n : ℕ, 1 ≤ n → a (10 * 3 ^ n) = 6 * (3 ^ (n + 1) - 5)) ∧
    (∀ n : ℕ, a (5 ^ n) = (5 ^ n + 1) / 2) ∧
    (∀ n : ℕ, a (2 * 5 ^ n) = 5 ^ n + 1) ∧
    (∀ n : ℕ, a (3 * 5 ^ n) = (5 ^ (n + 1) - 1) / 2) ∧
    (∀ n : ℕ, a (4 * 5 ^ n) = 3 * 5 ^ n + 1) ∧
    (∀ n : ℕ, a (6 * 5 ^ n) = 5 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, a (7 ^ n) = (7 ^ n + 1) / 2) ∧
    (∀ n : ℕ, a (2 * 7 ^ n) = 7 ^ n + 1) ∧
    (∀ n : ℕ, a (11 ^ n) = (6 * 11 ^ n - 1) / 5 + n) ∧
    (∀ n : ℕ, a (13 ^ n) = (13 ^ n + 1) / 2) ∧
    (∀ n : ℕ, a (17 ^ n) = (17 ^ n + 1) / 2) ∧
    (∀ n : ℕ, a (19 ^ n) = (10 * 19 ^ n - 1) / 9 + n) ∧
    (∀ n : ℕ, a (23 ^ n) = (23 ^ n + 1) / 2) ∧
    (∀ n : ℕ, a (29 ^ n) = (15 * 29 ^ n - 8) / 7 + 2 * n) ∧
    (∀ p n : ℕ, p.Prime → p ≠ 5 → ¬ InA053032 p →
      a (p ^ n) = 1 + ((p + 1) * ((p : ℚ) ^ n - 1)) / pisano p) ∧
    (∀ p n : ℕ, InA053032 p →
      a (p ^ n) = 1 + ((p + 1) * ((p : ℚ) ^ n - 1) + n * (p - 1)) / pisano p) ∧
    (∀ n : ℕ, 1 ≤ n → (n + 1 : ℚ) / 2 ≤ a n) := by
  sorry

end OMA.S_oeis_a015134

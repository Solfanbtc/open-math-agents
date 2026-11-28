import Mathlib

/-!
# A078613: Same numbers of distinct prime factors of forms 4*k+1 and 4*k+3.

Source: https://oeis.org/A078613
Credit: @Solfanbtc

`S` is the set of positive integers with as many distinct prime factors `≡ 1 (mod 4)` as distinct
prime factors `≡ 3 (mod 4)`: 1, 2, 4, 8, 15, 16, 30, ... `a n = Nat.nth S (n - 1)` is its `n`-th
element (offset 1). (The entry's example "99 = 3^2 · 11" is wrong: 11 ≡ 3 (mod 4), and 99 is not
a term.)

Conjecture (B. Cloitre, 2003): `a(n)` is asymptotic to `c n`, where `c` is around 4. The vague
"around 4" is not a precise claim, so `main` states `a(n) ~ c n` for some constant `c > 0`.

Remark: python3 gives `n / #(S ∩ [1, n])` = 3.86, 3.81, 3.99, 4.13, 4.23 at
`n = 10^3, …, 10^7`, slowly increasing. The Selberg–Delange heuristic for the additive function
`ω₁ - ω₃` predicts that `S` has density 0, roughly `x / √(log log x)` elements up to `x`.
That would make the conjecture false, so this statement is a natural disproof target.
-/

namespace OMA.S_oeis_a078613

open Filter Asymptotics

/-- Number of distinct prime factors of `n` congruent to `r` modulo 4. -/
def omegaMod4 (r n : ℕ) : ℕ := (n.primeFactors.filter (fun p => p % 4 = r)).card

/-- A078613 as a set. -/
def S : Set ℕ := {n | 1 ≤ n ∧ omegaMod4 1 n = omegaMod4 3 n}

/-- `a n`: the `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth S (n - 1)

theorem main :
    ∃ c : ℝ, 0 < c ∧ (fun n : ℕ => (a n : ℝ)) ~[atTop] fun n => c * n := by
  sorry

end OMA.S_oeis_a078613

import Mathlib

/-!
# A082449: Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f is iterated

Source: https://oeis.org/A082449
Credit: @Solfanbtc

`F p` is the greatest prime divisor of `p - 1`. For a prime `p`, `steps p` is the number of
iterations of `F` needed to reach 2 (e.g. 7 → 3 → 2 takes 2 steps). A082449(n) (offset 0) is the
least prime `p` with `steps p ≥ n`: 2, 3, 7, 23, 47, 283, 719, 1439, 2879, ...

A364332: `g 2 = 0`, and for an odd prime `p`, `g p = 1 + max {g q : q prime, q ∣ p - 1}`. It is
implemented with fuel: `gAux f p` recurses with fuel `f`, and `g p = gAux p p`. Fuel `p` is
enough, because every prime factor `q` of `p - 1` is `< p`.

Conjecture (Jianing Song, 2024; verified for `n ≤ 13`): A082449(n) is the smallest prime `p` with
`g p = n`. `main` states this for all `n ≥ 0`. Checked with python3: both descriptions give
2, 3, 7, 23, 47, 283, 719, 1439, 2879 for `n ≤ 8`.
-/

namespace OMA.S_oeis_a082449

/-- Greatest prime divisor of `p - 1` (0 if `p ≤ 2`). -/
def F (p : ℕ) : ℕ := (p - 1).primeFactors.sup id

/-- Number of iterations of `F` needed to reach 2. -/
noncomputable def steps (p : ℕ) : ℕ := sInf {k : ℕ | F^[k] p = 2}

/-- A082449(n): the least prime taking at least `n` steps. -/
noncomputable def A082449 (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ n ≤ steps p}

/-- `g` with explicit fuel. -/
def gAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, p => if p ≤ 2 then 0 else 1 + (p - 1).primeFactors.sup (gAux f)

/-- A364332 as a function of the prime: `g 2 = 0`, `g p = 1 + max_{q ∣ p-1} g q`. -/
def g (p : ℕ) : ℕ := gAux p p

theorem main : ∀ n : ℕ, IsLeast {p : ℕ | p.Prime ∧ g p = n} (A082449 n) := by
  sorry

end OMA.S_oeis_a082449

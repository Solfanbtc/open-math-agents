import Mathlib

/-!
# A256174: Boomerang Fractions: Starting with 1, on the first step add 1/n, and on subsequent steps either add 1/n or take the reciprocal. a(n) = minimal number of steps needed to return to 1.

Source: https://oeis.org/A256174
Credit: @Solfanbtc

Conjectures of the entry (offset 2, so `n ≥ 2`):
1. (Chai Wah Wu, Apr 02 2015) `a(b(b+1)) = 2(b+1)` for all `b ≥ 1` (exhaustive search for
   `b ≤ 12`).
2. (Jon E. Schoenfield, Apr 11 2015) For prime `n`, `a(n)` equals the minimal number of steps to
   return to `1` under the added constraint that the number of consecutive "add 1/n" steps
   immediately before each "take the reciprocal" step is a multiple of `n`.
3. (Schoenfield, stronger) The same holds when `n` is a prime power; and then it appears that,
   for `k ≥ 1`, `a(2^k) = 3*2^(k-1) + 1`, `a(3^k) = 7*3^(k-1) + 2`, `a(5^k) = 17*5^(k-1) + 3`,
   `a(7^k) = 30*7^(k-1) + 3`, `a(11^k) = 58*11^(k-1) + 4`, `a(13^k) = 70*13^(k-1) + 5`,
   `a(17^k) = 107*17^(k-1) + 4`, with minimal solutions using `1, 2, 3, 3, 4, 5, 4`
   "take the reciprocal" steps respectively. (At `k = 1` this includes the conjectured
   `a(13) = 75` of the K-12 conference.)
`main` is the conjunction of 1, 2, 3 (prime powers `p^k` with `k ≥ 1`), and the seven formulas
with their reciprocal counts.

Conventions. A run of steps is a list `s : List Bool` (`true` = add `1/n`, `false` = take the
reciprocal), applied to `1` in order in `ℚ` (all values stay positive). It is a return if the
first step is an addition and the final value is `1`; `a(n)` is the least length of a return
(the set is nonempty: `a(n) ≤ n^2`). The constraint: for each reciprocal step at index `i`, the
length of the maximal block of additions ending at index `i - 1` is divisible by `n`.
Checked (python3 BFS): `a(n)` for `n = 2, 3, 4, 5, 6, 8, 9, 10, 12` is
`4, 9, 7, 20, 6, 13, 23, 16, 8` (the data) and the constrained minimum is
`4, 9, 7, 20, 10, 13, 23, 16, 19` (Schoenfield's values).
-/

namespace OMA.S_oeis_a256174

/-- One step: add `1/n` (`true`) or take the reciprocal (`false`). -/
def step (n : ℕ) (x : ℚ) (b : Bool) : ℚ := if b then x + 1 / (n : ℚ) else x⁻¹

/-- The value reached from `1` after the steps `s`. -/
def val (n : ℕ) (s : List Bool) : ℚ := s.foldl (step n) 1

/-- `s` returns to `1`, its first step being an addition. -/
def IsReturn (n : ℕ) (s : List Bool) : Prop := s.head? = some true ∧ val n s = 1

/-- Schoenfield's constraint: the block of additions right before each reciprocal step has
length divisible by `n`. -/
def Constrained (n : ℕ) (s : List Bool) : Prop :=
  ∀ i (h : i < s.length), s[i] = false → n ∣ (((s.take i).reverse).takeWhile id).length

/-- A256174(n): the minimal number of steps to return to `1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | ∃ s : List Bool, s.length = k ∧ IsReturn n s}

/-- The minimal number of steps to return to `1` under Schoenfield's constraint. -/
noncomputable def aCons (n : ℕ) : ℕ :=
  sInf {k | ∃ s : List Bool, s.length = k ∧ IsReturn n s ∧ Constrained n s}

/-- Number of reciprocal steps of `s`. -/
def recips (s : List Bool) : ℕ := s.count false

/-- The conjectured prime-power data: `(p, c, d, r)` with `a(p^k) = c p^(k-1) + d`, attained
with `r` reciprocal steps. -/
def ppData : List (ℕ × ℕ × ℕ × ℕ) :=
  [(2, 3, 1, 1), (3, 7, 2, 2), (5, 17, 3, 3), (7, 30, 3, 3), (11, 58, 4, 4), (13, 70, 5, 5),
    (17, 107, 4, 4)]

/-- The conjectures of A256174. -/
theorem main :
    (∀ b : ℕ, 1 ≤ b → a (b * (b + 1)) = 2 * (b + 1)) ∧
    (∀ p : ℕ, p.Prime → a p = aCons p) ∧
    (∀ p k : ℕ, p.Prime → 1 ≤ k → a (p ^ k) = aCons (p ^ k)) ∧
    (∀ e ∈ ppData, ∀ k : ℕ, 1 ≤ k →
      a (e.1 ^ k) = e.2.1 * e.1 ^ (k - 1) + e.2.2.1 ∧
      ∃ s : List Bool, s.length = a (e.1 ^ k) ∧ IsReturn (e.1 ^ k) s ∧
        recips s = e.2.2.2) := by
  sorry

end OMA.S_oeis_a256174

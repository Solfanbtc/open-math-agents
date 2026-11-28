import Mathlib

/-!
# A095231: a(1)=1; a(n)=least positive integer such that the concatenation of all terms, including a(n), is == 1 (mod n).

Source: https://oeis.org/A095231
Credit: @Solfanbtc

Conjecture (OEIS entry): every natural number occurs infinitely many times, i.e. for every
`m ≥ 1` (all terms are positive integers) there are infinitely many `n` with `a(n) = m`.

Formalization: `state n = (a(n), C(n))`, where `C(n)` is the decimal concatenation
`a(1) a(2) … a(n)` as a natural number. For `n ≥ 2`, `a(n)` is the least `a ≥ 1` with
`C(n-1) · 10^(len a) + a ≡ 1 (mod n)`. The search runs over `1 ≤ a ≤ 100 n`, and this bound
always suffices: take `d` minimal with `10^(d-1) ≥ n`; the `9·10^(d-1) ≥ n` consecutive
`d`-digit numbers all have the same length, so they cover every residue mod `n`; hence a solution
exists below `10^d < 100 n`. The fallback value `0` is therefore never used for `n ≥ 2`.
Checked with `#eval`: the first 78 values agree with the OEIS data (%S, %T, %U).
-/

namespace OMA.S_oeis_a095231

/-- Least `a ∈ [1, 100 n]` such that appending `a` to the concatenation `c` gives `≡ 1 (mod n)`. -/
def step (n c : ℕ) : ℕ :=
  (((List.range (100 * n)).map (· + 1)).find?
    (fun a => decide ((c * 10 ^ (Nat.digits 10 a).length + a) % n = 1 % n))).getD 0

/-- `state n = (a(n), concatenation of a(1), …, a(n))`, for `n ≥ 1`. -/
def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 =>
    let c := (state (n + 1)).2
    let a := step (n + 2) c
    (a, c * 10 ^ (Nat.digits 10 a).length + a)

/-- A095231. -/
def a (n : ℕ) : ℕ := (state n).1

/-- Every positive integer occurs infinitely often in A095231. -/
theorem main : ∀ m : ℕ, 0 < m → Set.Infinite {n : ℕ | a n = m} := by
  sorry

end OMA.S_oeis_a095231

import Mathlib

/-!
# A073818: a(n) = max(prime(i)*(n+1-i) | 1 <= i <= n).

Source: https://oeis.org/A073818
Credit: @Solfanbtc

`a(n)` (offset 1) is `max {prime(i) (n+1-i) : 1 ≤ i ≤ n}` with `prime(1) = 2`; Mathlib's
`Nat.nth Nat.Prime` is 0-indexed, so `prime(i) = Nat.nth Nat.Prime (i - 1)`.
Data: 2, 4, 6, 10, 15, 22, 33, ... (the definition reproduces every term of %S, %T, %U).

Conjecture (M. Kurkov, 2022). For `n ≥ 2` the operator `P(n)` acts on a sequence
`s(1), s(2), ...` by keeping `s(1), ..., s(n)` fixed and then sorting every block of `n`
consecutive terms thereafter, i.e. the blocks of positions `n + qn + 1, ..., n + qn + n`
(`q ≥ 0`), in descending order if `n` is prime and in ascending order otherwise.
`PS(2) = P(2)(1, 2, 3, ...)` and `PS(n) = P(n)(PS(n-1))`; `b` is the limit of `PS(n)`.
Since `P(k)` fixes the first `k` terms, `PS(k)(m) = PS(m)(m)` for all `k ≥ m`, so the limit
exists and `b(m) = PS(m)(m)`; that is how `b` is defined below (`PS(1)` is the identity, the
starting sequence `1, 2, 3, ...`).
With `c(n) = b(prime(n) + 1)`, the claim is `a(n) = c(n-1)` for `n > 1` with a single exception
at `n = 5`: so `a(n) = b(prime(n-1) + 1)` for every `n ≥ 2` with `n ≠ 5`, and `a(5) ≠ c(4)`
(indeed `a(5) = 15` and `c(4) = b(8) = 16`). Checked in Python for `2 ≤ n < 120`.

Sequences are functions `ℕ → ℕ` read at positions `≥ 1` (position `0` is unused).
-/

namespace OMA.S_oeis_a073818

/-- `prime(i)`, 1-indexed. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- A073818. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (fun i => prime i * (n + 1 - i))

/-- Sort a block ascending, or descending when `desc`. -/
def blockSort (desc : Bool) (l : List ℕ) : List ℕ :=
  let l' := l.insertionSort (· ≤ ·)
  if desc then l'.reverse else l'

/-- The operator `P(n)`: fix positions `1..n`, then sort each later block of `n` consecutive
positions, descending if `n` is prime, ascending otherwise. -/
def P (n : ℕ) (s : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j ≤ n then s j else
    let q := (j - n - 1) / n
    let t := (j - n - 1) % n
    let start := n + q * n + 1
    (blockSort (decide n.Prime) ((List.range n).map (fun i => s (start + i)))).getD t 0

/-- `PS(1)` is `1, 2, 3, ...` and `PS(n) = P(n)(PS(n-1))` for `n ≥ 2`. -/
def PS : ℕ → ℕ → ℕ
  | 0 => fun j => j
  | 1 => fun j => j
  | n + 2 => P (n + 2) (PS (n + 1))

/-- The limit sequence `b(m) = PS(m)(m)`. -/
def b (m : ℕ) : ℕ := PS m m

theorem main : (∀ n : ℕ, 2 ≤ n → n ≠ 5 → a n = b (prime (n - 1) + 1)) ∧
    a 5 ≠ b (prime 4 + 1) := by
  sorry

end OMA.S_oeis_a073818

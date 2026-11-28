import Mathlib

/-!
# A072493: a(1) = 1 and a(n) = ceiling((Sum_{k=1..n-1} a(k))/3) for n >= 2.

Source: https://oeis.org/A072493
Credit: @Solfanbtc

Question (R. Stephan, 2003): is this sequence, with its first 8 terms removed, the same as
A005427? A005427 is the Josephus problem: the numbers `m` such that, when `m` people numbered
1 through `m` stand on a circle and every 4th person is removed (the counting starts at person 1,
so person 4 goes first), the final survivor is one of the first three people.

`main` states the expected answer: `A005427(n) = A072493(n + 8)` for every `n ≥ 1`. Here
`T n` is A072493(n). It is computed through the partial sums
`s n = T 1 + ⋯ + T n`, with `s 1 = 1` and `s (n+1) = s n + ⌈s n / 3⌉`, so that
`T n = s n - s (n-1)`; this gives 1, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, ...
`josephus m` simulates the game literally. With 0-based indices, the person removed is
`(p + 3) mod (current size)`, where `p` is the position the count starts from, and the count
restarts at the person after the removed one.

Range fix: the data of A005427 starts 5, 7, 9, 12, ..., so it leaves out `m = 1, 2, 3`
(trivially a survivor among the first three) and also `m = 4` (survivor: person 2). So A005427
is the set of `m ≥ 5` (more people than the step) whose survivor is in `{1, 2, 3}`, and this is
the set used here. Checked with python3: this set enumerates as 5, 7, 9, 12, 16, 22, ...,
matching the A005427 data, and equals `T (n + 9)` (0-indexed `n`) for all of its 47 elements
below 3·10^6.

Status: the entry answers "Yes" (C. Neder, Jan 10 2019), reducing it to the formula
`A005427(n) = 5 + ⌈(A005427(1) + ⋯ + A005427(n-1)) / 3⌉` given in A005427; the general
form for every step `k` is a conjecture of P. Hadjicostas in A005427 (cf. K. Burde,
J. Number Theory 26 (1987) 192-209).
-/

namespace OMA.S_oeis_a072493

/-- Partial sums of A072493: `s n = a(1) + ⋯ + a(n)`. -/
def s : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => s (n + 1) + (s (n + 1) + 2) / 3

/-- A072493 (offset 1): `T n = ⌈s (n-1) / 3⌉` for `n ≥ 2`, `T 1 = 1`. -/
def T (n : ℕ) : ℕ := s n - s (n - 1)

/-- Josephus game with step 4, run with fuel `f`: `l` is the circle, and the count starts at
index `p`. -/
def survive : ℕ → List ℕ → ℕ → ℕ
  | 0, l, _ => l.headD 0
  | f + 1, l, p =>
    if l.length ≤ 1 then l.headD 0
    else
      let i := (p + 3) % l.length
      survive f (l.eraseIdx i) (i % (l.length - 1))

/-- The last survivor when every 4th of `m` people `1, …, m` is removed, counting from person 1. -/
def josephus (m : ℕ) : ℕ := survive m (List.range' 1 m) 0

/-- A005427: the `m ≥ 5` whose last survivor is among persons 1, 2, 3. -/
def A005427Set : Set ℕ := {m | 5 ≤ m ∧ josephus m ≤ 3}

/-- A005427(n + 1) = A072493(n + 9) for all `n ≥ 0`. -/
theorem main : ∀ n : ℕ, Nat.nth A005427Set n = T (n + 9) := by
  sorry

end OMA.S_oeis_a072493

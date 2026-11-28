import Mathlib

/-!
# A104157: Smallest of n^2 consecutive primes forming an n × n magic square with least constant

Source: https://oeis.org/A104157
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest of `n^2` consecutive primes that form an `n × n` magic square
with the least magic constant, or `0` if no such magic square exists: `2, 0, 1480028129, 31, 13,
7, 7, 79, …`. A magic square: the `n^2` numbers placed in an `n × n` grid (each once) so that all
rows, all columns and both diagonals have the same sum (the magic constant).

Formalization. `prime(i)` is the `i`-th prime (`prime(1) = 2`). `Admits n i` says that the `n^2`
consecutive primes `prime(i), …, prime(i + n^2 - 1)` can be arranged (a bijection between the
cells and `{0, …, n^2 - 1}`) into a magic square. The magic constant of such a square is
`(prime(i) + ⋯ + prime(i + n^2 - 1))/n`, which is strictly increasing in `i`, so the square with
the least magic constant uses the least admissible `i`, and `a(n) = prime(i_min)`; `a(n) = 0`
if no `i` is admissible.

Conjecture (Max Alekseyev, Jan 29 2010, OEIS formula): for `n > 4`, `a(n) = prime(s)` where
`s > 1` is the smallest integer such that `(∑_{i=s}^{s+n^2-1} prime(i))/n` is an integer of the
same parity as `n`. (Python: this rule reproduces all data terms `a(5), …, a(63)`.)
-/

namespace OMA.S_oeis_a104157

/-- `prime(i)`, the `i`-th prime, `prime(1) = 2`. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- `v` is a magic square: all rows, columns and both diagonals have the same sum. -/
def IsMagic (n : ℕ) (v : Fin n → Fin n → ℕ) : Prop :=
  ∃ M : ℕ, (∀ r, ∑ c, v r c = M) ∧ (∀ c, ∑ r, v r c = M) ∧
    (∑ j, v j j = M) ∧ (∑ j, v j (Fin.rev j) = M)

/-- The `n^2` consecutive primes starting at `prime(i)` form an `n × n` magic square. -/
def Admits (n i : ℕ) : Prop :=
  ∃ f : Fin n × Fin n ≃ Fin (n ^ 2), IsMagic n (fun r c => prime (i + f (r, c)))

open Classical in
/-- A104157. -/
noncomputable def a (n : ℕ) : ℕ :=
  if {i : ℕ | 1 ≤ i ∧ Admits n i}.Nonempty then prime (sInf {i : ℕ | 1 ≤ i ∧ Admits n i}) else 0

/-- Sum of the `n^2` consecutive primes starting at `prime(s)`. -/
noncomputable def blockSum (n s : ℕ) : ℕ := ∑ k ∈ Finset.range (n ^ 2), prime (s + k)

/-- Alekseyev's conjecture: for `n > 4`, `a(n) = prime(s)` with `s > 1` least such that
`blockSum n s / n` is an integer of the same parity as `n`. -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = prime (sInf {s : ℕ | 1 < s ∧ n ∣ blockSum n s ∧ (blockSum n s / n) % 2 = n % 2}) := by
  sorry

end OMA.S_oeis_a104157

import Mathlib

/-!
# A026225: the numbers 3^i (3k+1) are the complement of the record positions A026179

Source: https://oeis.org/A026225
Credit: @Solfanbtc

A026225 (offset 1): the numbers of the form `3^i (3k + 1)`: 1, 3, 4, 7, 9, 10, 12, 13, 16, …

The entry: "Conjectures based on old name: these are numbers of the form (3*i+1)*3^j; see
A182828, and they comprise the complement of A026179, except for the initial 1 in A026179."
The first part became the new name after P. Munn's proof (see A026224); the second is the
"old conjecture" recorded in A026179 as well. `main` states the second part with the current
definitions.

A026177 (offset 1): `a(1) = 1`; for `n = 2, 3, 4, …` in turn, let `h = floor(n/2)`, `L = n - h`,
`R = n + h`; then `a(R) = n` if `n` is odd or `a(L)` is already defined, otherwise `a(L) = n`.
Data 1, 4, 2, 3, 10, 12, 5, 16, 6, 7, … A026179: the numbers `k` with `A026177(j) < A026177(k)`
for all `j < k` (the record positions): 1, 2, 5, 6, 8, 11, 14, …

The claim: for `k ≥ 2`, `k` is in A026179 iff `k` is not in A026225 (the initial `1` is in both,
hence "except for the initial 1").

Lean details. The partial function built by the procedure is a function `ℕ → ℕ` with `0` for
"not yet defined" (all values are `≥ 1`). Position `k` receives its value from some `n ≤ 2k`
(at `L = n - floor(n/2) ≥ n/2` or at `R ≥ n`), and later steps write only at positions `> k`,
so `a(k)` is read after processing `n = 2k`. Checked with python3: the procedure reproduces the
data of A026177, and the claim holds for `2 ≤ k < 3000`.
-/

namespace OMA.S_oeis_a026225

/-- One step of the A026177 procedure for `n ≥ 2`. -/
def step (n : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  if n % 2 = 1 ∨ f (n - n / 2) ≠ 0 then Function.update f (n + n / 2) n
  else Function.update f (n - n / 2) n

/-- The partial function after processing `1, …, n` (`0` means undefined). -/
def assign : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | 1 => Function.update (fun _ => 0) 1 1
  | n + 2 => step (n + 2) (assign (n + 1))

/-- A026177. -/
def a026177 (k : ℕ) : ℕ := assign (2 * k) k

/-- A026179: `k ≥ 1` is a record position of A026177. -/
def IsRecord (k : ℕ) : Prop := 1 ≤ k ∧ ∀ j, 1 ≤ j → j < k → a026177 j < a026177 k

/-- A026225: `k` has the form `3^i (3m + 1)`. -/
def InA026225 (k : ℕ) : Prop := ∃ i m : ℕ, k = 3 ^ i * (3 * m + 1)

/-- The old conjecture: apart from the initial 1, A026179 is the complement of A026225. -/
theorem main : ∀ k : ℕ, 2 ≤ k → (IsRecord k ↔ ¬ InA026225 k) := by
  sorry

end OMA.S_oeis_a026225

import Mathlib

/-!
# A056862: Restricted growth strings with a decrease at index k

Source: https://oeis.org/A056862
Credit: @Solfanbtc

`T(n, k)` (`n ≥ 2`, `1 ≤ k < n`) is the number of restricted growth strings (RGS)
`[s_1, …, s_n]` of set partitions of `{1, …, n}` (`s_1 = 1`, `s_i ≤ 1 + max_{j<i} s_j`, all
`s_i ≥ 1`) that have a decrease (fall) `s_k > s_{k+1}` at index `k`. Rows:
`0; 0, 1; 0, 3, 4; 0, 10, 14, 16; 0, 37, 54, 63, 68; …` (a brute-force count with this definition
reproduces the rows `n = 2..6`). Below an RGS is `s : Fin n → Fin (n+1)` (values `≤ n`), with
`s 0 = 1`, `s i ≥ 1`, `s i ≤ 1 + max_{j<i} s j`; index `k` (1-based) is position `k - 1` (0-based).

A011965 (offset 0): second differences of the Bell numbers,
`A011965(m) = B(m+2) - 2 B(m+1) + B(m)`: `1, 2, 7, 27, 114, …`; Bell numbers by
`B(0) = 1`, `B(m+1) = ∑_{i ≤ m} C(m, i) B(i)`.

Conjecture (R. J. Mathar, Mar 08 2016, OEIS formula): `T(n, 3) = 2 A011965(n)`.

Minimal fix (index shift): read literally with the two offsets, this is false at the first
admissible row (`T(4, 3) = 4`, `2 A011965(4) = 228`). The column `T(n, 3)`, `n = 4, 5, 6, …`, is
`4, 14, 54, 228, 1046, …` `= 2 · (2, 7, 27, 114, 523, …)`, i.e. `T(n, 3) = 2 A011965(n - 3)`: the
formula holds when the column is indexed from its first entry, which is the reading stated
(`n ≥ 4`, the rows having a third column). Python: holds for `4 ≤ n ≤ 11`.
-/

namespace OMA.S_oeis_a056862

/-- `s` is a restricted growth string of length `n`. -/
def IsRGS (n : ℕ) (s : Fin n → Fin (n + 1)) : Prop :=
  (∀ i : Fin n, (i : ℕ) = 0 → (s i : ℕ) = 1) ∧ (∀ i, 1 ≤ (s i : ℕ)) ∧
  ∀ i : Fin n, 0 < (i : ℕ) →
    (s i : ℕ) ≤ 1 + ((Finset.univ.filter fun j : Fin n => j < i).sup fun j => (s j : ℕ))

instance (n : ℕ) : DecidablePred (IsRGS n) := fun s => by unfold IsRGS; infer_instance

/-- `T(n, k)`: RGS of length `n` with a fall at index `k` (1-based), `s_k > s_{k+1}`. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Fin n → Fin (n + 1) =>
    IsRGS n s ∧ ∃ i : Fin n, ∃ i' : Fin n, (i : ℕ) = k - 1 ∧ (i' : ℕ) = k ∧ s i' < s i).card

/-- Bell numbers. -/
def bell : ℕ → ℕ
  | 0 => 1
  | m + 1 => ∑ i : Fin (m + 1), Nat.choose m i * bell i

/-- A011965: second differences of the Bell numbers. -/
def A011965 (m : ℕ) : ℤ := (bell (m + 2) : ℤ) - 2 * bell (m + 1) + bell m

/-- Mathar's conjecture (column indexed from its first entry): `T(n, 3) = 2 A011965(n - 3)`. -/
theorem main : ∀ n : ℕ, 4 ≤ n → (T n 3 : ℤ) = 2 * A011965 (n - 3) := by
  sorry

end OMA.S_oeis_a056862

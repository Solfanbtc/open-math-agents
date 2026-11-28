import Mathlib

/-!
# A094373: first occurrences in Ianakiev's palindrome-length sequence

Source: https://oeis.org/A094373 (with https://oeis.org/A007843)
`a = A094373` (offset 0) is the expansion of `(1-x-x^2)/((1-x)(1-2x))`: 1, 2, 3, 5, 9, 17, 33, ...,
i.e. `a(0) = 1` and `a(n) = 2^(n-1) + 1` for `n ≥ 1` (formula lines of the entry).

Comment of Ivan N. Ianakiev (Aug 20 2019): "Take A007843 and count the repeated values. The result
is 1,1,2,1,3,1,2,1,4,1,2,1,3,1,2,1,5,.... Build a third sequence, where a(1) = 1 and a(n) equals the
length (greater than 1) of the shortest palindromic subsequence of consecutive terms of the second
sequence starting with a(n) of the second sequence. The third sequence starts
1,3,5,3,9,3,5,3,17,3,5,3,9,3,5,3,33,.... Conjecturally, in the third sequence: (1) the indices of
the first occurrence of each value form the present sequence and (2) for n>1, a(n) is in the
a(n-1)-th position."

Formalization.
* `A007843 n` is the least positive `k` with `2^n ∣ k!` (offset 0: 1, 2, 4, 4, 6, 8, 8, 8, ...).
* The second sequence `s` (1-indexed) counts the repeated values: `s m` is the number of `n` with
  `A007843 n` equal to the `m`-th distinct value of A007843 (`v (m - 1)`, values in increasing
  order; A007843 is nondecreasing, so these are its run lengths).
* The third sequence `t` (1-indexed): `t 1 = 1`, and for `n ≥ 2`, `t n` is the least `L ≥ 2` such
  that the block `s n, s (n+1), ..., s (n+L-1)` is a palindrome (`sInf`; such an `L` exists in all
  computed cases).
* (1): an index `i ≥ 1` is the first occurrence of its value in `t` iff `i = a n` for some `n`.
  (2): for `n > 1`, `t (a (n - 1)) = a n`, i.e. `a(n)` is the value at position `a(n-1)`.
Checked with python3 from the definition of A007843: `s` and `t` begin as quoted above; up to
index 512 the first occurrences in `t` are exactly 1, 2, 3, 5, 9, ..., 257, and (2) holds.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a094373

/-- A094373: `a 0 = 1`, `a n = 2^(n-1) + 1` for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := if n = 0 then 1 else 2 ^ (n - 1) + 1

/-- A007843: the least positive integer `k` with `2^n ∣ k!`. -/
noncomputable def A007843 (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ 2 ^ n ∣ k.factorial}

/-- The `m`-th distinct value of A007843 (from `m = 0`, in increasing order). -/
noncomputable def v (m : ℕ) : ℕ := Nat.nth (fun x => x ∈ Set.range A007843) m

/-- The second sequence (1-indexed): the number of times the `m`-th value of A007843 repeats. -/
noncomputable def s (m : ℕ) : ℕ := Nat.card {n : ℕ // A007843 n = v (m - 1)}

/-- The third sequence (1-indexed): `t 1 = 1`; for `n ≥ 2`, the least length `L ≥ 2` of a
palindromic block of consecutive terms of `s` starting at `s n`. -/
noncomputable def t (n : ℕ) : ℕ :=
  if n = 1 then 1 else
    sInf {L : ℕ | 2 ≤ L ∧ (List.ofFn fun i : Fin L => s (n + i)).reverse =
      List.ofFn fun i : Fin L => s (n + i)}

theorem main :
    (∀ i : ℕ, 1 ≤ i → ((∀ j : ℕ, 1 ≤ j → j < i → t j ≠ t i) ↔ ∃ n : ℕ, i = a n)) ∧
    (∀ n : ℕ, 1 < n → t (a (n - 1)) = a n) := by
  sorry

end OMA.S_oeis_a094373

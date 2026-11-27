import OMAStatements.S_oeis_a047618
import Mathlib

/-!
Let `P k` be `k % 8 ∈ {0, 2, 5}`. `P` is 8-periodic with three hits per period, so
`count P (8m + r) = 3m + count P r`, and `Nat.nth_count` gives `nth P (3m) = 8m`,
`nth P (3m + 1) = 8m + 2`, `nth P (3m + 2) = 8m + 5`. Hence `a(3m+1), a(3m+2), a(3m+3)` are
`8m, 8m + 2, 8m + 5`, and both identities follow by cases on `n mod 3`.
-/

namespace R047618
open OMA.S_oeis_a047618

abbrev P (k : ℕ) : Prop := k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 5

theorem count_shift (m r : ℕ) :
    Nat.count P (8 * m + r) = Nat.count P (8 * m) + Nat.count P r := by
  rw [Nat.count_add]
  congr 1
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.count_succ, Nat.count_succ, ih]
    congr 1
    have hiff : P (8 * m + r) ↔ P r := by
      simp only [P]
      constructor <;> intro h <;> omega
    by_cases hr : P r
    · rw [if_pos hr, if_pos (hiff.mpr hr)]
    · rw [if_neg hr, if_neg (fun h => hr (hiff.mp h))]

theorem count_mul (m : ℕ) : Nat.count P (8 * m) = 3 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h8 : Nat.count P 8 = 3 := by decide
    rw [show 8 * (m + 1) = 8 * m + 8 by ring, count_shift, ih, h8]
    ring

theorem nth_eq (m : ℕ) : Nat.nth P (3 * m) = 8 * m ∧ Nat.nth P (3 * m + 1) = 8 * m + 2 ∧
    Nat.nth P (3 * m + 2) = 8 * m + 5 := by
  have c0 := count_mul m
  have k2 : Nat.count P 2 = 1 := by decide
  have k5 : Nat.count P 5 = 2 := by decide
  have c2 : Nat.count P (8 * m + 2) = 3 * m + 1 := by rw [count_shift, c0, k2]
  have c5 : Nat.count P (8 * m + 5) = 3 * m + 2 := by rw [count_shift, c0, k5]
  refine ⟨?_, ?_, ?_⟩
  · rw [← c0]; exact Nat.nth_count (by simp only [P]; omega)
  · rw [← c2]; exact Nat.nth_count (by simp only [P]; omega)
  · rw [← c5]; exact Nat.nth_count (by simp only [P]; omega)

theorem a_vals (m : ℕ) :
    a (3 * m + 1) = 8 * m ∧ a (3 * m + 2) = 8 * m + 2 ∧ a (3 * m + 3) = 8 * m + 5 := by
  obtain ⟨h0, h1, h2⟩ := nth_eq m
  refine ⟨?_, ?_, ?_⟩
  · show Nat.nth P (3 * m + 1 - 1) = _
    rw [Nat.add_sub_cancel]; exact h0
  · show Nat.nth P (3 * m + 2 - 1) = _
    rw [show 3 * m + 2 - 1 = 3 * m + 1 by omega]; exact h1
  · show Nat.nth P (3 * m + 3 - 1) = _
    rw [show 3 * m + 3 - 1 = 3 * m + 2 by omega]; exact h2

theorem sum3 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) + (a (n + 1) : ℤ) + (a (n + 2) : ℤ) = 8 * (n : ℤ) - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 1 ∨ n = 3 * m + 2 ∨ n = 3 * m + 3 :=
    ⟨(n - 1) / 3, by omega⟩
  obtain ⟨e1, e2, e3⟩ := a_vals m
  obtain ⟨f1, f2, _⟩ := a_vals (m + 1)
  rcases hm with rfl | rfl | rfl
  · rw [show 3 * m + 1 + 1 = 3 * m + 2 by ring, show 3 * m + 1 + 2 = 3 * m + 3 by ring,
      e1, e2, e3]
    push_cast; ring
  · rw [show 3 * m + 2 + 1 = 3 * m + 3 by ring, show 3 * m + 2 + 2 = 3 * (m + 1) + 1 by ring,
      e2, e3, f1]
    push_cast; ring
  · rw [show 3 * m + 3 + 1 = 3 * (m + 1) + 1 by ring,
      show 3 * m + 3 + 2 = 3 * (m + 1) + 2 by ring, e3, f1, f2]
    push_cast; ring

theorem recur (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 8 * ((n : ℤ) - 2) - (a (n - 1) : ℤ) - (a (n - 2) : ℤ) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 2 + 1 by omega, show k + 4 - 2 = k + 2 by omega]
  have h := sum3 (k + 2) (by omega)
  rw [show k + 2 + 2 = k + 4 by ring] at h
  push_cast at h ⊢
  linarith

end R047618

theorem OMA.solution : type_of% @OMA.S_oeis_a047618.main := by
  refine ⟨R047618.sum3, ?_, ?_, ?_, R047618.recur⟩
  · exact (R047618.a_vals 0).1
  · exact (R047618.a_vals 0).2.1
  · exact (R047618.a_vals 0).2.2

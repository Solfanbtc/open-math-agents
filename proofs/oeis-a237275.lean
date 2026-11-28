import OMAStatements.S_oeis_a237275
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.IntervalCases

/-! OEIS A237275: the least `k > 0` with last digit `d = k % 10 > 1` and `d ^ n ∣ k` ends in `2`.

A number ending in `2` works and is at most `4 * 2 ^ n`: `2 ^ n` itself if it ends in `2`, and
otherwise `3 * 2 ^ n`, `2 * 2 ^ n` or `4 * 2 ^ n` according as `2 ^ n` ends in `4`, `6` or `8`.
If the least `k` ended in `d ≥ 3`, then `3 ^ n ≤ d ^ n ≤ k ≤ 4 * 2 ^ n`, impossible for `n ≥ 4`;
the cases `n ≤ 3` are checked directly against the witnesses `2, 2, 12, 32`. -/

namespace OpenMath.A237275

open OMA.S_oeis_a237275

private theorem pow_two_mod (n : ℕ) :
    2 ^ (n + 1) % 10 = 2 ∨ 2 ^ (n + 1) % 10 = 4 ∨ 2 ^ (n + 1) % 10 = 6 ∨
      2 ^ (n + 1) % 10 = 8 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

private theorem witness (n : ℕ) :
    ∃ w, w ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} ∧ w ≤ 4 * 2 ^ n := by
  rcases n with _ | n
  · exact ⟨2, ⟨by decide, by decide, by decide⟩, by decide⟩
  · have hpos := Nat.two_pow_pos (n + 1)
    rcases pow_two_mod n with h | h | h | h
    · exact ⟨2 ^ (n + 1), ⟨hpos, by omega, dvd_of_eq (by rw [h])⟩, by omega⟩
    · refine ⟨3 * 2 ^ (n + 1), ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [show 3 * 2 ^ (n + 1) % 10 = 2 by omega]
      exact dvd_mul_left _ _
    · refine ⟨2 * 2 ^ (n + 1), ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [show 2 * 2 ^ (n + 1) % 10 = 2 by omega]
      exact dvd_mul_left _ _
    · refine ⟨4 * 2 ^ (n + 1), ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [show 4 * 2 ^ (n + 1) % 10 = 2 by omega]
      exact dvd_mul_left _ _

private theorem big (n : ℕ) : 4 * 2 ^ (n + 4) < 3 ^ (n + 4) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 4 = n + 4 + 1 by omega, pow_succ 2 (n + 4), pow_succ 3 (n + 4)]
    omega

theorem main : ∀ n : ℕ, a n % 10 = 2 := by
  intro n
  obtain ⟨w, hw, hw4⟩ := witness n
  have hk : a n ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} := Nat.sInf_mem ⟨w, hw⟩
  have hle : a n ≤ w := Nat.sInf_le hw
  have hsm : ∀ v, v ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} → a n ≤ v :=
    fun v hv => Nat.sInf_le hv
  generalize a n = k at hk hle hsm ⊢
  obtain ⟨hk0, hk1, hkd⟩ := hk
  by_contra hne
  have hd3 : 3 ≤ k % 10 := by omega
  have h3 : 3 ^ n ≤ k := (Nat.pow_le_pow_left hd3 n).trans (Nat.le_of_dvd hk0 hkd)
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n
    · have := hsm 2 ⟨by decide, by decide, by decide⟩
      omega
    · have := hsm 2 ⟨by decide, by decide, by decide⟩
      omega
    · have := hsm 12 ⟨by decide, by decide, by decide⟩
      interval_cases k <;> revert hkd hne hk1 <;> decide
    · have := hsm 32 ⟨by decide, by decide, by decide⟩
      interval_cases k <;> revert hkd hne hk1 <;> decide
  · have hb := big (n - 4)
    rw [show n - 4 + 4 = n by omega] at hb
    omega

end OpenMath.A237275

theorem OMA.solution : type_of% @OMA.S_oeis_a237275.main := OpenMath.A237275.main

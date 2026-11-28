import OMAStatements.S_oeis_a226839

namespace R226839
open OMA.S_oeis_a226839

theorem a_zero : a 0 = 1 := by
  rw [a]

/-- For `k ≥ 1`, the coefficient `T_{k+1}! / (k+1)!` is divisible by 3. -/
theorem three_dvd (k : ℕ) :
    3 ∣ (tri (k + 1 + 1)).factorial / (k + 1 + 1).factorial := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · obtain rfl : k = 0 := by omega
    norm_num [tri, Nat.factorial]
  · have h3 : k + 1 + 1 + 3 ≤ tri (k + 1 + 1) := by
      unfold tri
      have : 2 * (k + 1 + 1 + 3) ≤ (k + 1 + 1) * (k + 1 + 1 + 1) := by nlinarith
      omega
    generalize tri (k + 1 + 1) = m at h3 ⊢
    have hf := Nat.factorial_mul_descFactorial (Nat.sub_le m (k + 1 + 1))
    rw [show m - (m - (k + 1 + 1)) = k + 1 + 1 by omega] at hf
    apply Nat.dvd_div_of_mul_dvd
    rw [← hf]
    exact Nat.mul_dvd_mul_left _ ((Nat.dvd_factorial (by norm_num) (by omega)).trans
      (Nat.factorial_dvd_descFactorial _ _))

theorem aux {x y S : ℕ} (hx : x = y) (hS : 3 ∣ S) : x + S ≡ y [MOD 3] := by
  obtain ⟨c, rfl⟩ := hS
  subst hx
  unfold Nat.ModEq
  omega

theorem step (n : ℕ) : a (n + 1) ≡ a n [MOD 3] := by
  rw [a, Fin.sum_univ_succ]
  apply aux
  · have h0 : tri 1 = 1 := rfl
    simp [h0]
  · apply Finset.dvd_sum
    intro i _
    simp only [Fin.val_succ]
    split_ifs
    · exact ((three_dvd i.1).mul_right _).mul_right _
    · exact dvd_zero 3

end R226839

theorem OMA.solution : type_of% @OMA.S_oeis_a226839.main := by
  intro n
  induction n with
  | zero =>
    unfold Nat.ModEq
    rw [R226839.a_zero]
  | succ n ih => exact (R226839.step n).trans ih

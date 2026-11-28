import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib

/-! With `n! = 4 v`, an odd root `m = 2 x + 1` of `n! + 1 = m ^ 2` is the same as `x (x + 1) = v`;
an even root is impossible modulo 4. -/

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := by
  intro n hn
  obtain ⟨v, hv⟩ := Nat.dvd_factorial (by decide : 0 < 4) hn
  rw [hv, Nat.mul_div_cancel_left _ (by decide)]
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.even_or_odd m with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · ring_nf at hm; omega
    · exact ⟨x, by nlinarith⟩
  · rintro ⟨x, rfl⟩
    exact ⟨2 * x + 1, by ring⟩

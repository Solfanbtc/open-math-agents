import OMAStatements.S_oeis_a242533
import Mathlib

/-!
Two neighbours a, b of the same parity have a - b and a + b both even, so they are not coprime.
Hence along a valid cycle the parities of the values alternate, which is impossible for a cycle of
odd length: there is no valid arrangement at all for odd m, and the count is 0.
-/

namespace R242533
open OMA.S_oeis_a242533

theorem parity_ne (x y : ℕ) (h : Nat.Coprime (Int.natAbs ((x : ℤ) - (y : ℤ))) (x + y)) :
    x % 2 ≠ y % 2 := by
  intro heq
  have h1 : 2 ∣ Int.natAbs ((x : ℤ) - (y : ℤ)) := Int.ofNat_dvd_left.mp (by omega)
  have h2 : 2 ∣ x + y := by omega
  have := Nat.dvd_gcd h1 h2
  rw [h] at this
  omega

theorem no_valid (m : ℕ) (hm : Odd m) (σ : Equiv.Perm (Fin m)) : ¬ IsValidCycle m σ := by
  intro h
  have hm0 : 0 < m := hm.pos
  have step : ∀ k (hk : k + 1 < m),
      ((σ ⟨k, by omega⟩).val + 1) % 2 ≠ ((σ ⟨k + 1, hk⟩).val + 1) % 2 := by
    intro k hk
    have hk' := h ⟨k, by omega⟩
    simp only at hk'
    have e : (⟨(k + 1) % m, Nat.mod_lt _ hm0⟩ : Fin m) = ⟨k + 1, hk⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hk)
    rw [e] at hk'
    exact parity_ne _ _ hk'
  have chain : ∀ k (hk : k < m),
      ((σ ⟨k, hk⟩).val + 1) % 2 = ((σ ⟨0, hm0⟩).val + 1 + k) % 2 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := step k hk
      omega
  obtain ⟨t, ht⟩ := hm
  have hlast := h ⟨m - 1, by omega⟩
  simp only at hlast
  have e : (⟨(m - 1 + 1) % m, Nat.mod_lt _ hm0⟩ : Fin m) = ⟨0, hm0⟩ :=
    Fin.ext (by simp [Nat.sub_add_cancel hm0])
  rw [e] at hlast
  have h1 := parity_ne _ _ hlast
  have h2 := chain (m - 1) (by omega)
  omega

end R242533

theorem OMA.solution : type_of% @OMA.S_oeis_a242533.main := by
  intro m hm
  haveI : IsEmpty {σ : Equiv.Perm (Fin m) // OMA.S_oeis_a242533.IsValidCycle m σ} :=
    ⟨fun x => R242533.no_valid m hm x.1 x.2⟩
  simp [OMA.S_oeis_a242533.NPC, Finset.univ_eq_empty]

import OMAReductions.R_mo_368734_R1

-- Step mo-368734.R1.H1: hypothesis H1 of reduction mo-368734.R1
-- Credit: @Solfanbtc

/-! If `p % 5 ≠ 1` then `5` is coprime to `p - 1`, so `5 a = 1 + (p - 1) b` for some `a ≥ 1`.
By Fermat's little theorem `(x ^ 5) ^ a = x` for every `x : ZMod p` (also for `x = 0`), so
`x ↦ x ^ 5` is injective, hence so is `x ↦ x ^ 5 + 3`, which is then bijective on the finite
type `ZMod p`. -/

theorem OMA.solution : OMA.R_mo_368734_R1.H1 := by
  intro p hp hp5
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 := hp.two_le
  have hcop : Nat.Coprime 5 (p - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 fun h => hp5 (by omega)
  obtain ⟨a, b, ha, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ 5 * a = 1 + (p - 1) * b := by
    rcases Nat.lt_or_ge (p - 1) 2 with h | h
    · exact ⟨1, 4, le_rfl, by omega⟩
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
      refine ⟨m, 5 * m / (p - 1), ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos m with h0 | h0
        · simp [h0] at hm
        · exact h0
      · have := Nat.div_add_mod (5 * m) (p - 1)
        rw [hm] at this
        linarith
  have hinv : ∀ x : ZMod p, (x ^ 5) ^ a = x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, zero_pow (by norm_num), zero_pow (by omega)]
    · rw [← pow_mul, hab, pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow,
        mul_one]
  have hinj : Function.Injective (fun x : ZMod p => x ^ 5 + 3) := by
    intro x y h
    have h' : x ^ 5 = y ^ 5 := add_right_cancel h
    rw [← hinv x, ← hinv y, h']
  exact Finite.injective_iff_bijective.mp hinj

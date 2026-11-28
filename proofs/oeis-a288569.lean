import OMAStatements.S_oeis_a288569
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-! OEIS A288569, conjectures 2, 3 and 4, for `f = a087207`, `f m = ∑_{p ∣ m} 2 ^ count Prime p`.

The prime `2` contributes `2 ^ 0 = 1` and every odd prime contributes an even power of `2`. Hence
`f (2 ^ k) = 1`, `f p = 2 ^ c` with `c ≥ 1` for an odd prime `p`, `f 1 = 0`, `f m ≥ 1` for
`m ≥ 2`, `f m` is even for odd `m` and odd for even `m ≥ 2`. Along the orbit of an odd `n > 1`,
every term before the last nonzero one is at least `2`, so the parities alternate starting from
odd; the last nonzero term is `1`, which is odd, so the number of steps is odd. -/

namespace OpenMath.A288569

open OMA.S_oeis_a288569

private theorem count_two : Nat.count Nat.Prime 2 = 0 := by
  simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]

private theorem one_le_count (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    1 ≤ Nat.count Nat.Prime p := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have e : Nat.count Nat.Prime 3 = 1 := by
    simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  rw [← e]
  exact Nat.count_monotone _ h3

private theorem two_dvd_term (x p : ℕ) (hp : p ∈ x.primeFactors) (h2 : p ≠ 2) :
    2 ∣ 2 ^ Nat.count Nat.Prime p := by
  have := one_le_count p (Nat.prime_of_mem_primeFactors hp) h2
  exact dvd_pow_self 2 (by omega)

private theorem f_le_one (x : ℕ) (hx : x ≤ 1) : a087207 x = 0 := by
  interval_cases x <;> simp [a087207]

private theorem one_le_f (x : ℕ) (hx : 2 ≤ x) : 1 ≤ a087207 x := by
  have hmem : x.minFac ∈ x.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd x, by omega⟩
  calc 1 ≤ 2 ^ Nat.count Nat.Prime x.minFac := Nat.one_le_two_pow
    _ ≤ ∑ p ∈ x.primeFactors, 2 ^ Nat.count Nat.Prime p :=
        Finset.single_le_sum (f := fun p => 2 ^ Nat.count Nat.Prime p)
          (fun _ _ => Nat.zero_le _) hmem

private theorem f_odd (x : ℕ) (hx : x % 2 = 1) : a087207 x % 2 = 0 := by
  have : 2 ∣ ∑ p ∈ x.primeFactors, 2 ^ Nat.count Nat.Prime p :=
    Finset.dvd_sum fun p hp => two_dvd_term x p hp (by
      rintro rfl
      have := (Nat.mem_primeFactors.1 hp).2.1
      omega)
  unfold a087207
  omega

private theorem f_even (x : ℕ) (hx2 : 2 ≤ x) (hx : x % 2 = 0) : a087207 x % 2 = 1 := by
  have hmem : 2 ∈ x.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, by omega, by omega⟩
  have hrest : 2 ∣ ∑ p ∈ x.primeFactors.erase 2, 2 ^ Nat.count Nat.Prime p :=
    Finset.dvd_sum fun p hp =>
      two_dvd_term x p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
  have h : 2 ^ Nat.count Nat.Prime 2 + ∑ p ∈ x.primeFactors.erase 2, 2 ^ Nat.count Nat.Prime p =
      ∑ p ∈ x.primeFactors, 2 ^ Nat.count Nat.Prime p :=
    Finset.add_sum_erase _ (fun p => 2 ^ Nat.count Nat.Prime p) hmem
  unfold a087207
  rw [← h, count_two, pow_zero]
  omega

private theorem f_two_pow (k : ℕ) (hk : 1 ≤ k) : a087207 (2 ^ k) = 1 := by
  unfold a087207
  rw [Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Finset.sum_singleton, count_two,
    pow_zero]

theorem main :
    (∀ k : ℕ, 1 ≤ k → ReachesZeroIn (2 ^ k) 2) ∧
    (∀ p : ℕ, p.Prime → Odd p → ReachesZeroIn p 3) ∧
    (∀ n t : ℕ, 1 < n → Odd n → ¬ n.Prime → ReachesZeroIn n t → Odd t) := by
  refine ⟨fun k hk => ?_, fun p hp hodd => ?_, ?_⟩
  · have h1 := f_two_pow k hk
    refine ⟨?_, fun s hs => ?_⟩
    · show a087207 (a087207 (2 ^ k)) = 0
      rw [h1]
      exact f_le_one 1 le_rfl
    · interval_cases s
      · exact (Nat.two_pow_pos k).ne'
      · show a087207 (2 ^ k) ≠ 0
        rw [h1]
        omega
  · have h2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨r, hr⟩ := hodd
      omega
    have hc := one_le_count p hp h2
    have hfp : a087207 p = 2 ^ Nat.count Nat.Prime p := by
      unfold a087207
      rw [hp.primeFactors, Finset.sum_singleton]
    have h1 := f_two_pow _ hc
    refine ⟨?_, fun s hs => ?_⟩
    · show a087207 (a087207 (a087207 p)) = 0
      rw [hfp, h1]
      exact f_le_one 1 le_rfl
    · interval_cases s
      · exact hp.ne_zero
      · show a087207 p ≠ 0
        rw [hfp]
        exact (Nat.two_pow_pos _).ne'
      · show a087207 (a087207 p) ≠ 0
        rw [hfp, h1]
        omega
  · rintro n t hn hodd - ⟨ht, hlt⟩
    have hodd' : n % 2 = 1 := Nat.odd_iff.1 hodd
    have hsucc : ∀ s, a087207^[s + 1] n = a087207 (a087207^[s] n) := fun s =>
      Function.iterate_succ_apply' a087207 s n
    have hA : ∀ s, s + 1 < t → 2 ≤ a087207^[s] n := by
      intro s hs
      by_contra hcon
      have h1 := hlt (s + 1) hs
      rw [hsucc, f_le_one _ (by omega)] at h1
      exact h1 rfl
    have hB : ∀ s, s < t → a087207^[s] n % 2 = (s + 1) % 2 := by
      intro s
      induction s with
      | zero =>
        intro _
        show n % 2 = (0 + 1) % 2
        omega
      | succ s ih =>
        intro hs
        have h2 := hA s hs
        have ih' := ih (by omega)
        rw [hsucc]
        rcases Nat.mod_two_eq_zero_or_one (a087207^[s] n) with h | h
        · have := f_even _ h2 h
          omega
        · have := f_odd _ h
          omega
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact (show n ≠ 0 by omega) ht
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have hu0 := hlt u (by omega)
    have hu1 : a087207^[u] n = 1 := by
      rcases Nat.lt_or_ge (a087207^[u] n) 2 with h | h
      · omega
      · have := one_le_f _ h
        rw [hsucc] at ht
        omega
    have := hB u (by omega)
    exact Nat.odd_iff.2 (by omega)

end OpenMath.A288569

theorem OMA.solution : type_of% @OMA.S_oeis_a288569.main := OpenMath.A288569.main

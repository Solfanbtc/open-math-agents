import OMAStatements.S_oeis_a179929
import Mathlib

/-!
Proof sketch: stirling2 agrees with Nat.stirlingSecond. By the surjection formula,
j! S2(n,j) = (-1)^j sum_i (-1)^i C(j,i) i^n, and in ZMod k every z satisfies
z^(e + phi k) = z^e for e >= k (prime-power divisors of k; Euler for units).
Take N = 2k. Modulo k the terms with j >= k vanish (k divides j!), and for j < k all of
the exponents n + j, n - j, n are at least k, so each term is unchanged by n -> n + phi k.
-/

namespace R179929
open OMA.S_oeis_a179929

theorem s_eq : ∀ n j : ℕ, stirling2 n j = Nat.stirlingSecond n j
  | 0, 0 => rfl
  | _ + 1, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, j + 1 => by
    rw [stirling2, Nat.stirlingSecond_succ_succ, s_eq n (j + 1), s_eq n j]

def H (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j : ℤ) ^ n

def A (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (j + 1) * (k.choose j : ℤ) * ((j : ℤ) + 1) ^ n

def B (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (j + 1) * (k.choose (j + 1) : ℤ) * ((j : ℤ) + 1) ^ n

theorem h1 (n k : ℕ) : H n (k + 1) = A n k + B n k + (0 : ℤ) ^ n := by
  unfold H A B
  rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ']
    push_cast
    ring
  · simp

theorem h2 (n k : ℕ) : H n k = B n k + (0 : ℤ) ^ n := by
  have e : H n k = ∑ j ∈ Finset.range (k + 1 + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j : ℤ) ^ n := by
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : k < k + 1)]
    simp [H]
  rw [e, Finset.sum_range_succ']
  unfold B
  push_cast
  simp

theorem h3 (n k : ℕ) : H (n + 1) (k + 1) = ((k : ℤ) + 1) * A n k := by
  unfold H A
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_pow (Nat.add_one_ne_zero n), mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hc : ((k : ℤ) + 1) * (k.choose j : ℤ) = ((k + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq k j
  push_cast
  linear_combination (-(-1 : ℤ) ^ (j + 1) * ((j : ℤ) + 1) ^ n) * hc

theorem H_rec (n k : ℕ) : H (n + 1) (k + 1) = ((k : ℤ) + 1) * (H n (k + 1) - H n k) := by
  rw [h3, h1, h2]
  ring

theorem surj (n k : ℕ) :
    H n k = (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    unfold H
    simp only [pow_zero, mul_one]
    rw [Int.alternating_sum_range_choose]
    cases k with
    | zero => simp
    | succ k => simp [Nat.stirlingSecond]
  | succ n ih =>
    cases k with
    | zero => simp [H, Nat.stirlingSecond]
    | succ k =>
      rw [H_rec, ih (k + 1), ih k, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

theorem surj' (n k : ℕ) :
    (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ) = (-1 : ℤ) ^ k * H n k := by
  rw [surj]
  have hsq : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, pow_mul']
    simp
  linear_combination (-(k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ)) * hsq

theorem geuler {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : m ≤ n) (j : ℕ) :
    (j : ZMod m) ^ (n + m.totient) = (j : ZMod m) ^ n := by
  have hn1 : n ≠ 0 := by omega
  have hle : j ^ n ≤ j ^ (n + m.totient) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [zero_pow hn1]
    · exact Nat.pow_le_pow_right hj (Nat.le_add_right _ _)
  have hd : m ∣ j ^ (n + m.totient) - j ^ n := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hk : k ≤ n := by
      have e1 : p ^ k ≤ m := Nat.le_of_dvd hm hpk
      have e2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      omega
    by_cases hpj : p ∣ j
    · apply Nat.dvd_sub
      · exact (pow_dvd_pow p (by omega)).trans (pow_dvd_pow_of_dvd hpj _)
      · exact (pow_dvd_pow p hk).trans (pow_dvd_pow_of_dvd hpj _)
    · have hcop : Nat.Coprime j (p ^ k) :=
        Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj).symm
      have he := Nat.ModEq.pow_totient hcop
      obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hpk
      have hmod : j ^ n ≡ j ^ (n + m.totient) [MOD p ^ k] := by
        rw [hc, pow_add, pow_mul]
        calc j ^ n = j ^ n * 1 ^ c := by simp
          _ ≡ j ^ n * (j ^ Nat.totient (p ^ k)) ^ c [MOD p ^ k] :=
            Nat.ModEq.mul_left _ (Nat.ModEq.pow _ he.symm)
      exact (Nat.modEq_iff_dvd' hle).mp hmod
  have hmod : j ^ (n + m.totient) ≡ j ^ n [MOD m] := ((Nat.modEq_iff_dvd' hle).mpr hd).symm
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

theorem zeuler {m : ℕ} (hm : 0 < m) {e : ℕ} (he : m ≤ e) (z : ZMod m) :
    z ^ (e + m.totient) = z ^ e := by
  haveI : NeZero m := ⟨by omega⟩
  rw [← ZMod.natCast_zmod_val z]
  exact geuler hm he z.val

theorem key {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : m ≤ n) (k : ℕ) :
    (k.factorial : ZMod m) * (Nat.stirlingSecond (n + m.totient) k : ZMod m) =
      (k.factorial : ZMod m) * (Nat.stirlingSecond n k : ZMod m) := by
  have e : ∀ N : ℕ, (k.factorial : ZMod m) * (Nat.stirlingSecond N k : ZMod m) =
      (((-1 : ℤ) ^ k * H N k : ℤ) : ZMod m) := by
    intro N
    rw [← surj']
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [e, e]
  unfold H
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sum,
    Int.cast_natCast, geuler hm hn]

theorem fact0 {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : m ≤ j) : (j.factorial : ZMod m) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_factorial hm hj

theorem a_ext (n M : ℕ) (hM : n + 1 ≤ M) : a n = ∑ j ∈ Finset.range M,
    (-1 : ℤ) ^ (n + j) * (3 : ℤ) ^ (n - j) * (2 : ℤ) ^ j * (stirling2 n j * j.factorial : ℤ) := by
  unfold a
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx'
    simp only [Finset.mem_range, not_lt] at hx'
    rw [s_eq, Nat.stirlingSecond_eq_zero_of_lt (by omega)]
    simp

theorem step (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : 2 * k ≤ n) :
    (a (n + k.totient) : ZMod k) = (a n : ZMod k) := by
  rw [a, a_ext n (n + k.totient + 1) (by omega)]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.lt_or_ge j k with hjk | hjk
  · have e1 : n + k.totient + j = (n + j) + k.totient := by omega
    have e2 : n + k.totient - j = (n - j) + k.totient := by omega
    rw [e1, e2, zeuler hk (by omega : k ≤ n + j), zeuler hk (by omega : k ≤ n - j), s_eq, s_eq]
    have hkey := key hk (by omega : k ≤ n) j
    linear_combination ((-1 : ZMod k) ^ (n + j) * (3 : ZMod k) ^ (n - j) * (2 : ZMod k) ^ j) * hkey
  · rw [fact0 hk hjk]
    simp

end R179929

theorem OMA.solution : type_of% @OMA.S_oeis_a179929.main := by
  intro k hk
  refine ⟨2 * k, fun n hn => ?_⟩
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (R179929.step k (by omega) n hn)

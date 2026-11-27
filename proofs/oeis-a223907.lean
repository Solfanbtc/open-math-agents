import OMAStatements.S_oeis_a223907
import Mathlib

/-!
The unsigned Stirling numbers |s(4,m)|, m = 0..4, are 0, 6, 11, 6, 1, so
a(n) = 6*2^n + 11*3^n + 6*4^n + 5^n, which is the closed form.
Each geometric series G_c = Sum c^n x^n satisfies G_c * (1 - c x) = 1, and
A = 6 G_2 + 11 G_3 + 6 G_4 + G_5 - 24, so the g.f. identity is a linear combination of these.
-/

namespace R223907
open OMA.S_oeis_a223907 PowerSeries

theorem a_eq (n : ℕ) : a n = 6 * 2 ^ n + 11 * 3 ^ n + 6 * 4 ^ n + 5 ^ n := by
  have s0 : Nat.stirlingFirst 4 0 = 0 := by decide
  have s1 : Nat.stirlingFirst 4 1 = 6 := by decide
  have s2 : Nat.stirlingFirst 4 2 = 11 := by decide
  have s3 : Nat.stirlingFirst 4 3 = 6 := by decide
  have s4 : Nat.stirlingFirst 4 4 = 1 := by decide
  simp only [a, hatc, Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3, s4]
  push_cast
  ring

theorem closed (n : ℕ) : a n = 3 * 2 ^ (1 + n) + 3 * 2 ^ (1 + 2 * n) + 11 * 3 ^ n + 5 ^ n := by
  have h : (2 : ℤ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [a_eq, pow_add, pow_add, h]
  ring

theorem geom (c : ℤ) (q : ℤ⟦X⟧) (hq : q = C c) : (mk fun n => c ^ n) * (1 - q * X) = 1 := by
  subst hq
  ext n
  rw [mul_sub, mul_one,
    show (mk fun n => c ^ n) * (C c * X) = C c * ((mk fun n => c ^ n) * X) by ring,
    map_sub, coeff_C_mul, coeff_one]
  rcases n with _ | n
  · rw [coeff_zero_mul_X, coeff_mk]
    simp
  · have hn : n + 1 ≠ 0 := by omega
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, if_neg hn, pow_succ]
    ring

theorem A_eq : A = C 6 * (mk fun n => (2 : ℤ) ^ n) + C 11 * (mk fun n => (3 : ℤ) ^ n) +
    C 6 * (mk fun n => (4 : ℤ) ^ n) + (mk fun n => (5 : ℤ) ^ n) - C 24 := by
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mk, coeff_C]
  rcases n with _ | n
  · norm_num
  · have hn : n + 1 ≠ 0 := by omega
    rw [if_neg hn, if_neg hn, a_eq]
    ring

end R223907

open OMA.S_oeis_a223907 R223907 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a223907.main := by
  refine ⟨fun n _ => closed n, ?_⟩
  have h2 := geom 2 2 (by simp)
  have h3 := geom 3 3 (by simp)
  have h4 := geom 4 4 (by simp)
  have h5 := geom 5 5 (by simp)
  rw [A_eq]
  simp only [map_ofNat]
  linear_combination (6 * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X)) * h2 +
    (11 * (1 - 2 * X) * (1 - 4 * X) * (1 - 5 * X)) * h3 +
    (6 * (1 - 2 * X) * (1 - 3 * X) * (1 - 5 * X)) * h4 +
    ((1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) * h5

import OMAStatements.S_oeis_a067057
import Mathlib

/-!
Let `g(s) = Σ_{S ⊆ s} (Σ S) * (Σ (s \ S))`. Splitting the subsets of `insert b s` by whether they
contain `b` gives `g(insert b s) = 2 g(s) + 2^|s| * b * Σ s`. With `s = {1,...,n}` this is
`G(n+1) = 2 G(n) + 2^n (n+1) n(n+1)/2`, whence `48 G(n) = 2^n (n-1) n (n+1) (3n+2)` and
`96 a(n) = 2^n (n-1) n (n+1) (3n+2)`. This closed form is killed by `(1 - 2x)^5`, which gives the
g.f. coefficientwise.
-/

namespace R067057
open OMA.S_oeis_a067057 PowerSeries

/-- The full (doubled) sum over the subsets of a finset. -/
def g (s : Finset ℕ) : ℕ := ∑ S ∈ s.powerset, (∑ i ∈ S, i) * (∑ i ∈ s \ S, i)

theorem g_insert (s : Finset ℕ) (b : ℕ) (hb : b ∉ s) :
    g (insert b s) = 2 * g s + 2 ^ s.card * (b * ∑ i ∈ s, i) := by
  unfold g
  rw [Finset.sum_powerset_insert hb]
  have h1 : ∀ t ∈ s.powerset,
      (∑ i ∈ t, i) * (∑ i ∈ insert b s \ t, i) +
        (∑ i ∈ insert b t, i) * (∑ i ∈ insert b s \ insert b t, i) =
      2 * ((∑ i ∈ t, i) * (∑ i ∈ s \ t, i)) + b * ∑ i ∈ s, i := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have hbt : b ∉ t := fun h => hb (ht h)
    have hbst : b ∉ s \ t := fun h => hb (Finset.mem_sdiff.mp h).1
    rw [Finset.insert_sdiff_of_notMem s hbt, Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem hb, Finset.sum_insert hbt, Finset.sum_insert hbst,
      ← Finset.sum_sdiff ht]
    ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h1, Finset.sum_add_distrib,
    ← Finset.mul_sum s.powerset (fun t => (∑ i ∈ t, i) * (∑ i ∈ s \ t, i)) 2, Finset.sum_const,
    Finset.card_powerset, smul_eq_mul]

theorem Icc_succ (n : ℕ) : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem sum_Icc (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero => rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]; simp
  | succ n ih =>
    rw [Icc_succ, Finset.sum_insert (show n + 1 ∉ Finset.Icc 1 n by simp only [Finset.mem_Icc]; omega),
      mul_add, ih]
    ring

theorem G_succ (n : ℕ) : g (Finset.Icc 1 (n + 1)) =
    2 * g (Finset.Icc 1 n) + 2 ^ n * ((n + 1) * ∑ i ∈ Finset.Icc 1 n, i) := by
  rw [Icc_succ, g_insert (Finset.Icc 1 n) (n + 1) (by simp only [Finset.mem_Icc]; omega), Nat.card_Icc, Nat.add_sub_cancel]

theorem G_closed (n : ℕ) :
    48 * (g (Finset.Icc 1 n) : ℤ) = 2 ^ n * ((n : ℤ) - 1) * n * (n + 1) * (3 * n + 2) := by
  induction n with
  | zero => rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]; simp [g]
  | succ n ih =>
    have h1 : (g (Finset.Icc 1 (n + 1)) : ℤ) = 2 * g (Finset.Icc 1 n) +
        2 ^ n * ((n + 1) * ∑ i ∈ Finset.Icc 1 n, (i : ℤ)) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) (G_succ n)
      push_cast at e
      linear_combination e
    have h2 : 2 * ∑ i ∈ Finset.Icc 1 n, (i : ℤ) = n * (n + 1) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) (sum_Icc n)
      push_cast at e
      linear_combination e
    push_cast
    linear_combination 48 * h1 + 2 * ih + 24 * 2 ^ n * ((n : ℤ) + 1) * h2

theorem G_even (n : ℕ) : 2 ∣ g (Finset.Icc 1 n) := by
  rcases n with _ | n
  · rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]
    simp [g]
  · rw [G_succ]
    apply dvd_add (dvd_mul_right 2 _)
    rcases n with _ | n
    · rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]
      simp
    · rw [pow_succ]
      exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

theorem a_closed (n : ℕ) :
    96 * (a n : ℤ) = 2 ^ n * ((n : ℤ) - 1) * n * (n + 1) * (3 * n + 2) := by
  have h : 2 * a n = g (Finset.Icc 1 n) := Nat.mul_div_cancel' (G_even n)
  have h' : 2 * (a n : ℤ) = g (Finset.Icc 1 n) := by exact_mod_cast h
  linear_combination 48 * h' + G_closed n

end R067057

open OMA.S_oeis_a067057 R067057 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a067057.main := by
  have e0 : (a 0 : ℤ) = 0 := by have := a_closed 0; norm_num at this; linarith
  have e1 : (a 1 : ℤ) = 0 := by have := a_closed 1; norm_num at this; linarith
  have e2 : (a 2 : ℤ) = 2 := by have := a_closed 2; norm_num at this; linarith
  have e3 : (a 3 : ℤ) = 22 := by have := a_closed 3; norm_num at this; linarith
  have e4 : (a 4 : ℤ) = 140 := by have := a_closed 4; norm_num at this; linarith
  have hA : A = mk (fun n => (a n : ℤ)) := by
    ext n
    simp only [A, coeff_mk]
    by_cases h : n = 0
    · subst h
      rw [if_pos rfl, e0]
    · rw [if_neg h]
  rw [hA,
    show ((2 * X - 1) ^ 5 : PowerSeries ℤ)
      = C 32 * X ^ 5 - C 80 * X ^ 4 + C 80 * X ^ 3 - C 40 * X ^ 2 + C 10 * X ^ 1 - 1 by
        simp only [map_ofNat]; ring,
    show (-2 * X ^ 2 * (X + 1) : PowerSeries ℤ) = -(C 2 * X ^ 3 + C 2 * X ^ 2) by
        simp only [map_ofNat]; ring,
    show ∀ p : PowerSeries ℤ,
      p * (C 32 * X ^ 5 - C 80 * X ^ 4 + C 80 * X ^ 3 - C 40 * X ^ 2 + C 10 * X ^ 1 - 1)
        = C 32 * (p * X ^ 5) - C 80 * (p * X ^ 4) + C 80 * (p * X ^ 3) - C 40 * (p * X ^ 2)
          + C 10 * (p * X ^ 1) - p from fun p => by ring]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one,
    coeff_C, coeff_mk]
  match n with
  | 0 => norm_num [e0]
  | 1 => norm_num [e0, e1]
  | 2 => norm_num [e0, e1, e2]
  | 3 => norm_num [e0, e1, e2, e3]
  | 4 => norm_num [e0, e1, e2, e3, e4]
  | n + 5 =>
    have h0 := a_closed n
    have h1 := a_closed (n + 1)
    have h2 := a_closed (n + 2)
    have h3 := a_closed (n + 3)
    have h4 := a_closed (n + 4)
    have h5 := a_closed (n + 5)
    push_cast at h1 h2 h3 h4 h5
    have key : 96 * (32 * (a n : ℤ) - 80 * a (n + 1) + 80 * a (n + 2) - 40 * a (n + 3)
        + 10 * a (n + 4) - a (n + 5)) = 0 := by
      linear_combination 32 * h0 - 80 * h1 + 80 * h2 - 40 * h3 + 10 * h4 - h5
    simp only [show 5 ≤ n + 5 by omega, show 4 ≤ n + 5 by omega, show 3 ≤ n + 5 by omega,
      show 2 ≤ n + 5 by omega, show 1 ≤ n + 5 by omega, ↓reduceIte,
      show n + 5 - 5 = n by omega, show n + 5 - 4 = n + 1 by omega,
      show n + 5 - 3 = n + 2 by omega, show n + 5 - 2 = n + 3 by omega,
      show n + 5 - 1 = n + 4 by omega, show n + 5 ≠ 3 by omega, show n + 5 ≠ 2 by omega,
      show n + 2 ≠ 0 by omega, show n + 3 ≠ 0 by omega]
    linarith

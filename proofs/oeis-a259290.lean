import OMAStatements.S_oeis_a259290
import Mathlib

/-!
Rows are `Fin 2 → Bool`; `OK r x` is the block condition for consecutive rows `r, x`. With the
transfer operator `T f r = ∑ x, [OK r x] f x` and `E m = T^m 1`, appending a row gives
`a (L + m) = S L (E m)`. A linear identity between the `E m` holds on every row
(`decide +kernel`), which gives the recurrence of `a`; the generating function follows by
coefficient shifting and the closed form by induction, using `√17 ^ 2 = 17`.
-/

namespace R259290
open OMA.S_oeis_a259290

abbrev Row := Fin 2 → Bool

abbrev OK (r x : Row) : Prop := validBlock (r 0) (r 1) (x 1) (x 0)

def vals : List Bool := [false, true]

theorem vals_sum (h : Bool → ℕ) : ∑ v : Bool, h v = (vals.map h).sum := by
  rw [Fintype.sum_bool]
  simp [vals, add_comm]

def rsum (g : Row → ℕ) : ℕ := (vals.map (fun a => (vals.map (fun b => g ![a, b])).sum)).sum

theorem rsum_eq (g : Row → ℕ) : ∑ x : Row, g x = rsum g := by
  have e : ∀ u v : Bool, (piFinTwoEquiv fun _ => Bool).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [e, vals_sum]
  rfl

def T (f : Row → ℕ) (r : Row) : ℕ := rsum (fun x => if OK r x then f x else 0)

def E : ℕ → Row → ℕ
  | 0 => fun _ => 1
  | m + 1 => T (E m)

def S (L : ℕ) (f : Row → ℕ) : ℕ :=
  ∑ A : Fin (L + 1) → Row,
    if (∀ i : Fin L, OK (A i.castSucc) (A i.succ)) then f (A (Fin.last L)) else 0

theorem valid_snoc {L : ℕ} (w : Fin (L + 1) → Row) (x : Row) :
    (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ)) ↔
      (∀ i : Fin L, OK (w i.castSucc) (w i.succ)) ∧ OK (w (Fin.last L)) x := by
  have h1 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc = w i.castSucc :=
    fun i => by rw [Fin.snoc_castSucc]
  have h2 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.succ = w i.succ :=
    fun i => by rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  have h3 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).castSucc = w (Fin.last L) := by
    rw [Fin.snoc_castSucc]
  have h4 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ = x := Fin.snoc_last ..
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      rwa [h1, h2] at hi
    · have hl := h (Fin.last L)
      rwa [h3, h4] at hl
  · rintro ⟨hw, hx⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [h1, h2]
      exact hw j
    · rw [h3, h4]
      exact hx

theorem step_w {L : ℕ} (w : Fin (L + 1) → Row) (f : Row → ℕ) :
    (∑ x : Row, if (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ))
      then f (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1))) else 0) =
    if (∀ i : Fin L, OK (w i.castSucc) (w i.succ)) then T f (w (Fin.last L)) else 0 := by
  rw [T, ← rsum_eq]
  by_cases hw : ∀ i : Fin L, OK (w i.castSucc) (w i.succ)
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : OK (w (Fin.last L)) x
    · rw [if_pos ((valid_snoc w x).2 ⟨hw, hx⟩), if_pos hx, Fin.snoc_last]
    · rw [if_neg (fun h => hx ((valid_snoc w x).1 h).2), if_neg hx]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hw ((valid_snoc w x).1 h).1))

theorem pull (L : ℕ) (f : Row → ℕ) : S (L + 1) f = S L (T f) := by
  have he : S (L + 1) f = ∑ p : Row × (Fin (L + 1) → Row),
      if (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) p.2 p.1 i.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ))
      then f (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1))) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Row)
      (fun A : Fin (L + 1 + 1) → Row =>
        if (∀ i : Fin (L + 1), OK (A i.castSucc) (A i.succ))
        then f (A (Fin.last (L + 1))) else 0)).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  unfold S
  exact Finset.sum_congr rfl (fun w _ => step_w w f)

theorem iter (m : ℕ) : ∀ L, S (L + m) (fun _ => 1) = S L (E m) := by
  induction m with
  | zero => intro L; rfl
  | succ m ih =>
    intro L
    rw [show L + (m + 1) = L + 1 + m by omega, ih (L + 1)]
    exact pull L (E m)

theorem S0 (f : Row → ℕ) : S 0 f = ∑ r, f r := by
  rw [← (Equiv.funUnique (Fin 1) Row).sum_comp f]
  unfold S
  refine Fintype.sum_congr _ _ (fun A => ?_)
  have h0 : ∀ i : Fin 0, OK (A i.castSucc) (A i.succ) := fun i => Fin.elim0 i
  exact (if_pos h0).trans rfl

theorem card_eq (n : ℕ) : A259290 n = S n (fun _ => 1) := by
  rw [A259290, Finset.card_filter, ← (Equiv.curry (Fin (n + 1)) (Fin 2) Bool).symm.sum_comp]
  unfold S
  exact Finset.sum_congr rfl (fun B _ => if_congr Iff.rfl rfl rfl)

theorem a_E (L m : ℕ) : A259290 (L + m) = S L (E m) := (card_eq _).trans (iter m L)

theorem a_val (m : ℕ) : A259290 m = rsum (E m) := by
  have h := a_E 0 m
  rw [Nat.zero_add, S0, rsum_eq] at h
  exact h

theorem ident (r : Row) : E 2 r = E 1 r + 4 * E 0 r := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : Bool, r = ![u, v] := ⟨r 0, r 1, by funext i; fin_cases i <;> rfl⟩
  revert u v
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 2) = S L (E 1) + 4 * S L (E 0) := by
  unfold S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, OK (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact ident _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem a_rec (L : ℕ) : A259290 (L + 3) = A259290 (L + 2) + 4 * A259290 (L + 1) := by
  have h := rec_S (L + 1)
  rw [← a_E, ← a_E, ← a_E] at h
  exact h

theorem a1 : A259290 1 = 10 := by
  rw [a_val]
  decide +kernel

theorem a2 : A259290 2 = 26 := by
  rw [a_val]
  decide +kernel

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A259290 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A259290 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259290 n : ℤ)) =
      2 * PowerSeries.X * (5 + 8 * PowerSeries.X) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259290 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 10 + PowerSeries.X * Bs 2 := by rw [shiftB, a1]; norm_num
  have s2 : Bs 2 = 26 + PowerSeries.X * Bs 3 := by rw [shiftB, a2]; norm_num
  have R : Bs 3 = Bs 2 + PowerSeries.C 4 * Bs 1 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_zero]
    exact_mod_cast a_rec m
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - PowerSeries.X ^ 2) * s1 + (PowerSeries.X ^ 2) * s2 + (PowerSeries.X ^ 3) * R

theorem hD : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem key : ∀ n : ℕ, 1 ≤ n → (A259290 n : ℝ) * Real.sqrt 17 = 2 * (2⁻¹ : ℝ) ^ n * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [a1]
    push_cast
    ring
  | 2, _ => by
    rw [a2]
    push_cast
    linear_combination ((-1 : ℝ) * Real.sqrt 17) * hD
  | n + 3, _ => by
    have i1 := key (n + 2) (by omega)
    have i2 := key (n + 1) (by omega)
    have hr := a_rec n
    have hr' := congrArg (fun z : ℕ => (z : ℝ)) hr
    push_cast at hr'
    linear_combination (Real.sqrt 17) * hr' + (1) * i1 + (4) * i2 + (-(2 * (2⁻¹ : ℝ) ^ (n + 1) * ((1 - Real.sqrt 17) ^ (n + 1) * (-4 + Real.sqrt 17) * (((1 : ℝ) / 4))) + 2 * (2⁻¹ : ℝ) ^ (n + 1) * ((1 + Real.sqrt 17) ^ (n + 1) * (4 + Real.sqrt 17) * (((1 : ℝ) / 4))))) * hD

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (A259290 n : ℝ) =
      ((2 : ℝ) ^ (1 - (n : ℤ)) *
        ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17 := by
  have hs : Real.sqrt 17 ≠ 0 := by positivity
  rw [eq_div_iff hs, key n hn, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast,
    div_eq_mul_inv, ← inv_pow]
  all_goals ring

end R259290

theorem OMA.solution : type_of% @OMA.S_oeis_a259290.main := ⟨R259290.ps, R259290.closed⟩

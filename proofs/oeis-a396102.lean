import OMAStatements.S_oeis_a396102
import Mathlib

namespace R396102
open OMA.S_oeis_a396102

theorem pow_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : ℕ → R) :
    ∀ k n, f (powSeq g k n) = powSeq (fun i => f (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; simp only [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

theorem cmp_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u g : ℕ → R) (n : ℕ) :
    f (comp u g n) = comp (fun i => f (u i)) (fun i => f (g i)) n := by
  simp only [comp, map_sum, map_mul, pow_map]

theorem it_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : ℕ → R) :
    ∀ r n, f (iterComp u r n) = iterComp (fun i => f (u i)) r n := by
  intro r
  induction r with
  | zero => intro n; simp only [iterComp]; split_ifs <;> simp
  | succ r ih => intro n; simp only [iterComp, cmp_map, ih]

theorem pow_congr {R : Type*} [CommRing R] (g g' : ℕ → R) (N : ℕ) (h : ∀ j ≤ N, g j = g' j) :
    ∀ k n, n ≤ N → powSeq g k n = powSeq g' k n := by
  intro k
  induction k with
  | zero => intro n _; simp only [powSeq]
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [h i (le_trans hi' hn), ih (n - i) (le_trans (Nat.sub_le n i) hn)]

theorem cmp_congr {R : Type*} [CommRing R] (u u' g g' : ℕ → R) (N : ℕ)
    (hu : ∀ j ≤ N, u j = u' j) (hg : ∀ j ≤ N, g j = g' j) :
    ∀ n, n ≤ N → comp u g n = comp u' g' n := by
  intro n hn
  simp only [comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hu k (le_trans hk' hn), pow_congr g g' N hg k n hn]

theorem it_congr {R : Type*} [CommRing R] (u u' : ℕ → R) (N : ℕ)
    (hu : ∀ j ≤ N, u j = u' j) : ∀ r n, n ≤ N → iterComp u r n = iterComp u' r n := by
  intro r
  induction r with
  | zero => intro n _; simp only [iterComp]
  | succ r ih =>
    intro n hn
    simp only [iterComp]
    exact cmp_congr u u' _ _ N hu ih n hn

theorem pow_low {R : Type*} [CommRing R] (g : ℕ → R) (hg : g 0 = 0) :
    ∀ k n, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [hg, zero_mul]
    · rw [ih (n - i) (by omega), mul_zero]

def cm {R : Type*} [CommRing R] (m : R) (n : ℕ) : R := if n = 0 then 0 else m ^ (n - 1)

theorem cm_zero {R : Type*} [CommRing R] (m : R) : cm m 0 = 0 := by simp [cm]

theorem cm_succ {R : Type*} [CommRing R] (m : R) (i : ℕ) :
    cm m (i + 1) = (if i = 0 then 1 else 0) + m * cm m i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [cm]
  · have hi : i ≠ 0 := Nat.pos_iff_ne_zero.mp h
    simp [cm, hi, mul_pow_sub_one hi]

theorem pow_rec {R : Type*} [CommRing R] (m : R) (c : ℕ → R) (h0 : c 0 = 0)
    (hs : ∀ i, c (i + 1) = (if i = 0 then 1 else 0) + m * c i) (k n : ℕ) :
    powSeq c (k + 1) (n + 1) = powSeq c k n + m * powSeq c (k + 1) n := by
  have e1 : powSeq c (k + 1) (n + 1) =
      ∑ i ∈ Finset.range (n + 1 + 1), c i * powSeq c k (n + 1 - i) := rfl
  have e2 : powSeq c (k + 1) n = ∑ i ∈ Finset.range (n + 1), c i * powSeq c k (n - i) := rfl
  rw [e1, e2, Finset.sum_range_succ' (fun i => c i * powSeq c k (n + 1 - i)) (n + 1), h0,
    zero_mul, add_zero]
  simp [hs, Nat.add_sub_add_right, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

theorem cmp_one {R : Type*} [CommRing R] (c : ℕ → R) (n : ℕ) :
    comp (cm (1 : R)) c n = ∑ k ∈ Finset.range n, powSeq c (k + 1) n := by
  rw [comp, Finset.sum_range_succ']
  simp [cm]

theorem cmp_cm_succ {R : Type*} [CommRing R] (m : R) (n : ℕ) :
    comp (cm (1 : R)) (cm m) (n + 1) =
      (if n = 0 then 1 else 0) + (m + 1) * comp (cm (1 : R)) (cm m) n := by
  have hrec := pow_rec m (cm m) (cm_zero m) (cm_succ m)
  have hord := pow_low (cm m) (cm_zero m)
  rw [cmp_one, cmp_one]
  simp only [hrec, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ' (fun k => powSeq (cm m) k n),
    Finset.sum_range_succ (fun k => powSeq (cm m) (k + 1) n), hord (n + 1) n (Nat.lt_succ_self n)]
  have h0 : powSeq (cm m) 0 n = if n = 0 then 1 else 0 := rfl
  rw [h0]
  ring

theorem cmp_cm {R : Type*} [CommRing R] (m : R) :
    ∀ n, comp (cm (1 : R)) (cm m) n = cm (m + 1) n := by
  intro n
  induction n with
  | zero => simp [comp, cm]
  | succ n ih => rw [cmp_cm_succ, ih, cm_succ]

theorem it_cm {R : Type*} [CommRing R] :
    ∀ (r : ℕ) n, iterComp (cm (1 : R)) r n = cm (r : R) n := by
  intro r
  induction r with
  | zero =>
    intro n
    rcases n with _ | n
    · simp [iterComp, cm]
    · simp [iterComp, cm, zero_pow_eq]
  | succ r ih =>
    intro n
    have hf : iterComp (cm (1 : R)) r = cm (r : R) := funext ih
    show comp (cm (1 : R)) (iterComp (cm (1 : R)) r) n = _
    rw [hf, cmp_cm, Nat.cast_succ]

theorem pow_one' {R : Type*} [CommRing R] (g : ℕ → R) (m : ℕ) : powSeq g 1 m = g m := by
  show ∑ i ∈ Finset.range (m + 1), g i * powSeq g 0 (m - i) = g m
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (Nat.lt_succ_self m))]
  · simp [powSeq]
  · intro b hb hbm
    have hb' := Finset.mem_range.mp hb
    have hmb : m - b ≠ 0 := by omega
    simp [powSeq, hmb]

theorem pow_diag {R : Type*} [CommRing R] (g : ℕ → R) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    ∀ k, powSeq g k k = 1 := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    show ∑ i ∈ Finset.range (k + 1 + 1), g i * powSeq g k (k + 1 - i) = 1
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]
    · simp [h1, ih]
    · intro b hb hb1
      have hb' := Finset.mem_range.mp hb
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [h0]
      · rw [pow_low g h0 k (k + 1 - b) (by omega), mul_zero]

theorem pow_high {R : Type*} [CommRing R] (g g' : ℕ → R) (n : ℕ) (h0 : g 0 = 0)
    (h : ∀ j ≤ n, g j = g' j) (k : ℕ) (hk : 1 ≤ k) :
    powSeq g (k + 1) (n + 1) = powSeq g' (k + 1) (n + 1) := by
  have h0' : g' 0 = 0 := by rw [← h 0 (Nat.zero_le n), h0]
  show ∑ i ∈ Finset.range (n + 1 + 1), g i * powSeq g k (n + 1 - i) =
    ∑ i ∈ Finset.range (n + 1 + 1), g' i * powSeq g' k (n + 1 - i)
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; rw [h0, h0', zero_mul, zero_mul]
  · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · rw [h i (by omega), pow_congr g g' n h k (n + 1 - i) (by omega)]
    · have hz : n + 1 - i = 0 := by omega
      rw [hz, pow_low g h0 k 0 (by omega), pow_low g' h0' k 0 (by omega), mul_zero, mul_zero]

theorem it_low {R : Type*} [CommRing R] (u : ℕ → R) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ r, iterComp u r 0 = 0 ∧ iterComp u r 1 = 1 := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r ih =>
    constructor
    · show comp u (iterComp u r) 0 = 0
      simp [comp, h0]
    · show comp u (iterComp u r) 1 = 1
      simp [comp, Finset.sum_range_succ, h0, h1, pow_one', ih.2]

theorem it_lin {R : Type*} [CommRing R] (u v : ℕ → R) (n : ℕ) (hn : 1 ≤ n)
    (hu0 : u 0 = 0) (hu1 : u 1 = 1) (hv0 : v 0 = 0) (hv1 : v 1 = 1)
    (h : ∀ j ≤ n, u j = v j) :
    ∀ r : ℕ, iterComp u r (n + 1) - iterComp v r (n + 1) = (r : R) * (u (n + 1) - v (n + 1)) := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r ih =>
    have hU := it_low u hu0 hu1 r
    have hV := it_low v hv0 hv1 r
    have hUV : ∀ j ≤ n, iterComp u r j = iterComp v r j := fun j hj => it_congr u v n h r j hj
    show comp u (iterComp u r) (n + 1) - comp v (iterComp v r) (n + 1) = _
    simp only [comp]
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_add_of_mem 1 (n + 1) (Finset.mem_range.mpr (by omega))
        (Finset.mem_range.mpr (by omega)) (by omega)]
    · rw [pow_one', pow_one', hu1, hv1, pow_diag _ hU.1 hU.2, pow_diag _ hV.1 hV.2]
      push_cast
      linear_combination ih
    · intro c hc hc2
      have hc' := Finset.mem_range.mp hc
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · subst hc0; simp [hu0, hv0]
      · obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
        rw [h (k + 1) (by omega), pow_high _ _ n hU.1 hUV k (by omega)]
        exact sub_self _

theorem B_eq (n : ℕ) : iterComp (cm (1 : ZMod 3)) 3 (n + 1) =
    iterComp (cm (1 : ZMod 3)) 2 (n + 1) + iterComp (cm (1 : ZMod 3)) 2 n := by
  rw [it_cm, it_cm, it_cm]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  have h2 : ((2 : ℕ) : ZMod 3) = 2 := by decide
  have h33 : (3 : ZMod 3) = 0 := by decide
  rw [h3, h2]
  rcases n with _ | m
  · simp [cm]
  · rw [cm_succ (0 : ZMod 3) (m + 1), cm_succ (2 : ZMod 3) (m + 1), if_neg (by omega : m + 1 ≠ 0)]
    linear_combination (-(cm (2 : ZMod 3) (m + 1))) * h33

theorem cast_eq3 (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hrec : ∀ n : ℕ, iterComp a 3 (n + 1) = iterComp a 2 (n + 1) + iterComp a 2 n) :
    ∀ n, ((a n : ℤ) : ZMod 3) = cm (1 : ZMod 3) n := by
  have hE : ∀ n, iterComp (fun i => ((a i : ℤ) : ZMod 3)) 3 (n + 1) =
      iterComp (fun i => ((a i : ℤ) : ZMod 3)) 2 (n + 1) +
        iterComp (fun i => ((a i : ℤ) : ZMod 3)) 2 n := by
    intro n
    have hh := congrArg (Int.castRingHom (ZMod 3)) (hrec n)
    rw [map_add, it_map, it_map, it_map] at hh
    simpa only [eq_intCast] using hh
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [ha0, cm]
      · simp [ha1, cm]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hag : ∀ j ≤ m, ((a j : ℤ) : ZMod 3) = cm (1 : ZMod 3) j :=
        fun j hj => ih j (by omega)
      have hc0 : cm (1 : ZMod 3) 0 = 0 := cm_zero 1
      have hc1 : cm (1 : ZMod 3) 1 = 1 := by simp [cm]
      have L3 := it_lin (fun i => ((a i : ℤ) : ZMod 3)) (cm 1) m (by omega) (by simp [ha0])
        (by simp [ha1]) hc0 hc1 hag 3
      have L2 := it_lin (fun i => ((a i : ℤ) : ZMod 3)) (cm 1) m (by omega) (by simp [ha0])
        (by simp [ha1]) hc0 hc1 hag 2
      have Y := it_congr (fun i => ((a i : ℤ) : ZMod 3)) (cm 1) m hag 2 m le_rfl
      have Ea := hE m
      have Eb := B_eq m
      push_cast at L3 L2
      linear_combination L2 - L3 + Ea - Eb + Y

end R396102

theorem OMA.solution : type_of% @OMA.S_oeis_a396102.main := by
  intro a ha0 ha1 hrec n hn
  have h := R396102.cast_eq3 a ha0 ha1 hrec n
  have hn0 : n ≠ 0 := by omega
  have h1 : R396102.cm (1 : ZMod 3) n = 1 := by simp [R396102.cm, hn0]
  rw [h1, ← Int.cast_one] at h
  have h2 := (ZMod.intCast_eq_intCast_iff (a n) 1 3).mp h
  exact_mod_cast h2

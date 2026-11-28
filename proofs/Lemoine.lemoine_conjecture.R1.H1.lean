import OMAReductions.R_Lemoine_lemoine_conjecture_R1

-- Step Lemoine.lemoine_conjecture.R1.H1: hypothesis H1 of reduction Lemoine.lemoine_conjecture.R1
-- Credit: @Solfanbtc

/-! Finite check: trial division by every `d ≥ 2` with `d * d ≤ p` (a fuelled loop, proved sound
with `Nat.prime_def_le_sqrt`), and a scan over `q = 2, 3, …` for a prime `q` with `n - 2 q`
prime, evaluated by the kernel for every odd `7 ≤ n ≤ 10005`, in ten blocks of 500 values. -/

namespace OMA.LemoineH1

/-- `trial p k d`: no divisor of `p` among `d, d + 1, …` up to the first `e` with `p < e * e`
(at most `k` candidates are examined). -/
def trial (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, d => if p < d * d then true else (p % d != 0 && trial p k (d + 1))

lemma trial_sound (p : ℕ) : ∀ k d, trial p k d = true →
    ∀ m, d ≤ m → m < d + k → m * m ≤ p → ¬ m ∣ p
  | 0, d, _, m, h1, h2, _, _ => by omega
  | k + 1, d, h, m, h1, h2, h3, hdvd => by
    unfold trial at h
    split_ifs at h with hlt
    · have : d * d ≤ m * m := Nat.mul_le_mul h1 h1
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e
        exact h.1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact trial_sound p k (d + 1) h.2 m e (by omega) h3 hdvd

def isPrimeB (p : ℕ) : Bool := 2 ≤ p && trial p p 2

lemma isPrimeB_sound {p : ℕ} (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h.1, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hmp : m ≤ p := le_trans (Nat.le_mul_self m) hmm
  exact trial_sound p p 2 h.2 m hm (by omega) hmm hdvd

/-- Some `q` among `q₀, q₀ + 1, …` (at most `k` of them) has `q` and `n - 2 q` prime. -/
def lem (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | q, k + 1 => (2 * q ≤ n && isPrimeB q && isPrimeB (n - 2 * q)) || lem n (q + 1) k

lemma lem_sound (n : ℕ) : ∀ k q, lem n q k = true →
    ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧ p + 2 * q = n
  | 0, q, h => by simp [lem] at h
  | k + 1, q, h => by
    simp only [lem, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩ | h
    · exact ⟨n - 2 * q, q, isPrimeB_sound h3, isPrimeB_sound h2, by omega⟩
    · exact lem_sound n k (q + 1) h

def hasRep (n : ℕ) : Bool := lem n 2 n

lemma c0 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 0 + i)) = true := by decide +kernel
lemma c1 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 1 + i)) = true := by decide +kernel
lemma c2 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 2 + i)) = true := by decide +kernel
lemma c3 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 3 + i)) = true := by decide +kernel
lemma c4 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 4 + i)) = true := by decide +kernel
lemma c5 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 5 + i)) = true := by decide +kernel
lemma c6 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 6 + i)) = true := by decide +kernel
lemma c7 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 7 + i)) = true := by decide +kernel
lemma c8 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 8 + i)) = true := by decide +kernel
lemma c9 : ∀ i ≤ 499, hasRep (7 + 2 * (500 * 9 + i)) = true := by decide +kernel

lemma check (n : ℕ) (h6 : 6 < n) (ho : Odd n) (h : n ≤ 10001) : hasRep n = true := by
  have key : ∀ j < 10, ∀ i ≤ 499, hasRep (7 + 2 * (500 * j + i)) = true := by
    intro j hj
    interval_cases j
    all_goals first | exact c0 | exact c1 | exact c2 | exact c3 | exact c4 | exact c5 | exact c6 | exact c7 | exact c8 | exact c9
  obtain ⟨m, rfl⟩ := ho
  have e : 2 * m + 1 = 7 + 2 * (500 * ((m - 3) / 500) + (m - 3) % 500) := by omega
  rw [e]
  exact key _ (by omega) _ (by omega)

end OMA.LemoineH1

theorem OMA.solution : OMA.R_Lemoine_lemoine_conjecture_R1.H1 := fun n h6 ho h => by
  obtain ⟨p, q, hp, hq, e⟩ := OMA.LemoineH1.lem_sound n n 2 (OMA.LemoineH1.check n h6 ho h)
  exact ⟨p, q, hp, hq, e⟩

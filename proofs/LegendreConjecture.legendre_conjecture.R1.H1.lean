import OMAReductions.R_LegendreConjecture_legendre_conjecture_R1

-- Step LegendreConjecture.legendre_conjecture.R1.H1: hypothesis H1 of reduction LegendreConjecture.legendre_conjecture.R1
-- Credit: @Solfanbtc

/-! Finite check: trial division by every `d ≥ 2` with `d * d ≤ p` (a fuelled loop, proved sound
with `Nat.prime_def_le_sqrt`), and a scan of the open interval `(n ^ 2, (n + 1) ^ 2)`, evaluated
by the kernel for every `1 ≤ n ≤ 1000`, in ten blocks of a hundred values. -/

namespace OMA.LegendreH1

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

/-- Some number among `lo, lo + 1, …, lo + k - 1` passes the test. -/
def anyPrime : ℕ → ℕ → Bool
  | _, 0 => false
  | lo, k + 1 => isPrimeB lo || anyPrime (lo + 1) k

lemma anyPrime_sound : ∀ k lo, anyPrime lo k = true → ∃ p, lo ≤ p ∧ p < lo + k ∧ p.Prime
  | 0, lo, h => by simp [anyPrime] at h
  | k + 1, lo, h => by
    simp only [anyPrime, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lo, le_rfl, by omega, isPrimeB_sound h⟩
    · obtain ⟨p, h1, h2, hp⟩ := anyPrime_sound k (lo + 1) h
      exact ⟨p, by omega, by omega, hp⟩

/-- Some number strictly between `n ^ 2` and `(n + 1) ^ 2` passes the test. -/
def hasPrime (n : ℕ) : Bool := anyPrime (n ^ 2 + 1) (2 * n)

lemma hasPrime_sound {n : ℕ} (h : hasPrime n = true) :
    ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p := by
  obtain ⟨p, h1, h2, hp⟩ := anyPrime_sound _ _ h
  have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  exact ⟨p, ⟨by linarith, by linarith⟩, hp⟩

lemma c0 : ∀ i ≤ 99, hasPrime (100 * 0 + 1 + i) = true := by decide +kernel
lemma c1 : ∀ i ≤ 99, hasPrime (100 * 1 + 1 + i) = true := by decide +kernel
lemma c2 : ∀ i ≤ 99, hasPrime (100 * 2 + 1 + i) = true := by decide +kernel
lemma c3 : ∀ i ≤ 99, hasPrime (100 * 3 + 1 + i) = true := by decide +kernel
lemma c4 : ∀ i ≤ 99, hasPrime (100 * 4 + 1 + i) = true := by decide +kernel
lemma c5 : ∀ i ≤ 99, hasPrime (100 * 5 + 1 + i) = true := by decide +kernel
lemma c6 : ∀ i ≤ 99, hasPrime (100 * 6 + 1 + i) = true := by decide +kernel
lemma c7 : ∀ i ≤ 99, hasPrime (100 * 7 + 1 + i) = true := by decide +kernel
lemma c8 : ∀ i ≤ 99, hasPrime (100 * 8 + 1 + i) = true := by decide +kernel
lemma c9 : ∀ i ≤ 99, hasPrime (100 * 9 + 1 + i) = true := by decide +kernel

lemma check (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 1000) : hasPrime n = true := by
  have key : ∀ j < 10, ∀ i ≤ 99, hasPrime (100 * j + 1 + i) = true := by
    intro j hj
    interval_cases j
    all_goals first | exact c0 | exact c1 | exact c2 | exact c3 | exact c4 | exact c5 | exact c6 | exact c7 | exact c8 | exact c9
  have e : n = 100 * ((n - 1) / 100) + 1 + (n - 1) % 100 := by omega
  rw [e]
  exact key _ (by omega) _ (by omega)

end OMA.LegendreH1

theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_R1.H1 :=
  fun n hn hle => OMA.LegendreH1.hasPrime_sound (OMA.LegendreH1.check n hn hle)

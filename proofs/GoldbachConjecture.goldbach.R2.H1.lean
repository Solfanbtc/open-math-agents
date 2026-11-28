import OMAReductions.R_GoldbachConjecture_goldbach_R2

-- Step GoldbachConjecture.goldbach.R2.H1: hypothesis H1 of reduction GoldbachConjecture.goldbach.R2
-- Credit: @Solfanbtc

/-! Finite check. Every `p < 224 ^ 2 = 50176` that is not divisible by any prime `r` of the
list `P` of the 48 primes up to `223` with `r * r ≤ p` is prime (`P` is checked to contain every
prime below `224`, and a composite `p` has a prime factor `minFac p` with `minFac p ^ 2 ≤ p`).
A scan over `p = 2, 3, …` for primes `p` and `n - p` is then evaluated by the kernel for every
even `4 ≤ n ≤ 50002`, in 25 blocks of 1000 values. -/

namespace OMA.GoldbachH1

/-- The primes up to `223`. -/
def P : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223]

lemma P_complete : ∀ q < 224, q ∈ P ∨ q < 2 ∨ ∃ d < q, 2 ≤ d ∧ q % d = 0 := by decide +kernel

lemma mem_P_of_prime {q : ℕ} (hq : q.Prime) (h : q < 224) : q ∈ P := by
  rcases P_complete q h with h1 | h1 | ⟨d, hd, h2, h3⟩
  · exact h1
  · exact absurd hq.two_le (by omega)
  · have := hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h3)
    omega

/-- Trial division by the primes of `P` up to the square root. -/
def isPrimeL (p : ℕ) : Bool := 2 ≤ p && P.all (fun r => p < r * r || p % r != 0)

lemma isPrimeL_sound {p : ℕ} (hp : p < 50176) (h : isPrimeL p = true) : p.Prime := by
  simp only [isPrimeL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hnp
  have hq := Nat.minFac_prime (show p ≠ 1 by omega)
  have hle : p.minFac * p.minFac ≤ p := by
    have := Nat.minFac_sq_le_self (by omega : 0 < p) hnp
    simpa [sq] using this
  have hlt : p.minFac < 224 := by
    by_contra hc
    have := Nat.mul_le_mul (not_lt.mp hc) (not_lt.mp hc)
    omega
  rcases hall _ (mem_P_of_prime hq hlt) with h3 | h3
  · omega
  · exact h3 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p))

/-- Some `p` among `p₀, p₀ + 1, …` (at most `k` of them) has `p` and `n - p` prime. -/
def gb (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | p, k + 1 => (p ≤ n && isPrimeL p && isPrimeL (n - p)) || gb n (p + 1) k

lemma gb_sound (n : ℕ) (hn : n ≤ 50000) : ∀ k p, gb n p k = true →
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ n = a + b
  | 0, p, h => by simp [gb] at h
  | k + 1, p, h => by
    simp only [gb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩ | h
    · exact ⟨p, n - p, isPrimeL_sound (by omega) h2, isPrimeL_sound (by omega) h3, by omega⟩
    · exact gb_sound n hn k (p + 1) h

def hasGB (n : ℕ) : Bool := gb n 2 n

lemma c0 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 0 + i)) = true := by decide +kernel
lemma c1 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 1 + i)) = true := by decide +kernel
lemma c2 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 2 + i)) = true := by decide +kernel
lemma c3 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 3 + i)) = true := by decide +kernel
lemma c4 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 4 + i)) = true := by decide +kernel
lemma c5 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 5 + i)) = true := by decide +kernel
lemma c6 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 6 + i)) = true := by decide +kernel
lemma c7 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 7 + i)) = true := by decide +kernel
lemma c8 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 8 + i)) = true := by decide +kernel
lemma c9 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 9 + i)) = true := by decide +kernel
lemma c10 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 10 + i)) = true := by decide +kernel
lemma c11 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 11 + i)) = true := by decide +kernel
lemma c12 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 12 + i)) = true := by decide +kernel
lemma c13 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 13 + i)) = true := by decide +kernel
lemma c14 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 14 + i)) = true := by decide +kernel
lemma c15 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 15 + i)) = true := by decide +kernel
lemma c16 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 16 + i)) = true := by decide +kernel
lemma c17 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 17 + i)) = true := by decide +kernel
lemma c18 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 18 + i)) = true := by decide +kernel
lemma c19 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 19 + i)) = true := by decide +kernel
lemma c20 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 20 + i)) = true := by decide +kernel
lemma c21 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 21 + i)) = true := by decide +kernel
lemma c22 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 22 + i)) = true := by decide +kernel
lemma c23 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 23 + i)) = true := by decide +kernel
lemma c24 : ∀ i ≤ 999, hasGB (4 + 2 * (1000 * 24 + i)) = true := by decide +kernel

lemma check (n : ℕ) (h2 : 2 < n) (he : Even n) (h : n ≤ 50000) : hasGB n = true := by
  have key : ∀ j < 25, ∀ i ≤ 999, hasGB (4 + 2 * (1000 * j + i)) = true := by
    intro j hj
    interval_cases j
    all_goals first | exact c0 | exact c1 | exact c2 | exact c3 | exact c4 | exact c5 | exact c6 | exact c7 | exact c8 | exact c9 | exact c10 | exact c11 | exact c12 | exact c13 | exact c14 | exact c15 | exact c16 | exact c17 | exact c18 | exact c19 | exact c20 | exact c21 | exact c22 | exact c23 | exact c24
  obtain ⟨m, rfl⟩ := he
  have e : m + m = 4 + 2 * (1000 * ((m - 2) / 1000) + (m - 2) % 1000) := by omega
  rw [e]
  exact key _ (by omega) _ (by omega)

end OMA.GoldbachH1

theorem OMA.solution : OMA.R_GoldbachConjecture_goldbach_R2.H1 := fun n h2 he h => by
  obtain ⟨a, b, ha, hb, e⟩ := OMA.GoldbachH1.gb_sound n h n 2 (OMA.GoldbachH1.check n h2 he h)
  exact ⟨a, b, Nat.prime_iff.mp ha, Nat.prime_iff.mp hb, e⟩

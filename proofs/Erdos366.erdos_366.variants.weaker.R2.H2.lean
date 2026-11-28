import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R2

/-! A prime `p` dividing `a^3 b^4 c^5` divides `a`, `b` or `c`; writing that factor as `p * d`
exhibits `p^3` as a divisor. -/

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2 := by
  intro a b c _ _ _ p h
  obtain ⟨hp, h, -⟩ := Nat.mem_primeFactors.1 h
  simp only [hp.dvd_mul] at h
  rcases h with (h | h) | h <;> obtain ⟨d, rfl⟩ := hp.dvd_of_dvd_pow h
  · exact ⟨d^3*b^4*c^5, by ring⟩
  · exact ⟨a^3*p*d^4*c^5, by ring⟩
  · exact ⟨a^3*b^4*p^2*d^5, by ring⟩

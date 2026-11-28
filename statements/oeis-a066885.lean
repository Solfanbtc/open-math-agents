import Mathlib

/-!
# A066885: a(n) = (prime(n)^2 + 1)/2.

Source: https://oeis.org/A066885
Credit: @Solfanbtc

The conjecture in this entry is Haga's conjecture, which the comment cites ("a(n) is ... the
average of the primes in a prime(n) X prime(n) example of Haga's conjecture"). Its precise form
is in the companion entry https://oeis.org/A066883 (see also C. Rivera, The Prime Puzzles and
Problems Connection, Conjecture 26, "The Calendar-like square Conjecture", and P. Ribenboim,
The New Book of Prime Number Records, 3rd ed., pp. 397-398):

  if the integers from 1 to p^2 (p prime) are put in a p by p square in standard order, then
  there is a transversal consisting of primes, i.e. a set of p primes containing exactly one
  number in each row and column.

In standard order, the entry in row `i` and column `j` (`0 ≤ i, j < p`) is `i * p + j + 1`. A
transversal picks one cell per row in pairwise distinct columns, i.e. it is given by a
permutation `σ` of the columns. Every transversal has sum `p (p^2 + 1) / 2`, so its average is
`a(n) = (p^2 + 1)/2` for `p = prime(n)`; the content of the conjecture is that a transversal
made only of primes exists.

Checked with python3 (bipartite matching) for every prime `p ≤ 241`. For example `p = 5`:
5, 7, 11, 19, 23. The conjecture is stated for every prime `p`, including `p = 2`
(the transversal 2, 3).
-/

namespace OMA.S_oeis_a066885

/-- Haga's conjecture: for every prime `p`, the `p × p` square holding `1, …, p^2` in
standard order (row `i`, column `j` holds `i * p + j + 1`) has a transversal of primes. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      ∃ σ : Equiv.Perm (Fin p), ∀ i : Fin p, (i.val * p + (σ i).val + 1).Prime := by
  sorry

end OMA.S_oeis_a066885

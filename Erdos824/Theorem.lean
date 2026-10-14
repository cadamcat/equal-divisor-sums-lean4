import Erdos824.Final

/-!
# Erdős Problem 824

Let `h x` count the pairs `1 ≤ a < b < x` that are coprime and have equal divisor sums. For every
`ε > 0`, all sufficiently large `x` satisfy `h x > x ^ (2 - ε)`. This is the right-hand side of
Formal Conjectures' `Erdos824.erdos_824`, with the answer `True`.

`Erdos824.Final.statement` proves `Erdos824.Statement` (`Erdos824/Challenge.lean`), whose body is the
proposition below.
-/

namespace Erdos824

/-- Erdős Problem 824: `h x > x ^ (2 - ε)` for every `ε > 0` and all large `x`. -/
theorem erdos_824 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ) := by
  simpa only [Statement] using Erdos824.Final.statement

end Erdos824


import Mathlib

namespace Erdos708.PrimePowerSupports

/--
If p^(j+1) divides a, then p^j divides a.
This holds for any natural p.
-/
theorem power_support_step
    (p j a : ℕ)
    (h : p ^ (j + 1) ∣ a) :
    p ^ j ∣ a := by
  have hp : p ^ j ∣ p ^ (j + 1) := by
    refine ⟨p, ?_⟩
    simp [pow_succ]
  exact dvd_trans hp h

/--
The supports of higher powers are contained
in the supports of lower powers.
-/
theorem power_support_nested
    (p j k a : ℕ)
    (hjk : j ≤ k)
    (h : p ^ k ∣ a) :
    p ^ j ∣ a := by
  have hp : p ^ j ∣ p ^ k := by
    exact pow_dvd_pow p hjk
  exact dvd_trans hp h

end Erdos708.PrimePowerSupports

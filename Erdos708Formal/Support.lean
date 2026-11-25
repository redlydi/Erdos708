import Mathlib

/-!
# Divisibility supports

A first formal building block for the support-family argument in REPORT.md §3.
All theorems below are elementary and substantially weaker than the claimed
bound τ(A,I) ≤ ∑ w(a). That stronger bound is NOT formalized here.
-/

namespace Erdos708Formal

/-- The elements of a finite family divisible by `d`. -/
def support (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.filter (fun a => d ∣ a)

/-- Exact membership criterion for a support. -/
theorem mem_support_iff (A : Finset ℕ) (d a : ℕ) :
    a ∈ support A d ↔ a ∈ A ∧ d ∣ a := by
  simp [support]

/-- A divisibility support never contains numbers outside the family. -/
theorem support_subset (A : Finset ℕ) (d : ℕ) :
    support A d ⊆ A := by
  intro a ha
  exact ((mem_support_iff A d a).mp ha).1

/-- If `d ∣ e`, the support of `e` lies inside the support of `d`. -/
theorem support_antitone (A : Finset ℕ) {d e : ℕ} (hde : d ∣ e) :
    support A e ⊆ support A d := by
  intro a ha
  rcases (mem_support_iff A e a).mp ha with ⟨haA, hea⟩
  exact (mem_support_iff A d a).mpr ⟨haA, dvd_trans hde hea⟩

/-- Consecutive power-divisibility supports form a nested chain. -/
theorem prime_power_support_nested (A : Finset ℕ) (p j : ℕ) :
    support A (p ^ (j + 1)) ⊆ support A (p ^ j) := by
  apply support_antitone A
  exact ⟨p, (pow_succ p j).symm⟩

/-- The cardinality of a support is at most the size of the original family. -/
theorem support_card_le (A : Finset ℕ) (d : ℕ) :
    (support A d).card ≤ A.card := by
  exact Finset.card_le_card (support_subset A d)

/-- Concrete illustration: among 6, 10, 15, precisely 6 and 10 are even. -/
example : support ({6, 10, 15} : Finset ℕ) 2 = ({6, 10} : Finset ℕ) := by
  decide

/-- A concrete local collision used in the structural report (§2).
Both local requests fit at 210, but their naive extras do not. -/
theorem local_collision_210 :
    30 ∣ 210 ∧ 70 ∣ 210 ∧ ¬ (210 * 2 ∣ 210) ∧ ¬ (210 * 5 ∣ 210) := by
  norm_num

#print axioms mem_support_iff
#print axioms support_antitone
#print axioms prime_power_support_nested
#print axioms support_card_le
#print axioms local_collision_210

end Erdos708Formal

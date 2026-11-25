/- Exact, kernel-checked finite witness for Erdős #708.
   Lean 4.8.0, mathlib v4.8.0. Run: lake env lean Erdos708.lean -/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

namespace Erdos708Split
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def leftEnd : ℕ := 2825942749777232904620705
def center : ℕ := leftEnd + 1311
def moduli : Finset ℕ :=
  {1369,1517,1591,1681,1763,1849,1961,2173,2183,2257,2279,2419,2501,2537,2623}

private def ps : List ℕ := [37,41,43,53,59,61]
private def cap (p x : ℕ) : ℕ :=
  if x % p ≠ 0 then 0 else if x % (p^2) ≠ 0 then 1 else 2

private def capacity (x : ℕ) : ℕ :=
  1 + (if x = center then 5 else 0) + (if x = center+37 then 1 else 0) +
      (if x = center+41 then 1 else 0) + (if x = center+43 then 1 else 0)

private def testSite (i : ℕ) : Bool :=
  let x := leftEnd + i
  ps.all (fun p => x % (p^3) != 0) &&
    decide ((ps.map (fun p => cap p x)).sum ≤ capacity x)

private def allBelow (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => f n && allBelow f n

private theorem fromScan (f : ℕ → Bool) (n : ℕ) (h : allBelow f n = true)
    {i : ℕ} (hi : i < n) : f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have ha : f n = true ∧ allBelow f n = true := by
      simpa only [allBelow, Bool.and_eq_true] using h
    by_cases e : i = n
    · simpa [e] using ha.1
    · exact ih ha.2 (by omega)

private theorem scan : allBelow testSite 2623 = true := by decide

private theorem factor_bound (x p : ℕ) (hx : x ≠ 0) (hp : Nat.Prime p)
    (h3 : x % (p^3) ≠ 0) : x.factorization p ≤ cap p x := by
  have h (k : ℕ) (hk : x % (p^k) ≠ 0) : x.factorization p < k := by
    apply Nat.lt_of_not_ge
    intro hle
    exact hk ((Nat.dvd_iff_mod_eq_zero _ _).mp ((hp.pow_dvd_iff_le_factorization hx).2 hle))
  unfold cap
  split_ifs with h1 h2
  · have := h 1 (by simpa using h1)
    omega
  · have := h 2 h2
    omega
  · have := h 3 h3
    omega

private def weight (x : ℕ) : ℕ :=
  x.factorization 37 + x.factorization 41 + x.factorization 43 +
  x.factorization 53 + x.factorization 59 + x.factorization 61

private theorem siteBound {x : ℕ} (hx : x ∈ Ico leftEnd (leftEnd+2623)) :
    weight x ≤ capacity x := by
  obtain ⟨lo, hi⟩ := mem_Ico.mp hx
  have v := fromScan testSite 2623 scan (i := x-leftEnd) (by omega)
  simp only [testSite, Nat.add_sub_of_le lo, Bool.and_eq_true, decide_eq_true_eq] at v
  obtain ⟨h3, hv⟩ := v
  have xpos : x ≠ 0 := by unfold leftEnd at lo; omega
  have f (p : ℕ) (hp : p ∈ ps) (hprime : Nat.Prime p) :
      x.factorization p ≤ cap p x :=
    factor_bound x p xpos hprime (by simpa using (List.all_eq_true.mp h3 p hp))
  have a := f 37 (by decide) (by decide)
  have b := f 41 (by decide) (by decide)
  have c := f 43 (by decide) (by decide)
  have d := f 53 (by decide) (by decide)
  have e := f 59 (by decide) (by decide)
  have g := f 61 (by decide) (by decide)
  simp [ps, List.sum_cons] at hv
  unfold weight
  omega

private theorem demand {B : Finset ℕ} (hn : ∀ x ∈ B, x ≠ 0)
    (hdiv : (∏ a ∈ moduli, a) ∣ ∏ x ∈ B, x)
    (p d : ℕ) (hp : Nat.Prime p) (hd : p^d ∣ ∏ a ∈ moduli, a) :
    d ≤ ∑ x ∈ B, x.factorization p := by
  have hh := (hp.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.mpr hn)).mp
    (dvd_trans hd hdiv)
  rw [Nat.factorization_prod hn, Finsupp.finset_sum_apply] at hh
  exact hh

theorem certificate {B : Finset ℕ} (hB : B ⊆ Ico leftEnd (leftEnd + 2623))
    (hc : (∏ a ∈ moduli, a) ∣ ∏ x ∈ B, x) : 22 ≤ B.card := by
  have hn (x : ℕ) (hx : x ∈ B) : x ≠ 0 := by
    have hh := (mem_Ico.mp (hB hx)).1
    unfold leftEnd at hh
    omega
  have a := demand hn hc 37 7 (by decide) (by decide)
  have b := demand hn hc 41 7 (by decide) (by decide)
  have c := demand hn hc 43 7 (by decide) (by decide)
  have d := demand hn hc 53 3 (by decide) (by decide)
  have e := demand hn hc 59 3 (by decide) (by decide)
  have f := demand hn hc 61 3 (by decide) (by decide)
  have h := Finset.sum_le_sum (s := B) (fun x hx => siteBound (hB hx))
  simp only [weight, capacity, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_const, smul_eq_mul, mul_one] at h
  split_ifs at h <;> omega

/-- Any at-most uniform bound for 15 moduli in positive intervals is at least 22. -/
theorem lowerBound15 (k : ℕ)
    (uniform : ∀ A : Finset ℕ, A.card = 15 → (∀ a ∈ A, 2 ≤ a) →
      ∀ L : ℕ, 0 < L → ∃ B ⊆ Ico L (L + A.sup id),
        B.card ≤ k ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b) : 22 ≤ k := by
  have hmin : ∀ a ∈ moduli, 2 ≤ a := by decide
  obtain ⟨B,hB,hk,hd⟩ := uniform moduli (by decide) hmin leftEnd (by decide)
  have hmax : moduli.sup id = 2623 := by decide
  rw [hmax] at hB
  exact le_trans (certificate hB hd) hk


private def offsets : Finset ℕ := {13,16,21,30,39,40,53,64,72,81,90,91,92,107,122,127,150,163,1311,1348,1352,1354}
private def chosen : Finset ℕ := offsets.image (leftEnd + ·)

/-- A matching 22-element cover for this particular interval. -/
theorem attained : ∃ B ⊆ Ico leftEnd (leftEnd+2623), B.card = 22 ∧
    (∏ a ∈ moduli, a) ∣ ∏ b ∈ B, b := by
  refine ⟨chosen, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have rangeCheck : ∀ j ∈ offsets, j < 2623 := by decide
    have := rangeCheck i hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · decide
  · decide

#print axioms attained

#print axioms lowerBound15
end Erdos708Split

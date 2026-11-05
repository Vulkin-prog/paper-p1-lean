module

public import PaperP1.Algebra.MvPlaneBezout

/-! # Finite auxiliary zero sets with identically vanishing restrictions omitted

The exact exceptional locus includes only equations not divisible by the curve.
A supplied finite polynomial family gives a genuine finite set and degree sum.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialAuxiliaryExceptions

open MvPolynomial Set Finset

variable {F ι : Type*} [Field F]

def points (P : MvPolynomial (Fin 2) F) (f : ι → MvPolynomial (Fin 2) F) : Set (Fin 2 → F) :=
  {z | eval z P = 0 ∧ ∃ i, ¬P ∣ f i ∧ eval z (f i) = 0}

theorem population_card [Infinite F] [Fintype ι] (P : MvPolynomial (Fin 2) F)
    (hP : Irreducible P) (f : ι → MvPolynomial (Fin 2) F) (S : Finset (Fin 2 → F))
    (hS : ∀ z ∈ S, z ∈ points P f) :
    S.card ≤ P.totalDegree * ∑ i, (f i).totalDegree := by
  classical
  let T (i : ι) := S.filter (fun z ↦ ¬P ∣ f i ∧ eval z (f i) = 0)
  have hsub : S ⊆ Finset.univ.biUnion T := by
    intro z hz
    obtain ⟨i, hi, hzero⟩ := (hS z hz).2
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hz, hi, hzero⟩⟩
  have hcard (i : ι) : (T i).card ≤ P.totalDegree * (f i).totalDegree := by
    by_cases hdiv : P ∣ f i
    · have hempty : T i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact (mem_filter.mp hz).2.1 hdiv
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · apply MvPlaneBezout.common_points_card P (f i) hP hdiv (T i)
      intro z hz
      exact ⟨(hS z (mem_filter.mp hz).1).1, (mem_filter.mp hz).2.2⟩
  calc
    _ ≤ (Finset.univ.biUnion T).card := card_le_card hsub
    _ ≤ ∑ i, (T i).card := card_biUnion_le
    _ ≤ ∑ i, P.totalDegree * (f i).totalDegree := sum_le_sum (fun i _hi ↦ hcard i)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exists_finset [Infinite F] [Fintype ι] (P : MvPolynomial (Fin 2) F)
    (hP : Irreducible P) (f : ι → MvPolynomial (Fin 2) F) :
    ∃ E : Finset (Fin 2 → F), (∀ z, z ∈ E ↔ z ∈ points P f) ∧
      E.card ≤ P.totalDegree * ∑ i, (f i).totalDegree := by
  classical
  have hf : (points P f).Finite := by
    by_contra hbad
    have hInf : (points P f).Infinite := hbad
    obtain ⟨S, hS, hcard⟩ := hInf.exists_subset_card_eq (P.totalDegree * ∑ i, (f i).totalDegree + 1)
    have hc := population_card P hP f S (fun z hz ↦ hS hz)
    omega
  refine ⟨hf.toFinset, (fun z ↦ hf.mem_toFinset), ?_⟩
  exact population_card P hP f hf.toFinset (fun z hz ↦ hf.mem_toFinset.mp hz)

theorem divisible_or_nonzero (P : MvPolynomial (Fin 2) F) (f : ι → MvPolynomial (Fin 2) F)
    (z : Fin 2 → F) (hzero : eval z P = 0) (hnot : z ∉ points P f) (i : ι) :
    P ∣ f i ∨ eval z (f i) ≠ 0 := by
  by_cases hdiv : P ∣ f i
  · exact Or.inl hdiv
  · exact Or.inr (fun hz ↦ hnot ⟨hzero, i, hdiv, hz⟩)

theorem zero_of_divisible (P Q : MvPolynomial (Fin 2) F) (z : Fin 2 → F)
    (hzero : eval z P = 0) (hdiv : P ∣ Q) : eval z Q = 0 := by
  obtain ⟨R, rfl⟩ := hdiv
  rw [map_mul, hzero, zero_mul]

theorem restriction_zero_or_nowhere_zero (P : MvPolynomial (Fin 2) F)
    (f : ι → MvPolynomial (Fin 2) F) (S : Set (Fin 2 → F))
    (hS : ∀ z ∈ S, eval z P = 0 ∧ z ∉ points P f) (i : ι) :
    (∀ z ∈ S, eval z (f i) = 0) ∨ (∀ z ∈ S, eval z (f i) ≠ 0) := by
  by_cases hdiv : P ∣ f i
  · exact Or.inl (fun z hz ↦ zero_of_divisible P (f i) z (hS z hz).1 hdiv)
  · apply Or.inr
    intro z hz
    exact (divisible_or_nonzero P f z (hS z hz).1 (hS z hz).2 i).resolve_left hdiv

end PaperP1.PolynomialAuxiliaryExceptions

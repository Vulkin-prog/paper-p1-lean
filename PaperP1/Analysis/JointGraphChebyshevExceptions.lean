module

public import PaperP1.Algebra.GraphControlExceptions
public import PaperP1.Analysis.CurveChebyshevExceptions

/-! # A common genuine finite set for bounded graph jets and Chebyshev counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointGraphChebyshevExceptions

open MvPolynomial Set Finset

def points (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) : Set (Fin 2 → ℝ) :=
  GraphControlExceptions.points P (r + 1) ∪ CurveChebyshevExceptions.points P k

theorem avoids_both (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (z : Fin 2 → ℝ)
    (hnot : z ∉ points P r k) :
    z ∉ GraphControlExceptions.points P (r + 1) ∧ z ∉ MonomialWronskianExceptions.exceptionalPoints P k := by
  exact ⟨(fun hz ↦ hnot (Or.inl hz)), (fun hz ↦ hnot (Or.inr (Or.inr hz)))⟩

theorem exists_finset (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P) (r k : ℕ)
    (hk : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ), (∀ z, z ∈ E ↔ z ∈ points P r k) ∧
      E.card ≤ P.totalDegree ^ 2 * (30 * (r + 2) ^ 2 + 3 * (k + 1) ^ 6) := by
  classical
  obtain ⟨U, hU, hUcard⟩ := GraphControlExceptions.exists_finset P hP (by omega) (r + 1)
  obtain ⟨V, hV, hVcard⟩ := CurveChebyshevExceptions.exists_finset P hP k hk
  refine ⟨U ∪ V, ?_, ?_⟩
  · intro z
    simp only [Finset.mem_union, hU z, hV z, points, Set.mem_union]
  · have hc := Finset.card_union_le U V
    have hU' : U.card ≤ 30 * P.totalDegree ^ 2 * (r + 2) ^ 2 := by
      simpa only [show r + 1 + 1 = r + 2 by omega] using hUcard
    calc
      _ ≤ U.card + V.card := hc
      _ ≤ 30 * P.totalDegree ^ 2 * (r + 2) ^ 2 + 3 * P.totalDegree ^ 2 * (k + 1) ^ 6 :=
        Nat.add_le_add hU' hVcard
      _ = _ := by ring

end PaperP1.JointGraphChebyshevExceptions

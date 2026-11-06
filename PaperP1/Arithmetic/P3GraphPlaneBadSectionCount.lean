module

public import PaperP1.Arithmetic.PlaneNoetherSpecializationCount
public import PaperP1.Algebra.P3GraphPlaneSectionCoefficients

/-! # Actual reducible graph-plane sections have a uniform finite-field parameter bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneBadSectionCount

open MvPolynomial Finset P3GraphPlaneSection P3GraphPlaneSectionCoefficients
open scoped Classical

def badSections {F : Type} [Field F] [Fintype F] (P : MvPolynomial (Fin 4) F) : Finset (Fin 3 → F) :=
  univ.filter (fun a ↦ ¬ Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)))

def goodSections {F : Type} [Field F] [Fintype F] (P : MvPolynomial (Fin 4) F) : Finset (Fin 3 → F) :=
  univ.filter (fun a ↦ Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)))

theorem partition_card {F : Type} [Field F] [Fintype F] (P : MvPolynomial (Fin 4) F) :
    (goodSections P).card + (badSections P).card = Fintype.card F ^ 3 := by
  simpa only [goodSections, badSections, card_univ, Fintype.card_fun, Fintype.card_fin] using
    card_filter_add_card_filter_not (s := (univ : Finset (Fin 3 → F)))
      (fun a ↦ Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)))

theorem uniform_bad_section_bound (d : ℕ) :
    ∃ N : ℕ, ∀ (F K : Type) [Field F] [Fintype F] [Field K]
      (P : MvPolynomial (Fin 4) F), P.IsHomogeneous d → ∀ (φ : F →+* K) (a : Fin 3 → K),
      Irreducible (map (algebraMap K (AlgebraicClosure K)) (planeSection a (map φ P))) →
      (badSections P).card ≤ d * N * Fintype.card F ^ 2 := by
  obtain ⟨N, hN⟩ := PlaneNoetherSpecializationCount.uniform_bad_parameter_bound d
  refine ⟨N, ?_⟩
  intro F K _ _ _ P hP φ a hgood
  apply hN F K 3 d (by decide) (coefficients d P) (degree_bound d P hP) (eval₂Hom φ a)
  · rw [specialized_polynomial φ a d P hP]
    exact hgood
  · intro x hx
    rw [evaluation_polynomial x d P hP]
    exact (mem_filter.mp hx).2

theorem good_card_lower {F : Type} [Field F] [Fintype F] (P : MvPolynomial (Fin 4) F)
    (d N : ℕ) (hbad : (badSections P).card ≤ d * N * Fintype.card F ^ 2) :
    Fintype.card F ^ 3 - d * N * Fintype.card F ^ 2 ≤ (goodSections P).card := by
  have hp := partition_card P
  omega

theorem exists_good_section {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) (d N : ℕ)
    (hbad : (badSections P).card ≤ d * N * Fintype.card F ^ 2) (hlarge : d * N < Fintype.card F) :
    ∃ a : Fin 3 → F,
      Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)) := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hpow : d * N * Fintype.card F ^ 2 < Fintype.card F ^ 3 := by
    calc
      _ < Fintype.card F * Fintype.card F ^ 2 := Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos hq)
      _ = _ := by simp only [pow_succ, pow_zero, one_mul, Nat.mul_assoc]
  have hp : 0 < (goodSections P).card := lt_of_lt_of_le (Nat.sub_pos_of_lt hpow) (good_card_lower P d N hbad)
  obtain ⟨a, ha⟩ := card_pos.mp hp
  exact ⟨a, (mem_filter.mp ha).2⟩

end PaperP1.P3GraphPlaneBadSectionCount

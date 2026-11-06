module

public import PaperP1.Arithmetic.PlaneUniversalNoetherForms
public import PaperP1.Algebra.IntegerFormPolynomialSubstitution
public import PaperP1.Algebra.IntegerPolynomialEvaluationMass
public import PaperP1.Diophantine.FiniteFieldPolynomialZeroBound

/-! # A single actual good specialization bounds all geometrically reducible parameter values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneNoetherSpecializationCount

open MvPolynomial PlaneHomogeneousCoefficientFamily
open IntegerFormPolynomialSubstitution IntegerPolynomialEvaluationMass
open scoped Classical

theorem exists_nonzero_form (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : PlaneUniversalNoetherForms.Valid d forms)
    {F K τ : Type} [Field F] [Field K] (c : Index d → MvPolynomial τ F)
    (ε : MvPolynomial τ F →+* K)
    (hgood : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (polynomial d (fun i ↦ ε (c i))))) :
    ∃ Φ ∈ forms, substitute c Φ ≠ 0 := by
  obtain ⟨Φ, hΦ, hne⟩ := (hforms K (fun i ↦ ε (c i))).mp hgood
  refine ⟨Φ, hΦ, ?_⟩
  intro hz
  apply hne
  rw [← natural ε c Φ, hz, map_zero]

theorem bad_parameter_bound (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : PlaneUniversalNoetherForms.Valid d forms)
    {F K : Type} [Field F] [Fintype F] [Field K] {n : ℕ} (hn : 0 < n)
    (c : Index d → MvPolynomial (Fin n) F) (M : ℕ) (hc : ∀ i, (c i).totalDegree ≤ M)
    (ε : MvPolynomial (Fin n) F →+* K)
    (hgood : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (polynomial d (fun i ↦ ε (c i)))))
    (S : Finset (Fin n → F))
    (hS : ∀ x ∈ S, ¬ Irreducible (map (algebraMap F (AlgebraicClosure F))
      (polynomial d (fun i ↦ eval x (c i))))) :
    S.card ≤ M * familyDegree forms * Fintype.card F ^ (n - 1) := by
  obtain ⟨Φ, hΦ, hnonzero⟩ := exists_nonzero_form d forms hforms c ε hgood
  have hroot : ∀ x ∈ S, eval x (substitute c Φ) = 0 := by
    intro x hx
    rw [evaluation]
    by_contra hne
    exact hS x hx ((hforms F (fun i ↦ eval x (c i))).mpr ⟨Φ, hΦ, hne⟩)
  have hh := FiniteFieldPolynomialZeroBound.cardinality hn (substitute c Φ) hnonzero S hroot
  have hdeg : (substitute c Φ).totalDegree ≤ M * familyDegree forms :=
    (degree_bound c M hc Φ).trans (Nat.mul_le_mul_left M (Finset.le_sup hΦ))
  exact hh.trans (Nat.mul_le_mul_right _ hdeg)

theorem uniform_bad_parameter_bound (d : ℕ) :
    ∃ N : ℕ, ∀ (F K : Type) [Field F] [Fintype F] [Field K]
      (n M : ℕ), 0 < n → ∀ c : Index d → MvPolynomial (Fin n) F,
      (∀ i, (c i).totalDegree ≤ M) → ∀ ε : MvPolynomial (Fin n) F →+* K,
      Irreducible (map (algebraMap K (AlgebraicClosure K)) (polynomial d (fun i ↦ ε (c i)))) →
      ∀ S : Finset (Fin n → F),
        (∀ x ∈ S, ¬ Irreducible (map (algebraMap F (AlgebraicClosure F))
          (polynomial d (fun i ↦ eval x (c i))))) →
        S.card ≤ M * N * Fintype.card F ^ (n - 1) := by
  obtain ⟨forms, hforms⟩ := PlaneUniversalNoetherForms.exists_forms d
  refine ⟨familyDegree forms, ?_⟩
  intro F K _ _ _ n M hn c hc ε hgood S hS
  exact bad_parameter_bound d forms hforms hn c M hc ε hgood S hS

end PaperP1.PlaneNoetherSpecializationCount

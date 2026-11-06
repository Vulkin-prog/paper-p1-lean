module

public import PaperP1.Algebra.LinearHilbertParameterDependence
public import PaperP1.Algebra.HomogeneousFiniteParameterDescent
public import PaperP1.Algebra.TwoVariableGradedHilbert

/-! # Actual finite linear coordinate images inside a curve admit two finite linear parameters and their own Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLinearCurveImageNormalization

variable {F B R : Type*} [Field F] [Infinite F] [CommRing B] [CommRing R] [Algebra F B] [Algebra F R]

theorem exists_two_parameters
    (G : ℕ → Submodule F B) (H : ℕ → Submodule F R) [GradedAlgebra G] [GradedAlgebra H]
    [∀ n, Module.Finite F (H n)] (f : G →+*ᵍ H)
    (hscalar : ∀ r : F, f (algebraMap F B r) = algebraMap F R r) (hinj : Function.Injective f)
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (n : ℕ) (g : Fin n → B) (hg : ∀ i, g i ∈ G 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite) :
    ∃ u : Fin 2 → B, (∀ i, u i ∈ G 1) ∧ (MvPolynomial.aeval (R := F) u).Finite := by
  classical
  have hbad (m : ℕ) (hm : 3 ≤ m) (v : Fin m → B) (hvmem : ∀ i, v i ∈ G 1) :
      ¬ Function.Injective (MvPolynomial.aeval (R := F) v) := by
    intro hvinj
    let vR : Fin m → R := fun i ↦ f (v i)
    have heval : MvPolynomial.aeval (R := F) vR =
        (GradedModulePieceMap.algHom f hscalar).comp (MvPolynomial.aeval (R := F) v) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      rfl
    apply LinearHilbertParameterDependence.not_injective_of_three_le H a b hp m hm vR
      (fun i ↦ f.map_mem (hvmem i))
    rw [heval]
    exact hinj.comp hvinj
  revert g
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro g hg hfinite
    by_cases hn : n ≤ 2
    · let e : Fin n → Fin 2 := fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
      let u : Fin 2 → B := fun j ↦ if h : j.val < n then g ⟨j.val, h⟩ else 0
      have hu (j : Fin 2) : u j ∈ G 1 := by
        dsimp [u]
        split_ifs with hj
        · exact hg _
        · exact (G 1).zero_mem
      have heval : (MvPolynomial.aeval (R := F) u).comp (MvPolynomial.rename e) =
          MvPolynomial.aeval (R := F) g := by
        apply MvPolynomial.algHom_ext
        intro i
        simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
        simp only [u, e, dite_eq_left i.isLt]
      refine ⟨u, hu, AlgHom.Finite.of_comp_finite (f := MvPolynomial.rename e) ?_⟩
      rw [heval]
      exact hfinite
    · cases n with
      | zero => omega
      | succ m =>
        obtain ⟨v, hv, hvfinite⟩ := HomogeneousFiniteParameterDescent.exists_fewer_parameters
          G g hg hfinite (hbad (m + 1) (by omega) g hg)
        exact ih m (Nat.lt_succ_self m) v hv hvfinite

theorem exists_hilbert_polynomial [IsDomain B]
    (G : ℕ → Submodule F B) (H : ℕ → Submodule F R) [GradedAlgebra G] [GradedAlgebra H]
    [∀ n, Module.Finite F (H n)] (f : G →+*ᵍ H)
    (hscalar : ∀ r : F, f (algebraMap F B r) = algebraMap F R r) (hinj : Function.Injective f)
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (n : ℕ) (g : Fin n → B) (hg : ∀ i, g i ∈ G 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial G p := by
  let (r : ℕ) : Module.Finite F (G r) := Module.Finite.of_injective
    (GradedInjectiveHilbertComparison.pieceMap f hscalar r)
    (GradedInjectiveHilbertComparison.pieceMap_injective f hscalar hinj r)
  obtain ⟨u, hu, hufinite⟩ := exists_two_parameters G H f hscalar hinj a b hp n g hg hfinite
  exact TwoVariableGradedHilbert.exists_polynomial_of_finite G u hu hufinite

end PaperP1.FiniteLinearCurveImageNormalization

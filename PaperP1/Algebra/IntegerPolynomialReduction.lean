module

public import PaperP1.Algebra.PolynomialEvaluationCongruence
public import PaperP1.Algebra.LastChartPolynomial

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPolynomialReduction

open MvPolynomial

theorem map_evaluation {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (v : σ → R) (P : MvPolynomial σ R) :
    φ (eval v P) = eval (fun k ↦ φ (v k)) (map φ P) := by
  calc
    _ = eval₂Hom (φ.comp (RingHom.id R)) (fun k ↦ φ (v k)) P :=
      map_eval₂Hom (RingHom.id R) v φ P
    _ = _ := eval₂_eq_eval_map φ (fun k ↦ φ (v k)) P

theorem map_dehomogenize {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (P : MvPolynomial (Fin (n + 1)) R) :
    map φ (LastChartPolynomial.dehomogenize P) =
      eval₂Hom (C.comp φ) (Fin.snoc X 1) P := by
  have he : (MvPolynomial.map φ).comp (LastChartPolynomial.dehomogenize (R := R) (n := n)) =
      eval₂Hom (C.comp φ) (Fin.snoc X 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [LastChartPolynomial.dehomogenize]
    · intro i
      cases i using Fin.lastCases <;> simp [LastChartPolynomial.dehomogenize]
  exact RingHom.congr_fun he P

end PaperP1.IntegerPolynomialReduction

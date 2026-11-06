module

public import PaperP1.Algebra.PolynomialSubstitutionDegree

/-! # Actual integer-form substitution commutes with every field-valued polynomial evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerFormPolynomialSubstitution

open MvPolynomial

variable {F K σ τ : Type*} [CommRing F] [CommRing K]

def substitute (c : σ → MvPolynomial τ F) : MvPolynomial σ ℤ →+* MvPolynomial τ F :=
  eval₂Hom (C.comp (Int.castRingHom F)) c

theorem natural (ε : MvPolynomial τ F →+* K) (c : σ → MvPolynomial τ F)
    (P : MvPolynomial σ ℤ) :
    ε (substitute c P) = eval (fun i ↦ ε (c i)) (map (Int.castRingHom K) P) := by
  have he : ε.comp (substitute c) = eval₂Hom (Int.castRingHom K) (fun i ↦ ε (c i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitute]
    · intro i
      simp [substitute]
  rw [eval_map]
  exact RingHom.congr_fun he P

theorem evaluation (x : τ → F) (c : σ → MvPolynomial τ F) (P : MvPolynomial σ ℤ) :
    eval x (substitute c P) = eval (fun i ↦ eval x (c i)) (map (Int.castRingHom F) P) :=
  natural (eval x) c P

omit [CommRing K] in
theorem degree_bound (c : σ → MvPolynomial τ F) (M : ℕ)
    (hc : ∀ i, (c i).totalDegree ≤ M) (P : MvPolynomial σ ℤ) :
    (substitute c P).totalDegree ≤ M * P.totalDegree :=
  PolynomialSubstitutionDegree.eval2_bound (Int.castRingHom F) c M hc P

end PaperP1.IntegerFormPolynomialSubstitution

module

public import PaperP1.Algebra.BivariateLinearShear

/-! # Actual invertible uniform coordinate dilations preserve irreducibility and total degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformPolynomialDilation

open MvPolynomial

variable {R σ : Type*} [CommRing R]

def substitute (c : R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i ↦ C c * X i)

theorem substitute_one : substitute (σ := σ) (1 : R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitute]

theorem substitute_mul (c d : R) :
    (substitute (σ := σ) c).comp (substitute d) = substitute (c * d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitute, map_mul]
  ring

theorem evaluation (c : R) (P : MvPolynomial σ R) (z : σ → R) :
    eval z (substitute c P) = eval (fun i ↦ c * z i) P := by
  have he : (aeval z).comp (substitute c) = aeval (fun i ↦ c * z i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [substitute]
  exact DFunLike.congr_fun he P

theorem degree_le [Nontrivial R] (c : R) (P : MvPolynomial σ R) :
    (substitute c P).totalDegree ≤ P.totalDegree := by
  apply BivariateLinearShear.linear_substitution_degree
  intro i
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

def equiv {F : Type*} [Field F] (c : F) (hc : c ≠ 0) :
    MvPolynomial σ F ≃ₐ[F] MvPolynomial σ F :=
  AlgEquiv.ofAlgHom (substitute c) (substitute c⁻¹)
    (by rw [substitute_mul, mul_inv_cancel₀ hc, substitute_one])
    (by rw [substitute_mul, inv_mul_cancel₀ hc, substitute_one])

theorem degree {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (P : MvPolynomial σ F) :
    (substitute c P).totalDegree = P.totalDegree := by
  have he : substitute c⁻¹ (substitute c P) = P := (equiv c hc).symm_apply_apply P
  exact (degree_le c P).antisymm (by simpa only [he] using degree_le c⁻¹ (substitute c P))

theorem irreducible {F : Type*} [Field F] (c : F) (hc : c ≠ 0)
    (P : MvPolynomial σ F) (hP : Irreducible P) : Irreducible (substitute c P) :=
  (MulEquiv.irreducible_iff (equiv c hc).toRingEquiv.toMulEquiv).mpr hP

end PaperP1.UniformPolynomialDilation

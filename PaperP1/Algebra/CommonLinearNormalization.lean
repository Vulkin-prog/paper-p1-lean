module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Push

/-! # An actual common linear normalization of finitely many nonzero projective representatives -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonLinearNormalization

open MvPolynomial Finset

def form {F σ : Type*} [CommSemiring F] [Fintype σ] (a : σ → F) : MvPolynomial σ F :=
  ∑ i, C (a i) * X i

theorem form_homogeneous {F σ : Type*} [CommSemiring F] [Fintype σ] (a : σ → F) :
    (form a).IsHomogeneous 1 :=
  IsHomogeneous.sum Finset.univ _ 1 (fun i _ ↦ isHomogeneous_C_mul_X (a i) i)

theorem evaluation {F σ : Type*} [CommSemiring F] [Fintype σ] (a w : σ → F) :
    eval w (form a) = ∑ i, a i * w i := by
  simp only [form, map_sum, map_mul, eval_C, eval_X]

theorem symmetric_evaluation {F σ : Type*} [CommSemiring F] [Fintype σ] (a w : σ → F) :
    eval a (form w) = eval w (form a) := by
  rw [evaluation, evaluation]
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

theorem form_nonzero {F σ : Type*} [Field F] [Fintype σ] (w : σ → F) (hw : w ≠ 0) :
    form w ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hh
    exact hw (funext hh)
  have he : eval (Pi.single i (1 : F) : σ → F) (form w) = w i := by
    simp [evaluation, Pi.single_apply]
  intro hz
  exact hi (by simpa only [hz, map_zero] using he.symm)

theorem exists_form {F σ : Type*} [Field F] [Infinite F] [Finite σ]
    (S : Finset (σ → F)) (hne : ∀ w ∈ S, w ≠ 0) :
    ∃ ℓ : MvPolynomial σ F, ℓ.IsHomogeneous 1 ∧ ∀ w ∈ S, eval w ℓ ≠ 0 := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let P : MvPolynomial σ F := ∏ w ∈ S, form w
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w hw ↦ form_nonzero w (hne w hw))
  obtain ⟨a, ha⟩ : ∃ a : σ → F, eval a P ≠ 0 := by
    by_contra! hh
    apply hP
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero] using hh a
  refine ⟨form a, form_homogeneous a, ?_⟩
  intro w hw
  rw [← symmetric_evaluation a w]
  have hprod : ∏ v ∈ S, eval a (form v) ≠ 0 := by simpa only [P, map_prod] using ha
  exact Finset.prod_ne_zero_iff.mp hprod w hw

def normalize {F σ : Type*} [Field F] (ℓ : MvPolynomial σ F) (w : σ → F) : σ → F :=
  fun i ↦ (eval w ℓ)⁻¹ * w i

theorem normalized_value {F σ : Type*} [Field F] (ℓ : MvPolynomial σ F)
    (hℓ : ℓ.IsHomogeneous 1) (w : σ → F) (hw : eval w ℓ ≠ 0) :
    eval (normalize ℓ w) ℓ = 1 := by
  change eval (fun i ↦ (eval w ℓ)⁻¹ * w i) ℓ = 1
  rw [HomogeneousPolynomialEvaluation.eval_scale ℓ hℓ, pow_one]
  exact inv_mul_cancel₀ hw

theorem normalize_injOn {F σ : Type*} [Field F] (S : Finset (σ → F))
    (ℓ : MvPolynomial σ F) (hℓ : ∀ w ∈ S, eval w ℓ ≠ 0)
    (hsep : ∀ v ∈ S, ∀ w ∈ S, (∃ c : F, c ≠ 0 ∧ ∀ i, v i = c * w i) → v = w) :
    Set.InjOn (normalize ℓ) (S : Set (σ → F)) := by
  intro v hv w hw he
  apply hsep v hv w hw
  refine ⟨eval v ℓ * (eval w ℓ)⁻¹, mul_ne_zero (hℓ v hv) (inv_ne_zero (hℓ w hw)), ?_⟩
  intro i
  have hh := congrFun he i
  change (eval v ℓ)⁻¹ * v i = (eval w ℓ)⁻¹ * w i at hh
  have hm := congrArg (fun x : F ↦ eval v ℓ * x) hh
  simpa only [← mul_assoc, mul_inv_cancel₀ (hℓ v hv), one_mul] using hm

end PaperP1.CommonLinearNormalization

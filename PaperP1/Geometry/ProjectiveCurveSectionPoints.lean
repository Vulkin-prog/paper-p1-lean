module

public import PaperP1.Geometry.ProjectiveCurveHilbertDegree
public import PaperP1.Algebra.FiniteGradedPointEvaluation
public import PaperP1.Arithmetic.NormalizedIntegerPoints

/-! # Actual normalized rational and integer points on homogeneous curve sections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveCurveSectionPoints

open MvPolynomial ProjectiveCurveData ProjectiveCurveHilbertDegree

theorem normalized_population {σ : Type} [Finite σ] (Γ : Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal)
    (S : Finset (σ → ℚ)) (z : σ) (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ Γ.ideal, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * natDegree Γ := by
  classical
  let A := (MvPolynomial σ ℚ) ⧸ Γ.ideal
  let b : A := Ideal.Quotient.mk Γ.ideal f
  let J := HomogeneousPrincipalQuotient.ideal b
  let B := A ⧸ J
  let q : MvPolynomial σ ℚ →ₐ[ℚ] B :=
    (Ideal.Quotient.mkₐ ℚ J).comp (Ideal.Quotient.mkₐ ℚ Γ.ideal)
  let evI : S → A →ₐ[ℚ] ℚ := fun w ↦ Ideal.Quotient.liftₐ Γ.ideal (MvPolynomial.aeval w.val)
    (fun P hP ↦ hcurve w.val w.property P hP)
  have hevI (w : S) : evI w b = 0 := hsection w.val w.property
  have hJ (w : S) : ∀ x ∈ J, evI w x = 0 := by
    have hle : J ≤ RingHom.ker (evI w).toRingHom := by
      change Ideal.span {b} ≤ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact hevI w
    exact fun _ hx ↦ hle hx
  let ev : S → B →ₐ[ℚ] ℚ := fun w ↦ Ideal.Quotient.liftₐ J (evI w) (hJ w)
  have hcompat : ∀ P : MvPolynomial σ ℚ, ∀ w : S, ev w (q P) = eval w.val P := by
    intro P w
    rfl
  obtain ⟨N, hN⟩ := section_dimension Γ f hf hnot
  let n := max N S.card
  have hc := FiniteGradedPointEvaluation.card_le_dimension S z hnormal (n + e) (by dsimp [n]; omega) q ev hcompat
  have hpiece : (homogeneousSubmodule σ ℚ (n + e)).map q.toLinearMap =
      HomogeneousPrincipalQuotient.piece (piece Γ.ideal) b (n + e) := by
    change _ = ((homogeneousSubmodule σ ℚ (n + e)).map
      (Ideal.Quotient.mkₐ ℚ Γ.ideal).toLinearMap).map (Ideal.Quotient.mkₐ ℚ J).toLinearMap
    rw [← Submodule.map_comp]
    rfl
  rw [hpiece] at hc
  exact hc.trans_eq (hN n (le_max_left _ _))

theorem integer_population {σ : Type} [Finite σ] (Γ : Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal)
    (S : Finset (σ → ℤ)) (z : σ) (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ Γ.ideal, eval (fun i ↦ (w i : ℚ)) P = 0)
    (hsection : ∀ w ∈ S, eval (fun i ↦ (w i : ℚ)) f = 0) : S.card ≤ e * natDegree Γ := by
  classical
  let c : (σ → ℤ) → σ → ℚ := fun w i ↦ (w i : ℚ)
  have hinj : Function.Injective c := by
    intro v w he
    funext i
    exact Int.cast_injective (congrFun he i)
  let T := S.image c
  have hc := normalized_population Γ f hf hnot T z (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    change (v z : ℚ) = 1
    rw [hnormal v hv, Int.cast_one]) (by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hcurve v hv P hP) (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hsection v hv)
  change (S.image c).card ≤ e * natDegree Γ at hc
  rw [Finset.card_image_of_injective _ hinj] at hc
  exact hc

theorem integer_grid {σ : Type} [Finite σ] (Γ : Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal)
    (z : σ) (H : ℕ) :
    ((NormalizedIntegerPoints.points Γ.ideal z H).filter
      (fun w ↦ eval (fun i ↦ (w i : ℚ)) f = 0)).card ≤ e * natDegree Γ := by
  classical
  apply integer_population Γ f hf hnot _ z
  · intro w hw
    exact ((NormalizedIntegerPoints.mem_points Γ.ideal z H w).mp (Finset.mem_filter.mp hw).1).1.2
  · intro w hw P hP
    have hh := ((NormalizedIntegerPoints.mem_points Γ.ideal z H w).mp (Finset.mem_filter.mp hw).1).2 hP
    exact hh
  · exact fun _ hw ↦ (Finset.mem_filter.mp hw).2

end PaperP1.ProjectiveCurveSectionPoints

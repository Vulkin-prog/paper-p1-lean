module

public import PaperP1.Algebra.HomogeneousFiniteInterpolation

/-! # Actual homogeneous selectors normalized by an arbitrary homogeneous linear form -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearNormalizedHomogeneousInterpolation

open MvPolynomial
open scoped Classical

theorem selector {F σ : Type*} [Field F] (S : Finset (σ → F))
    (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (hnormal : ∀ w ∈ S, eval w ℓ = 1) (p : σ → F) (hp : p ∈ S)
    (n : ℕ) (hn : S.card - 1 ≤ n) :
    ∃ q : MvPolynomial σ F, q.IsHomogeneous n ∧
      ∀ w ∈ S, eval w q = if w = p then 1 else 0 := by
  classical
  let v : (σ → F) → Option σ → F := fun w ↦ Option.elim' 1 w
  have hinj : Function.Injective v := by
    intro w u he
    funext i
    exact congrFun he (some i)
  let T := S.image v
  have hcard : T.card = S.card := Finset.card_image_of_injective _ hinj
  obtain ⟨Q, hQ, hvalues⟩ := HomogeneousFiniteInterpolation.selector T none
    (by intro w hw; obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hw; rfl)
    (v p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩) n (by rw [hcard]; exact hn)
  let sub : Option σ → MvPolynomial σ F := Option.elim' ℓ X
  have hsub : ∀ i, (sub i).IsHomogeneous 1 := by
    intro i
    cases i with
    | none => exact hℓ
    | some i => exact isHomogeneous_X F i
  let q : MvPolynomial σ F := aeval sub Q
  refine ⟨q, by simpa only [one_mul] using hQ.aeval sub hsub, ?_⟩
  intro w hw
  have he : (aeval w).comp (aeval sub) = aeval (v w) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp only [AlgHom.comp_apply, aeval_X]
      change eval w ℓ = 1
      exact hnormal w hw
    | some i =>
      simp only [AlgHom.comp_apply, aeval_X]
      change (aeval w) (X i) = w i
      rw [aeval_X]
  have hqe : eval w q = eval (v w) Q := DFunLike.congr_fun he Q
  rw [hqe]
  simpa only [hinj.eq_iff] using hvalues (v w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

end PaperP1.LinearNormalizedHomogeneousInterpolation

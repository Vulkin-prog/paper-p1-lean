module

public import PaperP1.Algebra.ScalarExtendedGradedCoordinates
public import PaperP1.Algebra.ScalarExtendedFiniteFiber
public import PaperP1.Algebra.GradedPolynomialPresentation

/-! # Actual extended coordinate-power memberships force finiteness of the original parameter fibre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtendedParameterFiber

open MvPolynomial
open scoped TensorProduct

theorem finite_fiber {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] {n : ℕ} (x : Fin n → A)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (z : Fin n) (u : Fin n → ℕ) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ i : Fin n, (X i) ^ N ∈
      GradedPolynomialPresentation.kernel (F := E) (ScalarExtendedGradedCoordinates.coordinates (F := F) E x) ⊔
        Ideal.span {X z, CommonLinearNormalization.form (fun i ↦ (u i : E))}) :
    Module.Finite F (A ⧸ Ideal.span (Set.range
      (![x z, aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)))] : Fin 2 → A))) := by
  let g : Fin 2 → A := ![x z, aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)))]
  let K := Ideal.span (Set.range g)
  let B := A ⧸ K
  let q : A →ₐ[F] B := Ideal.Quotient.mkₐ F K
  let y := ScalarExtendedGradedCoordinates.coordinates (F := F) E x
  let ι : B →ₐ[F] E ⊗[F] B := Algebra.TensorProduct.includeRight
  let Φ : E ⊗[F] A →ₐ[E] E ⊗[F] B := (AlgHom.liftEquiv F E A (E ⊗[F] B)) (ι.comp q)
  let χ : MvPolynomial (Fin n) E →ₐ[E] E ⊗[F] B := Φ.comp (aeval (R := E) y)
  have hΦ (a : A) : Φ ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] q a := by
    change (1 : E) • ι (q a) = _
    rw [one_smul]
    rfl
  have hχX (i : Fin n) : χ (X i) = (1 : E) ⊗ₜ[F] q (x i) := by
    change Φ (aeval (R := E) y (X i)) = _
    rw [aeval_X]
    exact hΦ (x i)
  have hg0 : q (x z) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨(0 : Fin 2), rfl⟩
  have hg1 : q (aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)))) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨(1 : Fin 2), rfl⟩
  have hleft : GradedPolynomialPresentation.kernel (F := E) y ≤ RingHom.ker χ.toRingHom := by
    intro p hp
    change χ p = 0
    change aeval (R := E) y p = 0 at hp
    change Φ (aeval (R := E) y p) = 0
    rw [hp, map_zero]
  have hright : Ideal.span {X z, CommonLinearNormalization.form (fun i ↦ (u i : E))} ≤
      RingHom.ker χ.toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change χ (X z) = 0
      rw [hχX, hg0, TensorProduct.tmul_zero]
    · change Φ (aeval (R := E) y (CommonLinearNormalization.form (fun i ↦ (u i : E)))) = 0
      rw [ScalarExtendedGradedCoordinates.linear_form, hΦ, hg1, TensorProduct.tmul_zero]
  have hle : GradedPolynomialPresentation.kernel (F := E) y ⊔
      Ideal.span {X z, CommonLinearNormalization.form (fun i ↦ (u i : E))} ≤ RingHom.ker χ.toRingHom :=
    sup_le hleft hright
  have hzero (i : Fin n) : ((1 : E) ⊗ₜ[F] q (x i)) ^ N = 0 := by
    have hh := hle (hpow i)
    change χ ((X i) ^ N) = 0 at hh
    rwa [map_pow, hχX] at hh
  have hgenB : Algebra.adjoin F (Set.range (fun i ↦ q (x i))) = ⊤ := by
    have hh := congrArg (fun T : Subalgebra F A ↦ T.map q) hgen
    rw [AlgHom.map_adjoin, Algebra.map_top] at hh
    have he : q '' Set.range x = Set.range (fun i ↦ q (x i)) := (Set.range_comp' q x).symm
    rw [he] at hh
    exact hh.trans ((AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F K))
  exact ScalarExtendedFiniteFiber.finite_of_scalar_generator_powers (fun i ↦ q (x i)) hgenB N hN hzero

end PaperP1.ScalarExtendedParameterFiber

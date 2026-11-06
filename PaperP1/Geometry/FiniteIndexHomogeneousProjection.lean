module

public import PaperP1.Geometry.BoundedHomogeneousHypersurfaceProjection

/-! # The bounded actual hypersurface projection is independent of the finite coordinate index type -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteIndexHomogeneousProjection

open MvPolynomial LinearHypersurfaceImage

theorem exists_projection {F A σ : Type*} [Field F] [CharZero F] [CommRing A] [IsDomain A]
    [Algebra F A] [Fintype σ] {m : ℕ} (H : ℕ → Submodule F A) [GradedAlgebra H]
    (x : σ → A) (hx : ∀ i, x i ∈ H 1) (hgen : Algebra.adjoin F (Set.range x) = ⊤)
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g)) (d : ℕ) (hd : 0 < d)
    (hrank : letI : Algebra (MvPolynomial (Fin m) F) A := (aeval (R := F) g).toRingHom.toAlgebra;
      Module.finrank (MvPolynomial (Fin m) F) A = d) :
    ∃ (u : σ → ℕ) (q : MvPolynomial (Fin (m + 1)) F) (δ : A),
      (∀ i, u i ≤ ((Nat.card σ - 1) * d ^ 2 + 1) ^ (Nat.card σ - 1)) ∧
      let y := aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)));
      ideal (F := F) g y = Ideal.span {q} ∧ Irreducible q ∧ q.IsHomogeneous d ∧ q.totalDegree = d ∧
      (finSuccEquiv F m q).Monic ∧
      (letI : Algebra (CoordinateRing (F := F) g y) A := (toSource g y).toRingHom.toAlgebra;
        Module.finrank (CoordinateRing (F := F) g y) A = 1) ∧
      δ = aeval (R := F) (coordinates g y) (pderiv 0 q) ∧
      δ ∈ H (d - 1) ∧ δ ≠ 0 ∧ (∀ a : A, δ * a ∈ (toSource (F := F) g y).range) ∧
      ∀ (N : ℕ) (v : σ → ℤ), (∀ i, (v i).natAbs ≤ N) →
        |eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((Nat.card σ * (((Nat.card σ - 1) * d ^ 2 + 1) ^ (Nat.card σ - 1)) * N : ℕ) : ℤ) := by
  classical
  let n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let x' : Fin n → A := fun j ↦ x (e.symm j)
  have hx' : ∀ j, x' j ∈ H 1 := fun j ↦ hx (e.symm j)
  have hgen' : Algebra.adjoin F (Set.range x') = ⊤ := by
    have he : Set.range x' = Set.range x := by
      ext a
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [x', e.symm_apply_apply]⟩
    rwa [he]
  obtain ⟨u', q, δ, hu', hq, hirr, hhom, hdeg, hmonic, hrank', hpartial,
      hδmem, hδ0, hconductor, hheight⟩ :=
    BoundedHomogeneousHypersurfaceProjection.exists_projection H x' hx' hgen' g hg hfinite hinj d hd hrank
  let u : σ → ℕ := fun i ↦ u' (e i)
  have hy : aeval (R := F) x' (CommonLinearNormalization.form (fun j ↦ (u' j : F))) =
      aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F))) := by
    simp only [CommonLinearNormalization.form, map_sum, map_mul, aeval_C, aeval_X]
    apply Fintype.sum_equiv e.symm
    intro j
    simp only [u, x', e.apply_symm_apply]
  refine ⟨u, q, δ, ?_, ?_⟩
  · intro i
    simpa only [Nat.card_eq_fintype_card] using hu' (e i)
  · dsimp only
    rw [← hy]
    refine ⟨hq, hirr, hhom, hdeg, hmonic, hrank', hpartial, hδmem, hδ0, hconductor, ?_⟩
    intro N v hv
    have hh := hheight N (fun j ↦ v (e.symm j)) (fun j ↦ hv (e.symm j))
    have he : eval (fun j ↦ v (e.symm j)) (CommonLinearNormalization.form (fun j ↦ (u' j : ℤ))) =
        eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ))) := by
      rw [CommonLinearNormalization.evaluation, CommonLinearNormalization.evaluation]
      apply Fintype.sum_equiv e.symm
      intro j
      simp only [u, e.apply_symm_apply]
    rw [he] at hh
    simpa only [Nat.card_eq_fintype_card] using hh

end PaperP1.FiniteIndexHomogeneousProjection

module

public import PaperP1.Geometry.ProjFunctionFieldRank
public import PaperP1.Geometry.ProjChartFunctionFieldTransport
public import PaperP1.Algebra.FieldEquivScalarTransport

/-! # An actual finite graded projection and actual chart construct a finite radical cover of the actual chart fraction field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjChartRadicalCover

open AlgebraicGeometry HomogeneousLocalization

variable {F A B R : Type u} {ι κ : Type v} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H] [IsDomain A] [IsDomain B]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)
  {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))
  [CommRing R] [IsDomain R] (e : Away G b ≃+* R)

include hf hG hH hinj hb0 hv in
theorem exists_cover
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra; Submodule.span A (Set.range v) = ⊤)
    (a : κ → A) (root : κ → B) (hquad : ∀ ν, root ν ^ 2 = f (a ν)) :
    ∃ (L : Type u) (inst : Field L), letI := inst
      ∃ alg : Algebra (FractionRing R) L, letI := alg
        Module.Finite (FractionRing R) L ∧
        Module.finrank (FractionRing R) L = (letI : Algebra A B := f.toRingHom.toAlgebra; Module.finrank A B) ∧
        ∃ r : κ → L, ∀ ν, r ν ^ 2 = algebraMap (FractionRing R) L
          (algebraMap R (FractionRing R) (e (GradedDehomogenization.map G hb (a ν)))) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  let eP := ProjChartFunctionFieldTransport.equiv G hG hb hb0 e
  let : Algebra (FractionRing R) (Proj H).functionField := FieldEquivScalarTransport.algebra eP.symm
  have hdegree : Module.finrank (FractionRing R) (Proj H).functionField = Module.finrank A B :=
    (FieldEquivScalarTransport.finrank_eq eP.symm).trans
      (ProjFunctionFieldRank.finrank_eq_module f hf hG hH hinj hb hb0 v w hv hgen)
  have : Module.Finite A B := FreeApproximationRank.finite_of_span v hgen
  have hpos : 0 < Module.finrank A B := by
    have hle := LinearMap.finrank_le_finrank_of_injective (f := Algebra.linearMap A B) hinj
    exact lt_of_lt_of_le (by decide : 0 < 1) (by simpa only [Module.finrank_self] using hle)
  have hfinite : Module.Finite (FractionRing R) (Proj H).functionField :=
    Module.finite_of_finrank_pos (hdegree.symm ▸ hpos)
  have hfb0 : f b ≠ 0 := fun hz ↦ hb0 (hinj (hz.trans (map_zero f).symm))
  let r : κ → (Proj H).functionField := fun ν ↦ ProjChartFunctionField.chartMap H hH hfb0
    (GradedDehomogenization.map H (f.map_mem hb) (root ν))
  have hr (ν : κ) : r ν ^ 2 = algebraMap (FractionRing R) (Proj H).functionField
      (algebraMap R (FractionRing R) (e (GradedDehomogenization.map G hb (a ν)))) := by
    have heval := ProjChartFunctionFieldTransport.equiv_chartMap G hG hb hb0 e
      (GradedDehomogenization.map G hb (a ν))
    rw [FieldEquivScalarTransport.algebraMap_eq, ← heval, RingEquiv.symm_apply_apply]
    change r ν ^ 2 = ProjFunctionFieldMap.map f hf hG hH hinj
      (ProjChartFunctionField.chartMap G hG hb0 (GradedDehomogenization.map G hb (a ν)))
    have hnat := DFunLike.congr_fun
      (ProjChartFunctionFieldNaturality.chartMap_natural f hf hG hH hinj hb hb0 hfb0)
      (GradedDehomogenization.map G hb (a ν))
    simp only [RingHom.comp_apply] at hnat
    rw [hnat, GradedDehomogenizationModule.natural_apply f hb (a ν)]
    change (ProjChartFunctionField.chartMap H hH hfb0
      (GradedDehomogenization.map H (f.map_mem hb) (root ν))) ^ 2 = _
    rw [← map_pow, ← map_pow, hquad ν]
  exact ⟨(Proj H).functionField, inferInstance, FieldEquivScalarTransport.algebra eP.symm, hfinite, hdegree, r, hr⟩

end PaperP1.ProjChartRadicalCover

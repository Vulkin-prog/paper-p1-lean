module

public import PaperP1.Algebra.NativeAffineChart
public import PaperP1.Algebra.PlaneCurveVeroneseBaseQuotient

/-! # Contracting a homogeneous plane equation and then taking its Z-chart preserves its affine equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeVeroneseAffineIdeal

open Polynomial PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.NativeAffineChart PaperP1.TrivariatePolynomialEquiv

attribute [local instance] MvPolynomial.gradedAlgebra

local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance affineRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

def affineMap (F : Type*) [Field F] (D : ℕ) : Base F D →+* F[X][X] :=
  (specialization F).comp (Base F D).val.toRingHom

theorem affineMap_apply (F : Type*) [Field F] (D : ℕ) (p : Base F D) :
    affineMap F D p = specialization F (p : MvPolynomial (Fin 3) F) := rfl

def affineIdeal (F : Type*) [Field F] (D : ℕ) (Q : Ideal (Base F D)) : Ideal F[X][X] :=
  Q.map (affineMap F D)

theorem specialization_Z (F : Type*) [Field F] :
    specialization F (MvPolynomial.X (2 : Fin 3)) = 1 := by
  change HomogeneousSplitRadicalChart.chart F (threeEquiv F (MvPolynomial.X (2 : Fin 3))) = 1
  rw [threeEquiv_X_two]
  simp [HomogeneousSplitRadicalChart.chart]

theorem affineMap_radicand {F : Type*} [Field F] (c : F) (D : ℕ) (I J : Finset ℤ)
    (hdeg : I.card + J.card ≤ 2 * D) : affineMap F D (baseRadicand c D I J hdeg) =
      ScaledSplitWordSquares.scaledPolynomial c I J := by
  change HomogeneousSplitRadicalChart.chart F
    (threeEquiv F (HomogeneousSplitRadicalPolynomials.nativeRadicand c _ I J)) = _
  rw [HomogeneousSplitRadicalPolynomials.nativeRadicand_map,
    HomogeneousSplitRadicalChart.radicand_chart]

variable {F : Type*} [Field F] {e : ℕ} (f : MvPolynomial (Fin 3) F)
  (hf : f.IsHomogeneous e) (D : ℕ) (hD : 0 < D)

set_option backward.isDefEq.respectTransparency false in
include hf hD in
theorem contracted_principal : affineIdeal F D (PlaneCurveVeroneseBaseQuotient.ideal F f D) =
    Ideal.span {specialization F f} := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change (p : MvPolynomial (Fin 3) F) ∈ Ideal.span {f} at hp
    change specialization F (p : MvPolynomial (Fin 3) F) ∈ Ideal.span {specialization F f}
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
    apply Ideal.mem_span_singleton.mpr
    exact ⟨specialization F q, by rw [← map_mul, ← hq]⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hle : e ≤ e * D := Nat.le_mul_of_pos_right e hD
    let p : Base F D := ⟨f * MvPolynomial.X (2 : Fin 3) ^ (e * D - e), by
      apply GradedVeroneseAlgebra.piece_mem (MvPolynomial.homogeneousSubmodule (Fin 3) F) D e
      change (f * MvPolynomial.X (2 : Fin 3) ^ (e * D - e)).IsHomogeneous (e * D)
      convert hf.mul ((MvPolynomial.isHomogeneous_X F (2 : Fin 3)).pow (e * D - e)) using 1; omega⟩
    have hp : p ∈ PlaneCurveVeroneseBaseQuotient.ideal F f D := by
      change f * MvPolynomial.X (2 : Fin 3) ^ (e * D - e) ∈ Ideal.span {f}
      exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
    have he : affineMap F D p = specialization F f := by
      have hv : (p : MvPolynomial (Fin 3) F) = f * MvPolynomial.X (2 : Fin 3) ^ (e * D - e) := rfl
      rw [affineMap_apply, hv, map_mul, map_pow, specialization_Z, one_pow, mul_one]
    exact he ▸ Ideal.mem_map_of_mem (affineMap F D) hp

end PaperP1.NativeVeroneseAffineIdeal

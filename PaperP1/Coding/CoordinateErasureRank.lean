module

public import PaperP1.Coding.CoordinateForms
public import PaperP1.Algebra.EvenSupportRank

/-! # The dimension cost of any prescribed coordinate erasure

The zeroed coordinates need not be independent. Every injective even projection
of a surviving positive-dimensional space has at least two active positions.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateErasureRank

open Finset PaperP1.Arithmetic PaperP1.CoordinateForms

variable {U V : Type*} [AddCommGroup U] [Module F₂ U] [FiniteDimensional F₂ U]

def evaluation (L : V → Module.Dual F₂ U) (D : Finset V) : U →ₗ[F₂] (D → F₂) where
  toFun u v := L v u
  map_add' u w := by funext v; exact map_add (L v) u w
  map_smul' a u := by funext v; exact map_smul (L v) a u

omit [FiniteDimensional F₂ U] in
theorem evaluation_kernel (L : V → Module.Dual F₂ U) (D : Finset V) :
    LinearMap.ker (evaluation L D) = zeroCoordinates L D := by
  ext u
  rw [LinearMap.mem_ker, mem_zeroCoordinates]
  exact ⟨fun h v hv ↦ congrFun h ⟨v, hv⟩, fun h ↦ funext fun v ↦ h v v.property⟩

theorem dimension_cost (L : V → Module.Dual F₂ U) (D : Finset V) :
    Module.finrank F₂ U ≤ D.card + Module.finrank F₂ (zeroCoordinates L D) := by
  have he := (evaluation L D).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (evaluation L D))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hr
  rw [evaluation_kernel] at he
  omega

omit [FiniteDimensional F₂ U] in
theorem surviving_active {V : Type*} (L : V → Module.Dual F₂ U) (D : Finset V) (v : V)
    (hv : (L v).comp (zeroCoordinates L D).subtype ≠ 0) : L v ≠ 0 ∧ v ∉ D := by
  constructor
  · intro hz
    exact hv (by rw [hz, LinearMap.zero_comp])
  · intro hvD
    apply hv
    apply LinearMap.ext
    intro u
    exact u.property v hvD

variable {I : Type*} [Fintype I]

omit [FiniteDimensional F₂ U] in
theorem two_active (g : U →ₗ[F₂] (I → F₂)) (hinj : Function.Injective g)
    (heven : ∀ u, ∑ i, g u i = 0) (hdim : 0 < Module.finrank F₂ U) :
    ∃ i j : I, i ≠ j ∧ (LinearMap.proj i).comp g ≠ 0 ∧ (LinearMap.proj j).comp g ≠ 0 := by
  classical
  let T := univ.filter fun i ↦ (LinearMap.proj i).comp g ≠ 0
  have hzero (u : U) (i : I) (hi : i ∉ T) : g u i = 0 := by
    have hz : (LinearMap.proj i).comp g = 0 := by
      by_contra hh
      exact hi (mem_filter.mpr ⟨mem_univ i, hh⟩)
    exact congrArg (fun f : U →ₗ[F₂] F₂ ↦ f u) hz
  have hcard := EvenSupportRank.finrank_le_of_supported_even g hinj T hzero heven
  have htwo : 1 < T.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp htwo
  exact ⟨i, j, hij, (mem_filter.mp hi).2, (mem_filter.mp hj).2⟩

end PaperP1.CoordinateErasureRank

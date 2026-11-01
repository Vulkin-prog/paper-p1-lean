module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Rank gained by a finite family modulo an old subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuotientRank

variable {K U E : Type*} [DivisionRing K] [AddCommGroup U] [Module K U]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

def modulo (W : Submodule K U) (f : E →ₗ[K] U) : E →ₗ[K] (U ⧸ W) := W.mkQ.comp f

omit [FiniteDimensional K E] in
theorem ker_modulo (W : Submodule K U) (f : E →ₗ[K] U) :
    LinearMap.ker (modulo W f) = W.comap f := by
  ext e
  simp only [modulo, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]

theorem rank_add_kernel (W : Submodule K U) (f : E →ₗ[K] U) :
    Module.finrank K (LinearMap.range (modulo W f)) + Module.finrank K (W.comap f) =
      Module.finrank K E := by
  rw [← ker_modulo]
  exact (modulo W f).finrank_range_add_finrank_ker

omit [FiniteDimensional K E] in
theorem range_restricted_quotient (W : Submodule K U) (f : E →ₗ[K] U) :
    LinearMap.range (W.mkQ.comp (W ⊔ LinearMap.range f).subtype) =
      LinearMap.range (modulo W f) := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw, y, hy, hv⟩ := Submodule.mem_sup.mp v.property
    obtain ⟨e, rfl⟩ := hy
    refine ⟨e, ?_⟩
    change W.mkQ (f e) = W.mkQ v.val
    have hw0 : W.mkQ w = 0 := by simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hw
    rw [← hv, map_add, hw0, zero_add]
  · rintro ⟨e, rfl⟩
    exact ⟨⟨f e, (show LinearMap.range f ≤ W ⊔ LinearMap.range f from le_sup_right) (LinearMap.mem_range_self f e)⟩, rfl⟩

theorem rank_add_old (W : Submodule K U) [FiniteDimensional K W] (f : E →ₗ[K] U) :
    Module.finrank K (LinearMap.range (modulo W f)) + Module.finrank K W =
      Module.finrank K (W ⊔ LinearMap.range f : Submodule K U) := by
  let S := W ⊔ LinearMap.range f
  let g := W.mkQ.comp S.subtype
  have hker : LinearMap.ker g = W.comap S.subtype := by
    ext v
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
  have hdim := g.finrank_range_add_finrank_ker
  rw [hker, (Submodule.comapSubtypeEquivOfLe (show W ≤ S from le_sup_left)).finrank_eq] at hdim
  change Module.finrank K (LinearMap.range (W.mkQ.comp (W ⊔ LinearMap.range f).subtype)) + Module.finrank K W =
    Module.finrank K (W ⊔ LinearMap.range f : Submodule K U) at hdim
  rw [range_restricted_quotient] at hdim
  exact hdim

theorem joined_rank_add_kernel (W : Submodule K U) [FiniteDimensional K W] (f : E →ₗ[K] U) :
    Module.finrank K (W ⊔ LinearMap.range f : Submodule K U) + Module.finrank K (W.comap f) =
      Module.finrank K W + Module.finrank K E := by
  have h₁ := rank_add_old W f
  have h₂ := rank_add_kernel W f
  omega

end PaperP1.QuotientRank

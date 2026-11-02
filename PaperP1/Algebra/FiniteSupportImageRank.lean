module

public import PaperP1.Algebra.EvenSupportRank
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Actual support unions of basis images control the dimension of an injective projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSupportImageRank

open Finset

theorem finrank_le_card_of_supported {K E α : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] (g : E →ₗ[K] (α →₀ K)) (hg : Function.Injective g) (U : Finset α)
    (hzero : ∀ e u, u ∉ U → g e u = 0) : Module.finrank K E ≤ U.card := by
  let r : E →ₗ[K] (U → K) :=
    { toFun := fun e u ↦ g e u.val
      map_add' := by intros; funext; simp only [map_add, Finsupp.add_apply, Pi.add_apply]
      map_smul' := by intros; funext; simp only [map_smul, Finsupp.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  have hr : Function.Injective r := by
    intro e e' he
    apply hg
    ext u
    by_cases hu : u ∈ U
    · exact congrFun he ⟨u, hu⟩
    · rw [hzero e u hu, hzero e' u hu]
  have hdim := LinearMap.finrank_le_finrank_of_injective hr
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

def supportUnion {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K)) : Finset α :=
  univ.biUnion (fun i ↦ (g (b i)).support)

theorem mem_supportUnion {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K)) (u : α) :
    u ∈ supportUnion b g ↔ ∃ i, u ∈ (g (b i)).support := by
  simp only [supportUnion, mem_biUnion, mem_univ, true_and]

theorem outside_union_zero {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K))
    (e : E) (u : α) (hu : u ∉ supportUnion b g) : g e u = 0 := by
  let coord : E →ₗ[K] K := (Finsupp.lapply u).comp g
  have hc : coord = 0 := by
    apply b.ext
    intro i
    change g (b i) u = 0
    have hnot : u ∉ (g (b i)).support := by
      intro h
      exact hu ((mem_supportUnion b g u).mpr ⟨i, h⟩)
    exact Finsupp.notMem_support_iff.mp hnot
  exact congrArg (fun f : E →ₗ[K] K ↦ f e) hc

theorem support_subset_union {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K)) (e : E) :
    (g e).support ⊆ supportUnion b g := by
  intro u hu
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hu) (outside_union_zero b g e u hn)

theorem supportUnion_subset {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K)) (S : Finset α)
    (h : ∀ i, (g (b i)).support ⊆ S) : supportUnion b g ⊆ S := by
  intro u hu
  obtain ⟨i, hi⟩ := (mem_supportUnion b g u).mp hu
  exact h i hi

theorem support_subset_of_basis {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K)) (S : Finset α)
    (h : ∀ i, (g (b i)).support ⊆ S) (e : E) : (g e).support ⊆ S :=
  (support_subset_union b g e).trans (supportUnion_subset b g S h)

theorem rank_le_supportUnion {K E α ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [DecidableEq α] [Fintype ι] (b : Module.Basis ι K E) (g : E →ₗ[K] (α →₀ K))
    (hg : Function.Injective g) : Module.finrank K E ≤ (supportUnion b g).card :=
  finrank_le_card_of_supported g hg (supportUnion b g) (outside_union_zero b g)

end PaperP1.FiniteSupportImageRank

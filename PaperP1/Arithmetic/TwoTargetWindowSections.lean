module

public import PaperP1.Affine.EffectiveLinearSections
public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Model.LocalRunRank
public import Mathlib.Data.Fintype.Sum

/-! # Exact physical sections of two-target relations above any effective source subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWindowSections

open Finset PaperP1.Arithmetic PaperP1.Affine

local instance twoTargetPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Even (L : ℕ) := LinearMap.ker (startVertexSum L)

def sourceMap {s : ℕ} (x : Fin s → ℕ) (L : ℕ) :
    (Fin s → Even L) →ₗ[F₂] (ℕ →₀ F₂) where
  toFun v := ∑ i, evenSquareClassMap (x i) L (v i)
  map_add' v w := by simp only [Pi.add_apply, map_add, sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, map_smul, smul_sum, RingHom.id_apply]

theorem range_source_map {s : ℕ} (x : Fin s → ℕ) (L : ℕ) :
    LinearMap.range (sourceMap x L) = ⨆ i, squareClassSpace (x i) L := by
  apply le_antisymm
  · rintro u ⟨v, rfl⟩
    change (∑ i, evenSquareClassMap (x i) L (v i)) ∈ ⨆ i, squareClassSpace (x i) L
    exact Submodule.sum_mem _ fun i _ ↦ (le_iSup (fun i ↦ squareClassSpace (x i) L) i) ⟨v i, rfl⟩
  · apply iSup_le
    intro i u hu
    obtain ⟨v, rfl⟩ := hu
    let w : Fin s → Even L := fun j ↦ if j = i then v else 0
    refine ⟨w, ?_⟩
    change (∑ j : Fin s, evenSquareClassMap (x j) L (w j)) = evenSquareClassMap (x i) L v
    rw [sum_eq_single i]
    · simp only [w, ite_true]
    · intro j _ hji
      simp only [w, hji, ite_false, map_zero]
    · simp only [mem_univ, not_true_eq_false, false_implies]

abbrev Kernel (y z L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) :=
  TwoTargetKernel.Kernel W (squareClassSpace y L) (squareClassSpace z L)

abbrev Coordinate (s L : ℕ) := (Fin s ⊕ Fin 2) × Fin (L + 1)

def starts {s : ℕ} (x : Fin s → ℕ) (y z : ℕ) : Fin s ⊕ Fin 2 → ℕ
  | Sum.inl i => x i
  | Sum.inr t => if t = 0 then y else z

def physicalLift {s y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → Even L))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L) :
    Kernel y z L W →ₗ[F₂] (Coordinate s L → F₂) where
  toFun r v := match v.1 with
    | Sum.inl i => (σW r.val.1 i).val v.2
    | Sum.inr t => if t = 0 then (σY r.val.2.1).val v.2 else (σZ r.val.2.2).val v.2
  map_add' r q := by
    funext v
    rcases v with ⟨i | t, j⟩
    · simp
    · by_cases ht : t = 0 <;> simp [ht]
  map_smul' c r := by
    funext v
    rcases v with ⟨i | t, j⟩
    · simp
    · by_cases ht : t = 0 <;> simp [ht]

def targetProjection {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L)
    (t : Fin 2) : Kernel y z L W →ₗ[F₂] (Fin (L + 1) → F₂) :=
  if t = 0 then (Even L).subtype.comp (σY.comp (TwoTargetKernel.leftProjection W _ _))
  else (Even L).subtype.comp (σZ.comp (TwoTargetKernel.rightProjection W _ _))

theorem target_coordinate {s y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → Even L))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L)
    (t : Fin 2) (r : Kernel y z L W) (i : Fin (L + 1)) :
    targetProjection W σY σZ t r i = physicalLift W σW σY σZ r (Sum.inr t, i) := by
  by_cases ht : t = 0 <;> simp only [targetProjection, physicalLift, ht, ite_true, ite_false,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Submodule.subtype_apply,
    TwoTargetKernel.leftProjection, TwoTargetKernel.rightProjection, LinearMap.fst_apply, LinearMap.snd_apply]

theorem target_projection_injective {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L)
    (hY : Function.Injective σY) (hZ : Function.Injective σZ)
    (hWY : Disjoint W (squareClassSpace y L)) (hWZ : Disjoint W (squareClassSpace z L)) (t : Fin 2) :
    Function.Injective (targetProjection W σY σZ t) := by
  by_cases ht : t = 0
  · rw [targetProjection, ite_eq_left ht]
    exact Subtype.val_injective.comp (EffectiveLinearSections.left_lift_injective W _ _ σY hY hWZ)
  · rw [targetProjection, ite_eq_right ht]
    exact Subtype.val_injective.comp (EffectiveLinearSections.right_lift_injective W _ _ σZ hZ hWY)

theorem exists_sections {s : ℕ} (x : Fin s → ℕ) (y z L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ⨆ i, squareClassSpace (x i) L) :
    ∃ σW : W →ₗ[F₂] (Fin s → Even L),
    ∃ σY : squareClassSpace y L →ₗ[F₂] Even L,
    ∃ σZ : squareClassSpace z L →ₗ[F₂] Even L,
      (sourceMap x L).comp σW = W.subtype ∧
      (evenSquareClassMap y L).comp σY = (squareClassSpace y L).subtype ∧
      (evenSquareClassMap z L).comp σZ = (squareClassSpace z L).subtype ∧
      Function.Injective σW ∧ Function.Injective σY ∧ Function.Injective σZ := by
  have hsource : W ≤ LinearMap.range (sourceMap x L) := by rwa [range_source_map]
  obtain ⟨σW, hW, hWi⟩ := EffectiveLinearSections.exists_section (sourceMap x L) W hsource
  obtain ⟨σY, hY, hYi⟩ := EffectiveLinearSections.exists_section (evenSquareClassMap y L) _ le_rfl
  obtain ⟨σZ, hZ, hZi⟩ := EffectiveLinearSections.exists_section (evenSquareClassMap z L) _ le_rfl
  exact ⟨σW, σY, σZ, hW, hY, hZ, hWi, hYi, hZi⟩

theorem physical_even {s y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → Even L))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L)
    (r : Kernel y z L W) (j : Fin s ⊕ Fin 2) :
    startVertexSum L (fun i ↦ physicalLift W σW σY σZ r (j, i)) = 0 := by
  rcases j with j | t
  · exact (σW r.val.1 j).property
  · by_cases ht : t = 0
    · have h : startVertexSum L (σY r.val.2.1).val = 0 := (σY r.val.2.1).property
      simpa only [physicalLift, ht, ite_true, LinearMap.coe_mk, AddHom.coe_mk] using h
    · have h : startVertexSum L (σZ r.val.2.2).val = 0 := (σZ r.val.2.2).property
      simpa only [physicalLift, ht, ite_false, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem physical_relation {s y z L : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → Even L))
    (σY : squareClassSpace y L →ₗ[F₂] Even L) (σZ : squareClassSpace z L →ₗ[F₂] Even L)
    (hW : (sourceMap x L).comp σW = W.subtype)
    (hY : (evenSquareClassMap y L).comp σY = (squareClassSpace y L).subtype)
    (hZ : (evenSquareClassMap z L).comp σZ = (squareClassSpace z L).subtype)
    (r : Kernel y z L W) :
    (∑ j : Fin s ⊕ Fin 2, vertexParityMap (starts x y z j) L
      (fun i ↦ physicalLift W σW σY σZ r (j, i))) = 0 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  have hsum := r.property
  change (r.val.1 : ℕ →₀ F₂) + (r.val.2.1 : ℕ →₀ F₂) + (r.val.2.2 : ℕ →₀ F₂) = 0 at hsum
  have hs : (∑ j, evenSquareClassMap (x j) L (σW r.val.1 j)) = (r.val.1 : ℕ →₀ F₂) :=
    LinearMap.congr_fun hW r.val.1
  have hy : evenSquareClassMap y L (σY r.val.2.1) = (r.val.2.1 : ℕ →₀ F₂) :=
    LinearMap.congr_fun hY r.val.2.1
  have hz : evenSquareClassMap z L (σZ r.val.2.2) = (r.val.2.2 : ℕ →₀ F₂) :=
    LinearMap.congr_fun hZ r.val.2.2
  change (∑ j, evenSquareClassMap (x j) L (σW r.val.1 j)) +
    (evenSquareClassMap y L (σY r.val.2.1) + evenSquareClassMap z L (σZ r.val.2.2)) = 0
  rw [hs, hy, hz, ← add_assoc]
  exact hsum

theorem dimension_le_length (y z L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hWZ : Disjoint W (squareClassSpace z L)) :
    Module.finrank F₂ (Kernel y z L W) ≤ L := by
  have hrank := LinearMap.finrank_range_le (evenSquareClassMap y L)
  have heven : Module.finrank F₂ (Even L) = L := by
    simpa only [Module.finrank_fin_fun] using (startBoundaryEquivEven L).finrank_eq.symm
  have hk := TwoTargetKernel.dimension_le_left W (squareClassSpace y L) (squareClassSpace z L) hWZ
  rw [heven] at hrank
  with_unfolding_all exact Nat.le_trans hk hrank

end PaperP1.TwoTargetWindowSections

module

public import PaperP1.Arithmetic.ComponentIntersectionLower
public import PaperP1.Arithmetic.SupportedEvenSquareClasses
public import PaperP1.Asymptotics.SubsetComponentHostData

/-! # Free components on the actual pinned subsets give an intersection of those same subsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetComponentIntersectionLower

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeGraph
  PaperP1.ComponentProjectionInjectivity PaperP1.ShortBasisFinalCut
  PaperP1.MediumPrimeIncidence PaperP1.MediumPrimeColumns PaperP1.LocalDefectBound
  PaperP1.AsymmetricEnvelopeGraph PaperP1.SubsetComponentHostData

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (A : Submodule F₂ T) :
    AddCommGroup A := Submodule.addCommGroup A
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (A : Submodule F₂ T) : Module F₂ A := A.module

theorem finite_bound (x y H R : ℕ) (U V : Finset ℕ) :
    (nontrivial x y H R U V).card ≤
      Module.finrank F₂ ↥(FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V) +
        primeCount (10 * (H + 1)) + 2 := by
  classical
  let : Module.Finite F₂ (FiniteEvenSquareClasses.space U) :=
    Module.Finite.range (EvenImage.evenMap (FiniteEvenSquareClasses.data U))
  let X := start x R
  let Y := start y R
  let G := largePrimeGraph X Y H
  let Q := nontrivial x y H R U V
  let z := 10 * (H + 1)
  let A : Submodule F₂ (Q → F₂) := ⊤
  have hX : 1 ≤ X := by dsimp [X, start]; omega
  have hY : 1 ≤ Y := by dsimp [Y, start]; omega
  have hQ : IsFreeFamily X Y H Q := by
    intro c hc
    have hd := (mem_nontrivial x y H R U V c).mp hc
    exact (PinnedGraphResolution.mem_nontrivialUnpinnedComponents _).mpr
      ⟨SubsetEnvelopeGraph.original_unpinned U V c hd.1, hd.2⟩
  have hA : A ≤ LinearMap.ker (actualMap X Y H z Q) := by
    intro w _hw
    apply (actual_kernel_iff X Y H z Q w).mpr
    intro p hp
    have hh := (mem_mediumPrimes H z p).mp hp
    dsimp [z] at hh
    omega
  let f := relationMap X Y H z Q hX hY hQ A hA
  have hmem (w : CutSpace X Y H z Q A) :
      ShortBasisActualSpace.commonClasses X Y H (f w) ∈
        FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V := by
    have hgraph := ComponentSelection.selection_mem_graph G Q
      (fun c hc ↦ ((mem_nontrivial x y H R U V c).mp hc).1)
      (coefficientMap X Y H z Q A w)
    have hc := (mem_completeRelationCode (f w).val).mp (f w).property
    constructor
    · change (vertexParityMap X H (fun i ↦ (f w).val (Sum.inl i))) ∈ _
      rw [vertexParityMap_apply]
      apply SupportedEvenSquareClasses.combination_mem _ _ U hc.2.1
      intro i hi
      exact hgraph.2 (Sum.inl i) (mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩)))
    · rw [ShortBasisActualSpace.commonClasses_equal]
      rw [vertexParityMap_apply]
      apply SupportedEvenSquareClasses.combination_mem _ _ V hc.2.2
      intro i hi
      exact hgraph.2 (Sum.inr i) (mem_union_right _
        (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩))
  let g : CutSpace X Y H z Q A →ₗ[F₂]
      ↥(FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V) :=
    ((ShortBasisActualSpace.commonClasses X Y H).comp f).codRestrict _ hmem
  have hg : Function.Injective g := by
    intro u v huv
    apply square_class_image_injective X Y H z Q hX hY hQ A
    exact congrArg Subtype.val huv
  have hmono := LinearMap.finrank_le_finrank_of_injective hg
  have hd := dimension_lower X Y H z Q A
  have htop : Module.finrank F₂ A = Q.card := by
    simp only [A, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [htop] at hd
  dsimp [z] at hd hmono
  change Q.card ≤ _
  omega

end PaperP1.SubsetComponentIntersectionLower

module

public import PaperP1.Affine.TwoWindowLabels
public import PaperP1.Affine.PairRelationDimension
public import PaperP1.Combinatorics.LargePrimeOccurrences

/-! # Complete even relations in two actual formal windows

The full prime-parity equation is imposed on both formal vertex copies,
together with the separate evenness condition in each block. The kernel
dimension includes local relations and the actual common square classes.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open PaperP1.Arithmetic LargePrimeOccurrences Finset

local instance twoWindowRelationPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

abbrev EvenVertexSelection (L : ℕ) := LinearMap.ker (startVertexSum L)

def pairVertexParityMap (x y L : ℕ) : (Occurrence L → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v ↦ parityVec (twoStartCompleteVertexLabel x y L v))

def pairLeftSum (L : ℕ) : (Occurrence L → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ i, w (Sum.inl i)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by simp [mul_sum]

def pairRightSum (L : ℕ) : (Occurrence L → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ i, w (Sum.inr i)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by simp [mul_sum]

def completeRelationCode (x y L : ℕ) : Submodule F₂ (Occurrence L → F₂) :=
  LinearMap.ker (pairVertexParityMap x y L) ⊓
    (LinearMap.ker (pairLeftSum L) ⊓ LinearMap.ker (pairRightSum L))

theorem mem_completeRelationCode {x y L : ℕ} (w : Occurrence L → F₂) :
    w ∈ completeRelationCode x y L ↔ pairVertexParityMap x y L w = 0 ∧
      (∑ i, w (Sum.inl i)) = 0 ∧ (∑ i, w (Sum.inr i)) = 0 := by
  simp only [completeRelationCode, Submodule.mem_inf, LinearMap.mem_ker,
    pairLeftSum, pairRightSum, LinearMap.coe_mk, AddHom.coe_mk]

def completePairMap (x y L : ℕ) :
    (EvenVertexSelection L × EvenVertexSelection L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (evenSquareClassMap x L).coprod (evenSquareClassMap y L)

theorem pairVertexParityMap_elim (x y L : ℕ) (u v : EvenVertexSelection L) :
    pairVertexParityMap x y L (Sum.elim u.val v.val) =
      evenSquareClassMap x L u + evenSquareClassMap y L v := by
  change (∑ z : Occurrence L, Sum.elim u.val v.val z •
    parityVec (twoStartCompleteVertexLabel x y L z)) =
      (∑ i, u.val i • parityVec (startCompleteVertexLabel x L i)) +
        ∑ i, v.val i • parityVec (startCompleteVertexLabel y L i)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, twoStartCompleteVertexLabel]

def completeRelationEquivPair (x y L : ℕ) : completeRelationCode x y L ≃ₗ[F₂]
    LinearMap.ker (completePairMap x y L) where
  toFun w := by
    have hw := (mem_completeRelationCode w.val).mp w.property
    let u : EvenVertexSelection L := ⟨fun i ↦ w.val (Sum.inl i), by
      change (∑ i, w.val (Sum.inl i)) = 0
      exact hw.2.1⟩
    let v : EvenVertexSelection L := ⟨fun i ↦ w.val (Sum.inr i), by
      change (∑ i, w.val (Sum.inr i)) = 0
      exact hw.2.2⟩
    refine ⟨(u, v), ?_⟩
    change evenSquareClassMap x L u + evenSquareClassMap y L v = 0
    rw [← pairVertexParityMap_elim]
    have hfun : Sum.elim u.val v.val = w.val := by funext z; cases z <;> rfl
    rw [hfun]
    exact hw.1
  invFun w := by
    refine ⟨Sum.elim w.val.1.val w.val.2.val, ?_⟩
    apply (mem_completeRelationCode _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [pairVertexParityMap_elim]
      exact w.property
    · change startVertexSum L w.val.1.val = 0
      exact w.val.1.property
    · change startVertexSum L w.val.2.val = 0
      exact w.val.2.property
  left_inv w := by
    apply Subtype.ext
    funext z
    cases z <;> rfl
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem finrank_completeRelationCode (x y L : ℕ) :
    Module.finrank F₂ (completeRelationCode x y L) =
      Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) +
        Module.finrank F₂ (LinearMap.ker (evenSquareClassMap y L)) +
          Module.finrank F₂ (squareClassSpace x L ⊓ squareClassSpace y L :
            Submodule F₂ (ℕ →₀ F₂)) := by
  rw [(completeRelationEquivPair x y L).finrank_eq]
  exact finrank_coprod_kernel_eq (evenSquareClassMap x L) (evenSquareClassMap y L)

end PaperP1.Affine

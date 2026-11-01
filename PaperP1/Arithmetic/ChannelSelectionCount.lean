module

public import PaperP1.Arithmetic.ChannelSumIdentity
public import PaperP1.Arithmetic.ParityVector
public import PaperP1.Algebra.EvenSupportRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.FieldTheory.Finiteness

/-! # A_d counts actual binary even selections with prescribed extreme units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelSelectionCount

open Finset PaperP1.Arithmetic

local instance channelSelectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance channelSelectionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- A gap of m+1 has m interior unit positions and two prescribed selected endpoints. -/
def EndpointSelections (m : ℕ) :=
  {w : Fin (m + 2) → F₂ // w 0 = 1 ∧ w (Fin.last (m + 1)) = 1 ∧ ∑ i, w i = 0}

instance endpointFintype (m : ℕ) : Fintype (EndpointSelections m) := by
  unfold EndpointSelections
  infer_instance

def extend (m : ℕ) (v : Fin m → F₂) : Fin (m + 2) → F₂ := Fin.cons 1 (Fin.snoc v 1)

theorem extend_sum (m : ℕ) (v : Fin m → F₂) : ∑ i, extend m v i = ∑ i, v i := by
  unfold extend
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hone : (1 : F₂) + 1 = 0 := by decide
  calc
    _ = (1 + 1 : F₂) + ∑ i, v i := by ring
    _ = _ := by rw [hone, zero_add]

theorem extend_restrict (m : ℕ) (w : Fin (m + 2) → F₂)
    (hzero : w 0 = 1) (hlast : w (Fin.last (m + 1)) = 1) :
    extend m (fun i : Fin m ↦ w i.castSucc.succ) = w := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hzero.symm
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [extend, Fin.cons_succ, Fin.snoc_last]
      change 1 = w (Fin.last (m + 1))
      exact hlast.symm
    · simp only [extend, Fin.cons_succ, Fin.snoc_castSucc]

def interiorEquiv (m : ℕ) :
    LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin m)) ≃ EndpointSelections m where
  toFun v := ⟨extend m v.val, by
    refine ⟨by simp [extend], ?_, ?_⟩
    · change extend m v.val (Fin.last m).succ = 1
      simp only [extend, Fin.cons_succ, Fin.snoc_last]
    · rw [extend_sum]
      exact (EvenSupportRank.sumMap_apply v.val).symm.trans v.property⟩
  invFun w := ⟨(fun i : Fin m ↦ w.val i.castSucc.succ), by
    rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply]
    have hsum := congrArg (fun f : Fin (m + 2) → F₂ ↦ ∑ i, f i)
      (extend_restrict m w.val w.property.1 w.property.2.1)
    rw [extend_sum] at hsum
    exact hsum.trans w.property.2.2⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    simp only [extend, Fin.cons_succ, Fin.snoc_castSucc]
  right_inv w := by
    apply Subtype.ext
    exact extend_restrict m w.val w.property.1 w.property.2.1

theorem endpoint_card (m : ℕ) : Fintype.card (EndpointSelections m) = 2 ^ (m - 1) := by
  rw [← Fintype.card_congr (interiorEquiv m),
    Module.card_eq_pow_finrank (K := F₂) (V := LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin m))),
    EvenSupportRank.kernel_sum_finrank, Fintype.card_fin]
  rw [ZMod.card]

theorem weight_eq_endpoint_card (m : ℕ) :
    ChannelSumIdentity.weight (m + 1) = (Fintype.card (EndpointSelections m) : ℤ) := by
  rw [endpoint_card, Nat.cast_pow, Nat.cast_ofNat]
  by_cases hm : m = 0
  · subst m
    norm_num [ChannelSumIdentity.weight]
  · exact ChannelSumIdentity.weight_succ (by omega)

end PaperP1.ChannelSelectionCount

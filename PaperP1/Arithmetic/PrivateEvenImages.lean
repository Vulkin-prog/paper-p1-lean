module

public import PaperP1.Arithmetic.FiniteEvenSquareClasses

/-! # Private coordinates separate even images unless at least two values coincide -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateEvenImages

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance privateEvenPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem coefficient_zero_of_absent {S T U : Finset ℕ} (hprivate : Private U)
    (hS : S ⊆ U) (hT : T ⊆ U) (u : S → F₂) (v : T → F₂)
    (heq : EvenImage.combination (data S) u = EvenImage.combination (data T) v)
    (n : S) (hnT : n.val ∉ T) : u n = 0 := by
  obtain ⟨p, hp, hothers⟩ := hprivate n.val (hS n.property)
  have hcoord := congrArg (fun f : ℕ →₀ F₂ ↦ f p) heq
  rw [EvenImage.combination_apply, EvenImage.combination_apply] at hcoord
  change (∑ m : S, u m • parityVec m.val) p = (∑ m : T, v m • parityVec m.val) p at hcoord
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hcoord
  have hleft : (∑ m : S, u m * parityVec m.val p) = u n * parityVec n.val p := by
    apply sum_eq_single n
    · intro m _ hmn
      rw [hothers m.val (hS m.property) (fun h ↦ hmn (Subtype.ext h)), mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  have hright : (∑ m : T, v m * parityVec m.val p) = 0 := by
    apply sum_eq_zero
    intro m _
    have hmn : m.val ≠ n.val := by intro h; exact hnT (h ▸ m.property)
    rw [hothers m.val (hT m.property) hmn, mul_zero]
  rw [hleft, hright] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hp

theorem disjoint_of_inter_card_le_one (S T : Finset ℕ) (hprivate : Private (S ∪ T))
    (hcard : (S ∩ T).card ≤ 1) : Disjoint (space S) (space T) := by
  apply Submodule.disjoint_def.mpr
  intro z hzS hzT
  obtain ⟨u, hu, hmapu⟩ := (EvenImage.mem_image_iff (data S) z).mp hzS
  obtain ⟨v, _, hmapv⟩ := (EvenImage.mem_image_iff (data T) z).mp hzT
  have heq := hmapu.trans hmapv.symm
  have hout (n : S) (hnT : n.val ∉ T) : u n = 0 :=
    coefficient_zero_of_absent hprivate (subset_union_left) (subset_union_right) u v heq n hnT
  have hu0 : u = 0 := by
    funext n
    by_cases hnT : n.val ∈ T
    · have hsum : (∑ m : S, u m) = u n := by
        apply sum_eq_single n
        · intro m _ hmn
          by_cases hmT : m.val ∈ T
          · have hval : m.val = n.val :=
              card_le_one.mp hcard _ (mem_inter.mpr ⟨m.property, hmT⟩) _ (mem_inter.mpr ⟨n.property, hnT⟩)
            exact (hmn (Subtype.ext hval)).elim
          · exact hout m hmT
        · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
      exact hsum.symm.trans hu
    · exact hout n hnT
  rw [hu0, map_zero] at hmapu
  exact hmapu.symm

theorem two_le_inter_card (S T : Finset ℕ) (hprivate : Private (S ∪ T))
    (hdep : ¬Disjoint (space S) (space T)) : 2 ≤ (S ∩ T).card := by
  by_contra h
  exact hdep (disjoint_of_inter_card_le_one S T hprivate (by omega))

end PaperP1.PrivateEvenImages

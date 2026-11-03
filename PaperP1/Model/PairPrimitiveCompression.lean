module

public import PaperP1.Affine.PrimitiveCompressionCriterion
public import PaperP1.Affine.RelationLossMonotonicity
public import PaperP1.Model.CoreCanonicalComponents
public import PaperP1.Model.NoSingletonSeedCover
public import PaperP1.Model.FixedPairExtensions

/-! # Actual primitive extensions of one compressed pair: deletion losses and canonical connectedness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairPrimitiveCompression

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.SubspaceFamilyRank
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RelationProjectionRank
  PaperP1.ActualCanonicalComponents PaperP1.RelationCoreWitnesses

local instance pairPrimitiveCompressionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def nullity (L : ℕ) (e A : Finset ℕ) : ℕ :=
  MinimalRelativeRelations.nullity (FixedPairExtensions.sourceSpace e L) (fun x ↦ squareClassSpace x L) A

/-- Every proper compressed subfamily is direct, including the subfamily obtained by deleting the source. -/
def Primitive (L : ℕ) (e A : Finset ℕ) : Prop :=
  Disjoint e A ∧ runRelativeNullity L A = 0 ∧ 0 < nullity L e A ∧
    ∀ B : Finset ℕ, B ⊂ A → nullity L e B = 0

theorem primitive_iff_augmented (L : ℕ) (e A : Finset ℕ) (hdis : Disjoint e A) :
    Primitive L e A ↔
      (0 < relativeNullityOn
        (MinimalRelativeRelations.augmented (FixedPairExtensions.sourceSpace e L) (fun x ↦ squareClassSpace x L))
        (MinimalRelativeRelations.indices A) ∧
      ∀ J : Finset (Option ℕ), J ⊂ MinimalRelativeRelations.indices A →
        relativeNullityOn (MinimalRelativeRelations.augmented (FixedPairExtensions.sourceSpace e L)
          (fun x ↦ squareClassSpace x L)) J = 0) := by
  let : Fintype (FixedPairExtensions.sourceSpace e L) := MinimalRelativeRelations.spanFintype _ e
  rw [PrimitiveCompressionCriterion.primitive_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hdis, h⟩⟩

theorem nonempty (L : ℕ) (e A : Finset ℕ) (h : Primitive L e A) : A.Nonempty := by
  classical
  let : Fintype (FixedPairExtensions.sourceSpace e L) := MinimalRelativeRelations.spanFintype _ e
  by_contra hn
  have hz : nullity L e A = 0 := by
    rw [not_nonempty_iff_eq_empty.mp hn]
    exact MinimalRelativeRelations.nullity_empty _ _
  have hp := h.2.2.1
  omega

theorem union_nullity (L : ℕ) (e A : Finset ℕ) (h : Primitive L e A) :
    runRelativeNullity L (e ∪ A) = runRelativeNullity L e + nullity L e A :=
  MinimalRelativeRelations.source_union_identity (fun x ↦ squareClassSpace x L) e A h.1

theorem target_loss (L : ℕ) (e A : Finset ℕ) (h : Primitive L e A) (x : ℕ) (hx : x ∈ A) :
    loss (fun x ↦ squareClassSpace x L) (e ∪ A) x = nullity L e A := by
  have hxe : x ∉ e := fun he ↦ disjoint_left.mp h.1 he hx
  have herase : (e ∪ A).erase x = e ∪ A.erase x := by
    rw [erase_union_distrib, erase_eq_of_notMem hxe]
  have hsmall := MinimalRelativeRelations.source_union_identity (fun x ↦ squareClassSpace x L)
    e (A.erase x) (h.1.mono_right (erase_subset x A))
  have hz := h.2.2.2 (A.erase x) (erase_ssubset hx)
  change runRelativeNullity L (e ∪ A.erase x) = runRelativeNullity L e + nullity L e (A.erase x) at hsmall
  rw [hz, Nat.add_zero] at hsmall
  change runRelativeNullity L (e ∪ A) - runRelativeNullity L ((e ∪ A).erase x) = _
  rw [herase, hsmall, union_nullity L e A h, Nat.add_sub_cancel_left]

theorem source_loss (L : ℕ) (e A : Finset ℕ) (he : e.card = 2) (_h : Primitive L e A)
    (x : ℕ) (hx : x ∈ e) :
    runRelativeNullity L e ≤ loss (fun x ↦ squareClassSpace x L) (e ∪ A) x := by
  change relativeNullityOn (fun x ↦ squareClassSpace x L) e ≤ _
  rw [← RelationLossMonotonicity.pair_loss (fun x ↦ squareClassSpace x L) e he x hx]
  exact RelationLossMonotonicity.mono _ e (e ∪ A) subset_union_left x hx

theorem core (t L : ℕ) (e A : Finset ℕ) (he : e.card = 2) (h : Primitive L e A)
    (hepos : t - 1 ≤ runRelativeNullity L e) (hapos : t - 1 ≤ nullity L e A) :
    Core t L (e ∪ A) := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · exact hepos.trans (source_loss L e A he h x hx)
  · rw [target_loss L e A h x hx]
    exact hapos

theorem loss_le_local_rank (L : ℕ) (I : Finset ℕ) (x : ℕ) (hx : x ∈ I) :
    loss (fun x ↦ squareClassSpace x L) I x ≤ Module.finrank F₂ (squareClassSpace x L) := by
  rw [loss_eq_dimension (fun x ↦ squareClassSpace x L) I ⟨x, hx⟩]
  exact Submodule.finrank_le _

theorem source_rank_bound (L : ℕ) (e : Finset ℕ) (he : e.card = 2) (hpos : ∀ x ∈ e, 0 < x) :
    runRelativeNullity L e ≤ L := by
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
  change relativeNullityOn (fun x ↦ squareClassSpace x L) e ≤ L
  rw [← RelationLossMonotonicity.pair_loss (fun x ↦ squareClassSpace x L) e he x hx]
  exact (loss_le_local_rank L e x hx).trans (LocalRunRank.squareClass_rank_le x L (hpos x hx))

theorem target_rank_bound (L : ℕ) (e A : Finset ℕ) (h : Primitive L e A)
    (hpos : ∀ x ∈ A, 0 < x) : nullity L e A ≤ L := by
  obtain ⟨x, hx⟩ := nonempty L e A h
  rw [← target_loss L e A h x hx]
  exact (loss_le_local_rank L (e ∪ A) x (mem_union_right e hx)).trans
    (LocalRunRank.squareClass_rank_le x L (hpos x hx))

theorem size (L : ℕ) (e A : Finset ℕ) (he : e.card = 2) (h : Primitive L e A) :
    3 ≤ (e ∪ A).card := by
  have hne := (nonempty L e A h).card_pos
  rw [card_union_of_disjoint h.1, he]
  omega

theorem pair_in_block (L : ℕ) (e A C : Finset ℕ) (he : e.card = 2)
    (hdep : 0 < runRelativeNullity L e) (hC : C ∈ blocks L (e ∪ A)) (hxC : (e ∩ C).Nonempty) : e ⊆ C := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  obtain ⟨z, hz⟩ := hxC
  have hzpair : z = x ∨ z = y := by simpa only [mem_insert, mem_singleton] using (mem_inter.mp hz).1
  have hzC := (mem_inter.mp hz).2
  have hpair : x ∈ C ∧ y ∈ C := by
    have hsame (v w : ℕ) (hvw : v ≠ w) (heq : ({v, w} : Finset ℕ) = {x, y})
        (hv : v ∈ C) : w ∈ C := by
      by_contra hw
      have hwI : w ∈ ({x, y} : Finset ℕ) ∪ A := by rw [← heq]; simp
      have hwU : w ∈ (blocks L ({x, y} ∪ A)).biUnion id := by rw [union_blocks]; exact hwI
      obtain ⟨D, hD, hwD⟩ := mem_biUnion.mp hwU
      have hne : C ≠ D := fun hCD ↦ hw (hCD ▸ hwD)
      have hdis := (NoSingletonSeedCover.distinct_blocks L ({x, y} ∪ A) C D hC hD hne).2
      have hsmall : Disjoint (squareClassSpace v L) (squareClassSpace w L) :=
        hdis.mono (local_le_span (fun x ↦ squareClassSpace x L) C hv)
          (local_le_span (fun x ↦ squareClassSpace x L) D hwD)
      have hz := RetainedNullity.nullity_pair_eq_intersection (fun x ↦ squareClassSpace x L) v w hvw
      rw [hsmall.eq_bot, finrank_bot] at hz
      change runRelativeNullity L {v, w} = 0 at hz
      rw [heq] at hz
      omega
    rcases hzpair with hzx | hzy
    · have hxC : x ∈ C := hzx ▸ hzC
      exact ⟨hxC, hsame x y hxy rfl hxC⟩
    · have hyC : y ∈ C := hzy ▸ hzC
      exact ⟨hsame y x hxy.symm (pair_comm y x) hyC, hyC⟩
  intro v hv
  rcases (show v = x ∨ v = y by simpa only [mem_insert, mem_singleton] using hv) with rfl | rfl
  · exact hpair.1
  · exact hpair.2

theorem connected (L : ℕ) (e A : Finset ℕ) (he : e.card = 2)
    (hdep : 0 < runRelativeNullity L e) (h : Primitive L e A) : ConnectedWindowFamilies.Connected L (e ∪ A) := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
  have hxU : x ∈ (blocks L (e ∪ A)).biUnion id := by rw [union_blocks]; exact mem_union_left A hx
  obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hxU
  have heC := pair_in_block L e A C he hdep hC ⟨x, mem_inter.mpr ⟨hx, hxC⟩⟩
  have hcore : Core 2 L (e ∪ A) := core 2 L e A he h (by omega) (by have hp := h.2.2.1; omega)
  by_contra hconn
  have hcount := nonconnected_card L (e ∪ A) ⟨x, mem_union_left A hx⟩ hconn
  obtain ⟨D, hD, hDC⟩ := exists_mem_ne (show 1 < (blocks L (e ∪ A)).card by omega) C
  have hdis := (NoSingletonSeedCover.distinct_blocks L (e ∪ A) C D hC hD hDC.symm).1
  have hDA : D ⊆ A := by
    intro y hy
    rcases mem_union.mp (block_subset L (e ∪ A) D hD hy) with he | ha
    · exact False.elim (disjoint_left.mp hdis (heC he) hy)
    · exact ha
  have hpos := CrossingPairTriple.connected_positive L D
    (CoreCanonicalComponents.block_card 2 L (by omega) (e ∪ A) hcore D hD) (block_connected L (e ∪ A) D hD)
  have hmono := relativeNullityOn_mono (fun x ↦ squareClassSpace x L) hDA
  have hz := h.2.1
  change runRelativeNullity L D ≤ runRelativeNullity L A at hmono
  omega

theorem rank_dichotomy (L : ℕ) (e A : Finset ℕ) (he : e.card = 2) (h : Primitive L e A)
    (hpos : ∀ x ∈ e ∪ A, 0 < x) :
    runRelativeNullity L (e ∪ A) ≤ L + 2 ∨
      Core 4 L (e ∪ A) ∧ runRelativeNullity L (e ∪ A) ≤ 2 * L := by
  have hecap := source_rank_bound L e he (fun x hx ↦ hpos x (mem_union_left A hx))
  have hacap := target_rank_bound L e A h (fun x hx ↦ hpos x (mem_union_right e hx))
  have hid := union_nullity L e A h
  by_cases hsmall : runRelativeNullity L e ≤ 2 ∨ nullity L e A ≤ 2
  · exact Or.inl (by rcases hsmall with hsmall | hsmall <;> omega)
  · push Not at hsmall
    exact Or.inr ⟨core 4 L e A he h (by omega) (by omega), by omega⟩

end PaperP1.PairPrimitiveCompression

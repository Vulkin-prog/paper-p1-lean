module

public import PaperP1.Affine.CompressedBlocks
public import PaperP1.Arithmetic.GoodEdgeCompression
public import PaperP1.Model.CompatibleNullityBound

/-! # The actual first retained class and its boundary on regular arithmetic windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedGoodEdges

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.SubspaceFamilyRank
open PaperP1.GoodEdgeCompression PaperP1.Model.InfiniteStarts

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def Retained (H : ℝ) (N L : ℕ) (I : Finset ℕ) : Prop :=
  PaperP1.CompressedBlocks.SourceRetained (fun x ↦ squareClassSpace x L) (goodEdges H N L) I

theorem good_pair_card (H : ℝ) (N L : ℕ) (e : Finset ℕ) (he : e ∈ goodEdges H N L) : e.card = 2 := by
  classical
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  have hgood := (mem_filter.mp hxy).2
  have hlt := hgood.2.2.1
  simp [hlt.ne]

theorem good_pair_regular {H : ℝ} {N L : ℕ} (hN : 2 ≤ N)
    (e : Finset ℕ) (he : e ∈ goodEdges H N L) : e ⊆ PaperP1.RegularStarts.regularStarts N L := by
  classical
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  have hr := goodEdge_regular hN (mem_filter.mp hxy).2
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hr.1
  · simpa only [mem_singleton.mp hx] using hr.2

theorem good_pair_positive (H : ℝ) (N L : ℕ) (e : Finset ℕ) (he : e ∈ goodEdges H N L) :
    0 < runRelativeNullity L e := by
  classical
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  have hgood := (mem_filter.mp hxy).2
  have hneq := hgood.2.2.1.ne
  have hdep := hgood.2.2.2.2.1
  rw [runRelativeNullity, PaperP1.RetainedNullity.nullity_pair_eq_intersection _ _ _ hneq]
  apply Nat.pos_of_ne_zero
  intro hz
  have hbot := Submodule.finrank_eq_zero.mp hz
  exact hdep (disjoint_iff.mpr hbot)

theorem good_pair_nullity_le {H : ℝ} {N L : ℕ} (hN : 2 ≤ N)
    (e : Finset ℕ) (he : e ∈ goodEdges H N L) :
    (runRelativeNullity L e : ℝ) ≤ (L : ℝ) / 3 + 1 := by
  classical
  have hcard := good_pair_card H N L e he
  have hreg := good_pair_regular hN e he
  obtain ⟨x, y, a, b, rfl, hlead, hconclusion⟩ := main_3_5 hN e he
  have hxy : x ≠ y := by intro h; simp [h] at hcard
  have hxrank := (PaperP1.RegularStarts.mem_regularStarts.mp (hreg (by simp : x ∈ ({x, y} : Finset ℕ)))).2
  have hyrank := (PaperP1.RegularStarts.mem_regularStarts.mp (hreg (by simp : y ∈ ({x, y} : Finset ℕ)))).2
  have hdim := rank_add_nullity_on (fun z ↦ squareClassSpace z L) {x, y}
  rw [sum_pair hxy, hxrank, hyrank] at hdim
  change Module.finrank F₂ (span (fun z ↦ squareClassSpace z L) {x, y}) + runRelativeNullity L {x, y} = L + L at hdim
  rw [PaperP1.RetainedNullity.span_pair] at hdim
  have hreal : (Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) : ℝ) +
      runRelativeNullity L {x, y} = (L : ℝ) + L := by exact_mod_cast hdim
  obtain ⟨_, _, _, hbound, _, _⟩ := hconclusion
  rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hbound <;>
    linarith [Nat.cast_nonneg (α := ℝ) L]

theorem nullity_eq_rank_deficit (N L : ℕ) (I : Finset ℕ)
    (hI : I ⊆ PaperP1.RegularStarts.regularStarts N L) :
    runRelativeNullity L I = I.card * L - rank (fun x ↦ squareClassSpace x L) I := by
  have hdim := rank_add_nullity_on (fun x ↦ squareClassSpace x L) I
  have hsum : (∑ x ∈ I, Module.finrank F₂ (squareClassSpace x L)) = I.card * L := by
    calc
      _ = ∑ _x ∈ I, L := sum_congr rfl (fun x hx ↦ (PaperP1.RegularStarts.mem_regularStarts.mp (hI hx)).2)
      _ = _ := by simp
  rw [hsum] at hdim
  change rank (fun x ↦ squareClassSpace x L) I + runRelativeNullity L I = I.card * L at hdim
  omega

theorem hereditary (H : ℝ) (N L : ℕ) : PaperP1.Algebra.Hereditary (Retained H N L) := by
  intro I J hJI hI
  apply (PaperP1.CompressedBlocks.sourceRetained_iff _ _ J).mpr
  apply PaperP1.RetainedDependence.hereditary (fun x ↦ squareClassSpace x L) (goodEdges H N L)
    (good_pair_card H N L) hJI
  exact (PaperP1.CompressedBlocks.sourceRetained_iff _ _ I).mp hI

theorem unique_dependent_pair (H : ℝ) (N L : ℕ) (I : Finset ℕ)
    (hI : Retained H N L I) (hnot : runRelativeNullity L I ≠ 0) :
    ∃ e ∈ goodEdges H N L, e ⊆ I ∧ runRelativeNullity L I = runRelativeNullity L e ∧
      ∀ q : Finset ℕ, q ⊆ I → q.card = 2 → 0 < runRelativeNullity L q → q = e := by
  obtain ⟨e, he, hcomp, _, hunique⟩ := PaperP1.RetainedDependence.dependent_pair_unique
    (fun x ↦ squareClassSpace x L) (goodEdges H N L) (good_pair_card H N L) I
    ((PaperP1.CompressedBlocks.sourceRetained_iff _ _ I).mp hI) hnot
  exact ⟨e, he, hcomp.1, hcomp.2, hunique⟩

theorem finite_boundary_bound {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (I : Finset ℕ) (hreg : I ⊆ PaperP1.RegularStarts.regularStarts N L)
    (hI : PaperP1.Algebra.OrderedBoundary (Retained H N L) I) :
    0 < runRelativeNullity L I ∧ (runRelativeNullity L I : ℝ) ≤ 4 * L / 3 + 1 ∧
      (runRelativeNullity L I : ℝ) < 3 * L / 2 := by
  have hboundary : PaperP1.Algebra.OrderedBoundary
      (PaperP1.RetainedDependence.Retained (fun x ↦ squareClassSpace x L) (goodEdges H N L)) I := by
    constructor
    · intro h
      exact hI.1 ((PaperP1.CompressedBlocks.sourceRetained_iff _ _ I).mpr h)
    · exact (PaperP1.CompressedBlocks.sourceRetained_iff _ _ _).mp hI.2
  have hlocal : ∀ x ∈ I, (Module.finrank F₂ (squareClassSpace x L) : ℝ) ≤ (L : ℝ) := by
    intro x hx
    rw [(PaperP1.RegularStarts.mem_regularStarts.mp (hreg hx)).2]
  have hbound := PaperP1.RetainedDependence.boundary_nullity_bound (fun x ↦ squareClassSpace x L)
    (goodEdges H N L) ((L : ℝ) / 3 + 1) L (by positivity) (good_pair_nullity_le hN) I hboundary hlocal
  change 0 < runRelativeNullity L I ∧ (runRelativeNullity L I : ℝ) ≤ (L : ℝ) / 3 + 1 + L at hbound
  have hlarge : (7 : ℝ) ≤ L := by exact_mod_cast hL
  exact ⟨hbound.1, by linarith [hbound.2], by linarith [hbound.2]⟩

end PaperP1.RetainedGoodEdges

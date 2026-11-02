module

public import PaperP1.Model.PrincipalChannelEdges
public import PaperP1.Model.DirectJointBlocks

/-! # The actual event spaces of principal edges and their independent joint activations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeSpaces

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.SubspaceFamilyRank

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def space (L : ℕ) (e : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) := span (fun x ↦ squareClassSpace x L) e

def coupledPairs (N H L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((PrincipalChannelEdges.edges N H L) ×ˢ (PrincipalChannelEdges.edges N H L)).filter
    fun p ↦ ¬Disjoint (space L p.1) (space L p.2)

def coupledProductMass (N H L : ℕ) : ℝ :=
  ∑ p ∈ coupledPairs N H L, infiniteJointMoment L p.1 * infiniteJointMoment L p.2

def factorialPairs (N H L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((PrincipalChannelEdges.edges N H L) ×ˢ (PrincipalChannelEdges.edges N H L)).filter fun p ↦ p.1 ≠ p.2

def jointSecond (N H L : ℕ) : ℝ := ∑ p ∈ factorialPairs N H L, infiniteJointMoment L (p.1 ∪ p.2)

theorem space_pair (L x y : ℕ) : space L {x, y} = squareClassSpace x L ⊔ squareClassSpace y L := by
  change span (fun z ↦ squareClassSpace z L) (insert x (insert y ∅)) = _
  rw [span_insert, span_insert, span_empty, sup_bot_eq]

theorem site_le {L : ℕ} {e : Finset ℕ} {x : ℕ} (hx : x ∈ e) : squareClassSpace x L ≤ space L e :=
  le_iSup_of_le (⟨x, hx⟩ : e) le_rfl

theorem regular {N H L : ℕ} (hN : 2 ≤ N) {e : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) :
    e ⊆ RegularStarts.regularStarts N L := by
  rcases mem_union.mp he with he | he
  · exact PrivateChannelRank.regular hN (by decide : 0 < 2) (by decide : 2 < 3) (mem_filter.mp he).1
  · exact PrivateChannelRank.regular hN (by decide : 0 < 3) (by decide : 3 < 4) (mem_filter.mp he).1

theorem independent_sets {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {e f : Finset ℕ}
    (he : e ∈ PrincipalChannelEdges.edges N H L)
    (hspaces : Disjoint (space L e) (space L f)) : Disjoint e f := by
  apply disjoint_left.mpr
  intro x hxe hxf
  have hself : Disjoint (squareClassSpace x L) (squareClassSpace x L) := hspaces.mono (site_le hxe) (site_le hxf)
  have hbot : squareClassSpace x L = ⊥ := disjoint_self.mp hself
  have hrank := (RegularStarts.mem_regularStarts.mp (regular hN he hxe)).2
  rw [hbot, finrank_bot] at hrank
  omega

theorem joint_factor {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N)
    {e f : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) (hf : f ∈ PrincipalChannelEdges.edges N H L)
    (hspaces : Disjoint (space L e) (space L f)) :
    infiniteJointMoment L (e ∪ f) = infiniteJointMoment L e * infiniteJointMoment L f := by
  have hpair := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  have hecard := (mem_powersetCard.mp (hpair he)).2
  have hfcard := (mem_powersetCard.mp (hpair hf)).2
  exact DirectJointBlocks.factor L hL e f (card_pos.mp (by omega)) (card_pos.mp (by omega))
    (independent_sets hN hL he hspaces) hspaces

theorem independent_ne {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N)
    {e f : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) (hf : f ∈ PrincipalChannelEdges.edges N H L)
    (hspaces : Disjoint (space L e) (space L f)) : e ≠ f := by
  intro hef
  have hdis := independent_sets hN hL he hspaces
  rw [hef] at hdis
  have hfempty : f = ∅ := disjoint_self.mp hdis
  have hcard := (mem_powersetCard.mp (PrincipalChannelEdges.subset_pairs (H := H) hN hlarge hf)).2
  rw [hfempty, card_empty] at hcard
  omega

theorem beta_squared_le_joint_add_coupled {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N) :
    PrincipalChannelEdges.beta N H L ^ 2 ≤ jointSecond N H L + coupledProductMass N H L := by
  let E := PrincipalChannelEdges.edges N H L
  have hpoint (p : Finset ℕ × Finset ℕ) (hp : p ∈ E ×ˢ E) :
      infiniteJointMoment L p.1 * infiniteJointMoment L p.2 ≤
        (if p.1 ≠ p.2 then infiniteJointMoment L (p.1 ∪ p.2) else 0) +
        (if ¬Disjoint (space L p.1) (space L p.2) then infiniteJointMoment L p.1 * infiniteJointMoment L p.2 else 0) := by
    obtain ⟨he, hf⟩ := mem_product.mp hp
    by_cases hdep : ¬Disjoint (space L p.1) (space L p.2)
    · rw [ite_eq_left hdep]
      have hn : 0 ≤ if p.1 ≠ p.2 then infiniteJointMoment L (p.1 ∪ p.2) else 0 := by
        split_ifs
        · exact infiniteJointMoment_nonneg L _
        · rfl
      linarith only [hn]
    · have hspaces := not_not.mp hdep
      rw [ite_eq_right hdep, ite_eq_left (independent_ne hN hL hlarge he hf hspaces), add_zero,
        joint_factor hN hL hlarge he hf hspaces]
  calc
    _ = ∑ p ∈ E ×ˢ E, infiniteJointMoment L p.1 * infiniteJointMoment L p.2 := by
      rw [sum_product, ← sum_mul_sum, pow_two]
      rfl
    _ ≤ ∑ p ∈ E ×ˢ E,
        ((if p.1 ≠ p.2 then infiniteJointMoment L (p.1 ∪ p.2) else 0) +
          (if ¬Disjoint (space L p.1) (space L p.2) then infiniteJointMoment L p.1 * infiniteJointMoment L p.2 else 0)) :=
      sum_le_sum hpoint
    _ = _ := by rw [sum_add_distrib, ← sum_filter, ← sum_filter]; rfl

end PaperP1.PrincipalEdgeSpaces

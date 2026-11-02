module

public import PaperP1.Model.CompatibleChannelEdges
public import PaperP1.Model.PrivateChannelHostSupport

/-! # The literal compatible edge family of the two principal channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalChannelEdges

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrivateChannelSources PaperP1.PrivateChannelActivity

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def edges (N H L : ℕ) : Finset (Finset ℕ) :=
  CompatibleChannelEdges.edges N H 2 3 L ∪ CompatibleChannelEdges.edges N H 3 4 L

def beta (N H L : ℕ) : ℝ := ∑ e ∈ edges N H L, infiniteJointMoment L e

theorem forward_disjoint {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    Disjoint (goodSources N H 2 3 L) (goodSources N H 3 4 L) := by
  apply disjoint_left.mpr
  intro xy h23 h34
  have hxy23 := FixedChannelLinearCount.unit_alignment (by omega : 0 < N)
    (good_sources_subset_unitSources N H 2 3 L h23)
  have hxy34 := FixedChannelLinearCount.unit_alignment (by omega : 0 < N)
    (good_sources_subset_unitSources N H 3 4 L h34)
  have hx : N ≤ xy.1 := (mem_Ico.mp (mem_goodSources.mp h23).1).1
  have h23le := abs_le.mp hxy23
  have h34le := abs_le.mp hxy34
  push_cast at h23le h34le
  have hlargeZ : (29 : ℤ) * (L + 1) < N := by exact_mod_cast hlarge
  have hxZ : (N : ℤ) ≤ xy.1 := by exact_mod_cast hx
  norm_num at h23le h34le
  nlinarith only [h23le.2, h34le.1, hlargeZ, hxZ]

theorem unordered_disjoint {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    Disjoint (pairs N H 2 3 L) (pairs N H 3 4 L) := by
  apply disjoint_left.mpr
  intro e h23 h34
  obtain ⟨xy, hxy, hxe⟩ := mem_image.mp h23
  obtain ⟨uv, huv, hue⟩ := mem_image.mp h34
  have hxylt := good_sources_order hN (by decide : 2 < 3) (by omega) hxy
  have huvlt := good_sources_order hN (by decide : 3 < 4) (by omega) huv
  have heq : ({xy.1, xy.2} : Finset ℕ) = {uv.1, uv.2} := hxe.trans hue.symm
  have hx : xy.1 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← heq]; simp
  have hy : xy.2 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← heq]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  have hp : xy = uv := Prod.ext (by omega) (by omega)
  exact disjoint_left.mp (forward_disjoint hN hlarge) hxy (hp ▸ huv)

theorem compatible_disjoint {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    Disjoint (CompatibleChannelEdges.edges N H 2 3 L) (CompatibleChannelEdges.edges N H 3 4 L) :=
  (unordered_disjoint hN hlarge).mono (filter_subset _ _) (filter_subset _ _)

theorem card_bound {N H L : ℕ} (hN : 0 < N) :
    (edges N H L).card ≤ 26 * (L + 1) * N := by
  calc
    _ ≤ (CompatibleChannelEdges.edges N H 2 3 L).card + (CompatibleChannelEdges.edges N H 3 4 L).card := card_union_le _ _
    _ ≤ (2 * (2 + 3) + 1) * (L + 1) * N + (2 * (3 + 4) + 1) * (L + 1) * N :=
      Nat.add_le_add (CompatibleChannelEdges.card_bound hN (by decide : 0 < 2))
        (CompatibleChannelEdges.card_bound hN (by decide : 0 < 3))
    _ = _ := by ring

theorem beta_eq {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    beta N H L = (channelMass N H 2 3 L + channelMass N H 3 4 L) / 2 := by
  rw [beta, edges, sum_union (compatible_disjoint hN hlarge),
    CompatibleChannelEdges.joint_mass_eq hN (by decide : 2 < 3) (by omega),
    CompatibleChannelEdges.joint_mass_eq hN (by decide : 3 < 4) (by omega)]
  ring

theorem subset_pairs {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    edges N H L ⊆ (dyadicBlock N).powersetCard 2 := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact mem_powersetCard.mpr (pair_data hN (by decide : 2 < 3) (by omega) (mem_filter.mp he).1)
  · exact mem_powersetCard.mpr (pair_data hN (by decide : 3 < 4) (by omega) (mem_filter.mp he).1)

theorem activity_gap {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) (hL : 0 < L) :
    0 ≤ beta N H L - CompatibleActivitySplit.absolute L (edges N H L) ∧
      beta N H L - CompatibleActivitySplit.absolute L (edges N H L) ≤
        independentMass N H 2 3 L + independentMass N H 3 4 L := by
  have ha23 := CompatibleChannelEdges.absolute_eq (H := H) hN (by decide : 2 < 3) (by omega : (2 + 3) * (L + 1) < N) hL
  have ha34 := CompatibleChannelEdges.absolute_eq (H := H) hN (by decide : 3 < 4) (by omega : (3 + 4) * (L + 1) < N) hL
  have ha : CompatibleActivitySplit.absolute L (edges N H L) =
      CompatibleActivitySplit.absolute L (CompatibleChannelEdges.edges N H 2 3 L) +
      CompatibleActivitySplit.absolute L (CompatibleChannelEdges.edges N H 3 4 L) :=
    sum_union (compatible_disjoint hN hlarge)
  have hi23 := CompatibleChannelEdges.absolute_comparison (H := H) hN (by decide : 2 < 3) (by omega : (2 + 3) * (L + 1) < N) hL
  have hi34 := CompatibleChannelEdges.absolute_comparison (H := H) hN (by decide : 3 < 4) (by omega : (3 + 4) * (L + 1) < N) hL
  have hp23 : 0 ≤ CompatibleChannelEdges.independentMass N H 2 3 L :=
    sum_nonneg fun e _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hp34 : 0 ≤ CompatibleChannelEdges.independentMass N H 3 4 L :=
    sum_nonneg fun e _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  rw [beta_eq hN hlarge, ha, ha23, ha34]
  exact ⟨by linarith only [hp23, hp34], by linarith only [(abs_le.mp hi23).1, (abs_le.mp hi34).1, ha23, ha34]⟩

theorem beta_nonneg (N H L : ℕ) : 0 ≤ beta N H L :=
  sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e

end PaperP1.PrincipalChannelEdges

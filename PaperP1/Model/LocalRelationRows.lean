module

public import PaperP1.Arithmetic.LocalRelationSets
public import PaperP1.Affine.OneRelationMass
public import PaperP1.Model.RelativeSignIndependence

/-! # The actual affine phase and marginal of a window with one even square relation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRelationRows

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.LocalRelationSets PaperP1.WindowRelationCode

theorem boundary_mem_code_iff {M x L : ℕ} (hx : 0 < x) (hcut : x + L ≤ M) (u : Fin L → F₂) :
    startCompleteBoundary L u ∈ windowRelationCode (x - 1) (L + 1) ↔
      relationMap (startSystem M x L) u = 0 := by
  have hidentity : relationMap (startSystem M x L) u =
      parityPairing M (vertexParityMap x L (startCompleteBoundary L u)) := by
    rw [relationMap_start_eq_parityPairing]
    rfl
  constructor
  · intro hu
    have hzero := (PaperP1.LocalRunRank.mem_start_windowRelationCode hx _).mp hu
    rw [hidentity, show vertexParityMap x L (startCompleteBoundary L u) = 0 from hzero.1, map_zero]
  · intro hu
    apply (PaperP1.LocalRunRank.mem_start_windowRelationCode hx _).mpr
    refine ⟨?_, startVertexSum_startCompleteBoundary_eq_zero u⟩
    have hS : vertexParityMap x L (startCompleteBoundary L u) ∈ squareClassSpace x L :=
      ⟨startBoundaryToEven L u, rfl⟩
    apply parityPairing_injOn_bounded M (squareClassSpace_le_boundedPrimeParity hcut hS)
      ((boundedPrimeParity M).zero_mem)
    simpa only [hidentity, map_zero] using hu

theorem only_two_row_relations {M x L : ℕ} (hx : 0 < x) (hcut : x + L ≤ M)
    (hrank : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (u : Fin L → F₂) (hu : u ≠ 0) (hrel : relationMap (startSystem M x L) u = 0) :
    ∀ v, relationMap (startSystem M x L) v = 0 → v = 0 ∨ v = u := by
  let : Fintype (windowRelationCode (x - 1) (L + 1)) := Fintype.ofFinite _
  let w : windowRelationCode (x - 1) (L + 1) :=
    ⟨startCompleteBoundary L u, (boundary_mem_code_iff hx hcut u).mpr hrel⟩
  have hw : w ≠ 0 := by
    intro h
    apply hu
    apply startCompleteBoundary_injective L
    have hval := congrArg Subtype.val h
    change startCompleteBoundary L u = 0 at hval
    simpa only [map_zero] using hval
  intro v hv
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  · right
    let z : windowRelationCode (x - 1) (L + 1) :=
      ⟨startCompleteBoundary L v, (boundary_mem_code_iff hx hcut v).mpr hv⟩
    have hz : z ≠ 0 := by
      intro h
      apply hv0
      apply startCompleteBoundary_injective L
      have hval := congrArg Subtype.val h
      change startCompleteBoundary L v = 0 at hval
      simpa only [map_zero] using hval
    have hzw := BinaryRankOne.nonzero_eq hrank z w hz hw
    exact startCompleteBoundary_injective L (congrArg Subtype.val hzw)

theorem incidence_root_eq_rhs {L : ℕ} (hL : 0 < L) (i : Fin L) :
    startIncidenceColumn i (startRootVertex L) = startRhs L i := by
  let i₀ : Fin L := ⟨0, hL⟩
  have hprivate : startPrivateVertex i₀ = startRootVertex L := by simp [startPrivateVertex, i₀]
  have h := startIncidenceColumn_apply_private i₀ i
  rw [hprivate] at h
  simpa [startRhs_apply, Fin.ext_iff, i₀] using h

theorem dot_rhs_eq_root {L : ℕ} (hL : 0 < L) (u : Fin L → F₂) :
    dotProduct u (startRhs L) = startCompleteBoundary L u (startRootVertex L) := by
  change (∑ i, u i * startRhs L i) = _
  rw [startCompleteBoundary_apply]
  simp_rw [incidence_root_eq_rhs hL]

theorem one_relation_marginal {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hrank : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (S : Finset ℕ) (hS : S ⊆ window x L) (hrel : Relation S) :
    infiniteMarginal x L = if x - 1 ∈ S then 0 else 2 * (2 ^ L : ℝ)⁻¹ := by
  classical
  have hword := (PaperP1.LocalRunRank.mem_start_windowRelationCode hx _).mp (word_mem_code hx S hS hrel)
  obtain ⟨u, hu⟩ := startBoundaryToEven_surjective L ⟨word x L S, hword.2⟩
  have hboundary : startCompleteBoundary L u = word x L S := congrArg Subtype.val hu
  have hune : u ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hboundary
    exact word_ne_zero hx S hS hrel.1 hboundary.symm
  have hrow : relationMap (startSystem (x + L) x L) u = 0 := by
    apply (boundary_mem_code_iff hx le_rfl u).mp
    rw [hboundary]
    exact word_mem_code hx S hS hrel
  have hphase : dotProduct u (startRhs L) = if x - 1 ∈ S then 1 else 0 := by
    rw [dot_rhs_eq_root hL, hboundary]
    simp only [word, startCompleteVertexLabel_root]
  rw [infiniteMarginal_eq_finite (M := x + L) le_rfl,
    exactMarginal_start_eq_affineMass (x + L) x L hL,
    uniformSolutionMass_eq_one_add_sign _ _ u hune hrow (only_two_row_relations hx le_rfl hrank u hune hrow)]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat, hphase]
  by_cases hp : x - 1 ∈ S <;> simp [hp, binarySign]
  ring

end PaperP1.LocalRelationRows

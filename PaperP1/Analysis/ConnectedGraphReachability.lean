module

public import PaperP1.Analysis.AnchoredNormalizedGraph
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Data.Finset.Insert

/-! # Connected local graph neighborhoods yield one actual chart for every finite population

Local graph neighborhoods inside the set are the explicit geometric premise.
Actual chart gluing proves that the points reachable from an anchor form a
clopen subset. No component-wide chart or finite-population cover is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedGraphReachability

open MvPolynomial Set Filter LocalNormalizedGraphPiece AnchoredNormalizedGraph
open scoped Topology


def LocalCharts (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) : Prop :=
  ∀ z ∈ C, ∃ q : Piece P, z 0 ∈ Ioo q.left q.right ∧
    (fun i ↦ q.path i (z 0)) = z ∧ pointImage q ⊆ C

def Reachable (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor z : Fin 2 → ℝ) : Prop :=
  ∃ A : Anchored P C anchor, z ∈ pointImage A.chart

theorem reachable_subset (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor z : Fin 2 → ℝ)
    (hz : Reachable P C anchor z) : z ∈ C := by
  obtain ⟨A, hA⟩ := hz
  exact A.image_subset hA

theorem reachable_anchor (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor : Fin 2 → ℝ)
    (ha : anchor ∈ C) (hlocal : LocalCharts P C) : Reachable P C anchor anchor := by
  obtain ⟨q, ht, he, hsub⟩ := hlocal anchor ha
  let A : Anchored P C anchor := ⟨q, ht, he, hsub⟩
  exact ⟨A, anchor_in_image A⟩

theorem reachable_clopen (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor : Fin 2 → ℝ)
    (hlocal : LocalCharts P C) : IsClopen {z : C | Reachable P C anchor z.val} := by
  have hzero (w : C) : eval w.val P = 0 := by
    obtain ⟨q, ht, he, _hsub⟩ := hlocal w.val w.property
    rw [← he]
    exact q.equation (w.val 0) ht
  have hopen : IsOpen {z : C | Reachable P C anchor z.val} := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨A, hzA⟩ := hz
    obtain ⟨t, ht, he⟩ := hzA
    obtain ⟨U, hU, hmem, hcover⟩ := NormalizedGraphImageNeighborhood.exists_open_neighborhood P A.chart t ht
    have hzu : z ∈ Subtype.val ⁻¹' U := by
      change z.val ∈ U
      rw [← he]
      exact hmem
    apply Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hzu)
    intro w hw
    obtain ⟨hx, hp⟩ := hcover w.val hw (hzero w)
    exact ⟨A, ⟨w.val 0, hx, hp⟩⟩
  have hcompl : IsOpen ({z : C | Reachable P C anchor z.val}ᶜ) := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change ¬Reachable P C anchor z.val at hz
    obtain ⟨q, hparam, he, hsub⟩ := hlocal z.val z.property
    obtain ⟨U, hU, hmem, hcover⟩ := NormalizedGraphImageNeighborhood.exists_open_neighborhood P q (z.val 0) hparam
    have hzu : z ∈ Subtype.val ⁻¹' U := by
      change z.val ∈ U
      rw [← he]
      exact hmem
    apply Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hzu)
    intro w hw
    change ¬Reachable P C anchor w.val
    intro hwR
    obtain ⟨A, hwA⟩ := hwR
    obtain ⟨hx, hp⟩ := hcover w.val hw (hzero w)
    obtain ⟨B, _hAB, hqB⟩ := attach A q hsub w.val hwA ⟨w.val 0, hx, hp⟩
    exact hz ⟨B, hqB ⟨z.val 0, hparam, he⟩⟩
  exact ⟨isOpen_compl_iff.mp hcompl, hopen⟩

theorem reachable_all (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor : Fin 2 → ℝ)
    (ha : anchor ∈ C) (hC : IsPreconnected C) (hlocal : LocalCharts P C) :
    ∀ z ∈ C, Reachable P C anchor z := by
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have hclopen := reachable_clopen P C anchor hlocal
  have hnonempty : ({z : C | Reachable P C anchor z.val} : Set C).Nonempty :=
    ⟨⟨anchor, ha⟩, reachable_anchor P C anchor ha hlocal⟩
  have heq := hclopen.eq_univ hnonempty
  intro z hz
  have hm : (⟨z, hz⟩ : C) ∈ {w : C | Reachable P C anchor w.val} := by
    rw [heq]
    exact mem_univ _
  exact hm

theorem exists_chart_for_finite_population (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ))
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ C) (hC : IsPreconnected C) (hlocal : LocalCharts P C)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ z ∈ S, z ∈ C) :
    ∃ A : Anchored P C anchor, ∀ z ∈ S, z ∈ pointImage A.chart := by
  classical
  have hall := reachable_all P C anchor ha hC hlocal
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro _hS
    obtain ⟨A, _hA⟩ := hall anchor ha
    exact ⟨A, by simp⟩
  | @insert z S _hz ih =>
    intro hS
    obtain ⟨A, hA⟩ := ih (fun w hw ↦ hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨Az, hzAz⟩ := hall z (hS z (Finset.mem_insert_self _ _))
    obtain ⟨B, hAB, hzB⟩ := attach A Az.chart Az.image_subset anchor (anchor_in_image A) (anchor_in_image Az)
    refine ⟨B, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hzB hzAz
    · exact hAB (hA w hw)

end PaperP1.ConnectedGraphReachability

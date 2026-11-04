module

public import PaperP1.Probability.PositionalDeletionSupport

/-! # The pointwise cost of removing every remaining active pair

No degree bound is required. The cost is at most two vertices per extra
active edge, plus the original count outside the retained ground.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalAllPairCost

open Finset PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalCountProjection

variable {ι : Type*}

local instance allPairCostDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def restrict (G : Finset ι) (v : Configuration ι) : Configuration ι := v.filter (fun x ↦ x ∈ G)

def outside (G : Finset ι) (v : Configuration ι) : Configuration ι := v.filter (fun x ↦ x ∉ G)

theorem restrict_le (G : Finset ι) (v : Configuration ι) (x : ι) : restrict G v x ≤ v x := by
  rw [restrict, Finsupp.filter_apply]
  split_ifs <;> omega

theorem restrict_add_outside (G : Finset ι) (v : Configuration ι) :
    restrict G v + outside G v = v := by
  ext x
  simp only [restrict, outside, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hx : x ∈ G <;> simp [hx]

theorem count_restrict_add (G : Finset ι) (v : Configuration ι) :
    totalCount (restrict G v) + totalCount (outside G v) = totalCount v := by
  have hh := congrArg totalCount (restrict_add_outside G v)
  simpa only [map_add] using hh

theorem outside_mono (G : Finset ι) {u v : Configuration ι} (h : ∀ x, u x ≤ v x) :
    totalCount (outside G u) ≤ totalCount (outside G v) := by
  apply totalCount_mono
  intro x
  by_cases hx : x ∈ G
  · simp only [outside, Finsupp.filter_apply, not_not.mpr hx, ite_false]
    exact le_rfl
  · simp only [outside, Finsupp.filter_apply, ite_eq_left hx]
    exact h x

theorem active_restrict (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G) : activeEdges E (restrict G v) = activeEdges E v := by
  ext e
  simp only [activeEdges, mem_filter]
  apply and_congr_right
  intro he
  have hx (x : ι) (hxe : x ∈ e) : restrict G v x = v x := by
    simp only [restrict, Finsupp.filter_apply, ite_eq_left (hE e he hxe)]
  exact ⟨fun h x hxe ↦ by simpa only [hx x hxe] using h x hxe,
    fun h x hxe ↦ by simpa only [hx x hxe] using h x hxe⟩

theorem isolate_restrict (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G) : isolate E (restrict G v) = restrict G (isolate E v) := by
  have hv : vertices E (restrict G v) = vertices E v := by
    simp only [vertices, active_restrict G E v hE]
  ext x
  rw [isolate, Finsupp.filter_apply, hv]
  simp only [restrict, isolate, Finsupp.filter_apply]
  by_cases hxG : x ∈ G <;> by_cases hxE : x ∈ vertices E v <;> simp [hxG, hxE]

theorem active_mono (E F : Finset (Finset ι)) (v : Configuration ι) (hEF : E ⊆ F) :
    activeEdges E v ⊆ activeEdges F v := by
  intro e he
  exact mem_filter.mpr ⟨hEF (mem_filter.mp he).1, (mem_filter.mp he).2⟩

theorem vertices_mono (E F : Finset (Finset ι)) (v : Configuration ι) (hEF : E ⊆ F) :
    vertices E v ⊆ vertices F v := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨e, active_mono E F v hEF he, hxe⟩

theorem isolate_antitone (E F : Finset (Finset ι)) (v : Configuration ι) (hEF : E ⊆ F)
    (x : ι) : isolate F v x ≤ isolate E v x := by
  simp only [isolate, Finsupp.filter_apply]
  by_cases hxF : x ∈ vertices F v
  · simp only [not_not.mpr hxF, ite_false]
    exact Nat.zero_le _
  · have hxE : x ∉ vertices E v := fun hx ↦ hxF (vertices_mono E F v hEF hx)
    simp only [hxF, hxE, not_false_eq_true, ite_true]
    exact le_rfl

theorem active_union [DecidableEq ι] (E D : Finset (Finset ι)) (v : Configuration ι) :
    activeEdges (E ∪ D) v = activeEdges E v ∪ activeEdges D v := by
  ext e
  simp only [activeEdges, mem_filter, mem_union]
  tauto

theorem vertices_union [DecidableEq ι] (E D : Finset (Finset ι)) (v : Configuration ι) :
    vertices (E ∪ D) v = vertices E v ∪ vertices D v := by
  ext x
  simp only [vertices, active_union, mem_biUnion, mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

theorem extra_edge_cost [DecidableEq ι] (E F : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hEF : E ⊆ F) (hF : ∀ e ∈ F, e.card = 2) :
    totalCount (isolate F v) ≤ totalCount (isolate E v) ∧
      totalCount (isolate E v) - totalCount (isolate F v) ≤ 2 * (activeEdges (F \ E) v).card := by
  have hmono := totalCount_mono (isolate_antitone E F v hEF)
  have hEcount := totalCount_isolate_binary_add E v hv
  have hFcount := totalCount_isolate_binary_add F v hv
  have hcover : (vertices F v).card ≤ (vertices E v).card + (vertices (F \ E) v).card := by
    have he : E ∪ (F \ E) = F := union_sdiff_of_subset hEF
    have hvertices := vertices_union E (F \ E) v
    rw [he] at hvertices
    rw [hvertices]
    exact card_union_le (vertices E v) (vertices (F \ E) v)
  have hD := vertices_card_upper (F \ E) v (fun e he ↦ hF e (mem_sdiff.mp he).1)
  exact ⟨hmono, by omega⟩

theorem full_cost [DecidableEq ι] (G : Finset ι) (E F : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hEF : E ⊆ F) (hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2) :
    totalCount (isolate F (restrict G v)) ≤ totalCount (isolate E v) ∧
      totalCount (isolate E v) - totalCount (isolate F (restrict G v)) ≤
        2 * (activeEdges (F \ E) v).card + totalCount (outside G v) := by
  have hE : ∀ e ∈ E, e ⊆ G := fun e he ↦ (hF e (hEF he)).1
  have hD : ∀ e ∈ F \ E, e ⊆ G := fun e he ↦ (hF e (mem_sdiff.mp he).1).1
  have hbinary : ∀ x, restrict G v x ≤ 1 := fun x ↦ (restrict_le G v x).trans (hv x)
  have hmid := extra_edge_cost E F (restrict G v) hbinary hEF (fun e he ↦ (hF e he).2)
  rw [isolate_restrict G E v hE, active_restrict G (F \ E) v hD] at hmid
  have hsplit := count_restrict_add G (isolate E v)
  have hout := outside_mono G (isolate_le E v)
  exact ⟨by omega, by omega⟩

theorem disagreement_cost [DecidableEq ι] (G : Finset ι) (E F : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hEF : E ⊆ F) (hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2) :
    (if totalCount (isolate E v) ≠ totalCount (isolate F (restrict G v)) then 1 else 0) ≤
      (activeEdges (F \ E) v).card + totalCount (outside G v) := by
  have hh := full_cost G E F v hv hEF hF
  split_ifs <;> omega

end PaperP1.PositionalAllPairCost

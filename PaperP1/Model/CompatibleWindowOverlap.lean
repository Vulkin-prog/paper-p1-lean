module

public import PaperP1.Model.RunSeparation
public import PaperP1.Model.JointBranchingEvents
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Positive actual joint mass leaves at most one common complete-window value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleWindowOverlap

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.NormalizedWindowSets

theorem interval_overlap_le_one {x z L : ℕ} (hx : 0 < x) (hz : 0 < z)
    (hsep : x + L ≤ z ∨ z + L ≤ x) : (values x L ∩ values z L).card ≤ 1 := by
  rw [values_eq_interval hx, values_eq_interval hz]
  apply card_le_one.mpr
  intro n hn m hm
  obtain ⟨hnx, hnz⟩ := mem_inter.mp hn
  obtain ⟨hmx, hmz⟩ := mem_inter.mp hm
  simp only [mem_Ico] at hnx hnz hmx hmz
  rcases hsep with hsep | hsep <;> omega

theorem joint_event_nonempty (A : Finset ℕ) {L : ℕ} (hL : 0 < L)
    (hq : 0 < infiniteJointMoment L A) : (JointBranchingEvents.jointEvent A L).Nonempty := by
  classical
  have hprob : 0 < infiniteRademacherMeasure.real (JointBranchingEvents.jointEvent A L) := by
    rwa [← JointBranchingEvents.infiniteJointMoment_eq_probability A hL]
  by_contra h
  have hempty := Set.not_nonempty_iff_eq_empty.mp h
  simp [hempty] at hprob

theorem compatible_pair_separated {x z L : ℕ} (hxz : x ≠ z) (hL : 0 < L)
    (hq : 0 < infiniteJointMoment L {x, z}) : x + L ≤ z ∨ z + L ≤ x := by
  obtain ⟨ω, hω⟩ := joint_event_nonempty {x, z} hL hq
  change ∀ n ∈ ({x, z} : Finset ℕ), StartEvent (infiniteValueBit ω) n L at hω
  have hxEvent := hω x (mem_insert_self _ _)
  have hzEvent := hω z (mem_insert_of_mem (mem_singleton_self _))
  rcases lt_or_gt_of_ne hxz with hlt | hgt
  · exact Or.inl (RunSeparation.startEvent_separated _ hxEvent hzEvent hlt)
  · exact Or.inr (RunSeparation.startEvent_separated _ hzEvent hxEvent hgt)

theorem compatible_pair_overlap_le_one {x z L : ℕ} (hx : 0 < x) (hz : 0 < z) (hxz : x ≠ z)
    (hL : 0 < L) (hq : 0 < infiniteJointMoment L {x, z}) : (values x L ∩ values z L).card ≤ 1 :=
  interval_overlap_le_one hx hz (compatible_pair_separated hxz hL hq)

theorem triple_joint_pairs {x y z L : ℕ} (hq : 0 < infiniteJointMoment L {x, y, z}) :
    0 < infiniteJointMoment L {x, z} ∧ 0 < infiniteJointMoment L {y, z} := by
  have hsubX : ({x, z} : Finset ℕ) ⊆ {x, y, z} := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn ⊢
    rcases hn with hn | hn <;> simp [hn]
  have hsubY : ({y, z} : Finset ℕ) ⊆ {x, y, z} := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn ⊢
    rcases hn with hn | hn <;> simp [hn]
  exact ⟨hq.trans_le (infiniteJointMoment_antitone L hsubX), hq.trans_le (infiniteJointMoment_antitone L hsubY)⟩

end PaperP1.CompatibleWindowOverlap

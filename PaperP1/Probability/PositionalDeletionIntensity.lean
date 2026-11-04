module

public import PaperP1.Probability.PositionalDeletionSupport
public import PaperP1.Probability.PositionalFactorialCovariance
public import PaperP1.Probability.PositiveCountBonferroni

/-! # Exact coordinate removals and nonnegative incidence remainders

The once-deletion rule is the actual uniform choice of an active edge.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletionIntensity

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalDeletionKernels
  PaperP1.PositionalFactorialCovariance

variable {ι : Type*}

local instance intensityDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def incident (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) : ℝ :=
  ∑ e ∈ activeEdges E v, if x ∈ e then 1 else 0

def removedOnce (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) : ℝ :=
  ((activeEdges E v).card : ℝ)⁻¹ * incident E v x

def removedAll (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) : ℝ :=
  if x ∈ vertices E v then (v x : ℝ) else 0

theorem incident_nonneg (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    0 ≤ incident E v x := sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)

theorem incident_eq_card (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    incident E v x = (((activeEdges E v).filter fun e ↦ x ∈ e).card : ℝ) :=
  sum_boole _ _

theorem incident_le_card (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    incident E v x ≤ ((activeEdges E v).card : ℝ) := by
  rw [incident_eq_card]
  exact_mod_cast card_le_card (filter_subset _ _)

theorem incident_eq_zero (E : Finset (Finset ι)) (v : Configuration ι)
    (hne : ¬(activeEdges E v).Nonempty) (x : ι) : incident E v x = 0 := by
  rw [incident, not_nonempty_iff_eq_empty.mp hne, sum_empty]

theorem removedOnce_bounds (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    0 ≤ removedOnce E v x ∧ removedOnce E v x ≤ incident E v x := by
  constructor
  · exact mul_nonneg (by positivity) (incident_nonneg E v x)
  · by_cases hne : (activeEdges E v).Nonempty
    · have hk : (1 : ℝ) ≤ (activeEdges E v).card := by exact_mod_cast card_pos.mpr hne
      have hi : ((activeEdges E v).card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
      exact (mul_le_mul_of_nonneg_right hi (incident_nonneg E v x)).trans_eq (one_mul _)
    · simp only [removedOnce, incident_eq_zero E v hne x, mul_zero]
      exact le_rfl

theorem delete_coordinate (E : Finset (Finset ι)) (v : Configuration ι)
    (e : Finset ι) (he : e ∈ activeEdges E v) (x : ι) :
    (deleteEdge e v x : ℝ) = (v x : ℝ) - if x ∈ e then 1 else 0 := by
  have hh := congrArg (fun u : Configuration ι ↦ u x) (deleteEdge_add E v he)
  simp only [Finsupp.add_apply, edgeVector_apply] at hh
  have hr := congrArg (fun n : ℕ ↦ (n : ℝ)) hh
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hr
  linarith only [hr]

theorem onceKernel_mean (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    mean (onceKernel E v) x = (v x : ℝ) - removedOnce E v x := by
  by_cases hne : (activeEdges E v).Nonempty
  · rw [mean, onceKernel, ite_eq_left hne,
      (PositionalUniformAtoms.hasSum_test _ _ (fun w ↦ (w x : ℝ))).tsum_eq]
    have he := sum_congr rfl (fun e he ↦ delete_coordinate E v e he x)
    rw [he, sum_sub_distrib, sum_const, nsmul_eq_mul]
    have hk : ((activeEdges E v).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    dsimp only [removedOnce, incident]
    field_simp
  · rw [mean, onceKernel, ite_eq_right hne,
      (PositionalDeterministicMap.hasSum_atom_test v (fun w ↦ (w x : ℝ))).tsum_eq]
    simp only [removedOnce, incident_eq_zero E v hne x, mul_zero, sub_zero]

theorem isolate_coordinate (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    (isolate E v x : ℝ) = (v x : ℝ) - removedAll E v x := by
  rw [isolate, Finsupp.filter_apply, removedAll]
  by_cases hx : x ∈ vertices E v <;> simp [hx]

theorem removedAll_bounds (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (x : ι) :
    0 ≤ removedAll E v x ∧ removedAll E v x ≤ incident E v x := by
  constructor
  · unfold removedAll
    split_ifs <;> positivity
  · by_cases hx : x ∈ vertices E v
    · rw [removedAll, ite_eq_left hx, incident_eq_card]
      have hpos : 0 < ((activeEdges E v).filter fun e ↦ x ∈ e).card := by
        apply card_pos.mpr
        obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
        exact ⟨e, mem_filter.mpr ⟨he, hxe⟩⟩
      exact_mod_cast (show v x ≤ ((activeEdges E v).filter fun e ↦ x ∈ e).card by
        have hcap := hv x
        omega)
    · rw [removedAll, ite_eq_right hx]
      exact incident_nonneg E v x

theorem sum_incident (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, incident E v x) = 2 * ((activeEdges E v).card : ℝ) := by
  unfold incident
  rw [sum_comm]
  have he : (∑ e ∈ activeEdges E v, ∑ x ∈ G, if x ∈ e then (1 : ℝ) else 0) =
      ∑ _e ∈ activeEdges E v, (2 : ℝ) := by
    apply sum_congr rfl
    intro e he
    have hed := hE e (mem_filter.mp he).1
    have hf : G.filter (fun x ↦ x ∈ e) = e := by
      ext x
      simp only [mem_filter]
      exact ⟨fun h ↦ h.2, fun hx ↦ ⟨hed.1 hx, hx⟩⟩
    rw [← sum_filter, hf, sum_const, nsmul_eq_mul, hed.2]
    norm_num
  rw [he, sum_const, nsmul_eq_mul]
  ring

theorem sum_removedOnce (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, removedOnce E v x) = if (activeEdges E v).Nonempty then 2 else 0 := by
  unfold removedOnce
  rw [← mul_sum, sum_incident G E v hE]
  by_cases hne : (activeEdges E v).Nonempty
  · rw [ite_eq_left hne]
    have hk : ((activeEdges E v).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    field_simp
  · rw [ite_eq_right hne, not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero, mul_zero, mul_zero]

theorem sum_removedAll (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e ⊆ G) :
    (∑ x ∈ G, removedAll E v x) = ((vertices E v).card : ℝ) := by
  have hs : vertices E v ⊆ G := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
    exact hE e (mem_filter.mp he).1 hxe
  have hf : G.filter (fun x ↦ x ∈ vertices E v) = vertices E v := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun hx ↦ ⟨hs hx, hx⟩⟩
  unfold removedAll
  rw [← sum_filter, hf]
  have hh : (∑ x ∈ vertices E v, (v x : ℝ)) = ∑ _x ∈ vertices E v, (1 : ℝ) := by
    apply sum_congr rfl
    intro x hx
    have hp := vertices_positive E v hx
    have hc := hv x
    have he : v x = 1 := by omega
    rw [he, Nat.cast_one]
  rw [hh, sum_const, nsmul_eq_mul, mul_one]

theorem once_remainder (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, (incident E v x - removedOnce E v x)) =
      2 * (((activeEdges E v).card : ℝ) - if (activeEdges E v).Nonempty then 1 else 0) := by
  rw [sum_sub_distrib, sum_incident G E v hE, sum_removedOnce G E v hE]
  split_ifs <;> ring

theorem isolated_remainder (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, (incident E v x - removedAll E v x)) ≤
      2 * (((activeEdges E v).card : ℝ) - if (activeEdges E v).Nonempty then 1 else 0) := by
  rw [sum_sub_distrib, sum_incident G E v hE, sum_removedAll G E v hv (fun e he ↦ (hE e he).1)]
  by_cases hne : (activeEdges E v).Nonempty
  · rw [ite_eq_left hne]
    have hl : (2 : ℝ) ≤ (vertices E v).card := by exact_mod_cast vertices_card_lower E v (fun e he ↦ (hE e he).2) hne
    linarith only [hl]
  · rw [ite_eq_right hne]
    have hl : (0 : ℝ) ≤ (vertices E v).card := by positivity
    linarith only [hl]

theorem twice_excess_le_factorial (E : Finset (Finset ι)) (v : Configuration ι) :
    2 * (((activeEdges E v).card : ℝ) - if (activeEdges E v).Nonempty then 1 else 0) ≤
      ((activeEdges E v).card : ℝ) * (((activeEdges E v).card : ℝ) - 1) := by
  have hh := (PositiveCountBonferroni.pointwise (activeEdges E v).card).2
  simp only [Nat.cast_pos, card_pos] at hh
  linarith only [hh]

theorem once_factorial_remainder (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, (incident E v x - removedOnce E v x)) ≤
      ((activeEdges E v).card : ℝ) * (((activeEdges E v).card : ℝ) - 1) := by
  rw [once_remainder G E v hE]
  exact twice_excess_le_factorial E v

theorem isolated_factorial_remainder (G : Finset ι) (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, (incident E v x - removedAll E v x)) ≤
      ((activeEdges E v).card : ℝ) * (((activeEdges E v).card : ℝ) - 1) :=
  (isolated_remainder G E v hv hE).trans (twice_excess_le_factorial E v)

end PaperP1.PositionalDeletionIntensity

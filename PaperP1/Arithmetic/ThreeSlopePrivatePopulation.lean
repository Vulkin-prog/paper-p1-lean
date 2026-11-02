module

public import PaperP1.Model.ThreeSlopeWitnessActivity
public import PaperP1.Arithmetic.NormalizedPrivateDefects
public import PaperP1.Arithmetic.GlobalDefectCount

/-! # Literal dyadic parameters and the finite defect budget for private rational witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopePrivatePopulation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ThreeSlopeProgressions
  PaperP1.PrivateNormalizedFamilies PaperP1.NormalizedWindowSets PaperP1.GoodEdgeCompression
  PaperP1.DefectivePredicate PaperP1.GlobalDefectCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def parameters (N : ℕ) : Finset ℕ := Icc ((N + 9) / 10) ((2 * N - 1) / 15)

theorem parameter_bounds {N t : ℕ} (hN : 10 ≤ N) (ht : t ∈ parameters N) :
    1 ≤ t ∧ N ≤ 10 * t ∧ 15 * t < 2 * N ∧ t ≤ N := by
  have hh := mem_Icc.mp ht
  omega

theorem centres_dyadic {N t : ℕ} (hN : 10 ≤ N) (ht : t ∈ parameters N) (i : Fin 3) :
    centres t i ∈ dyadicBlock N := by
  have hh := parameter_bounds hN ht
  fin_cases i <;> norm_num [centres, multiple, dyadicBlock, mem_Ico] <;> omega

theorem parameter_count {N : ℕ} (hN : 1000 ≤ N) :
    (N : ℝ) / 60 ≤ ((parameters N).card : ℝ) := by
  have hh : N ≤ 60 * (parameters N).card := by
    rw [parameters, Nat.card_Icc]
    omega
  have hhR : (N : ℝ) ≤ 60 * (parameters N).card := by exact_mod_cast hh
  linarith only [hhR]

theorem step_le_six (i : Fin 3) : step i ≤ 6 := by fin_cases i <;> norm_num [step]

theorem union_bounds {t : ℕ} (ht : 1 ≤ t) (L n : ℕ) (hn : n ∈ valueUnion step (centres t) L) :
    60 * t - 6 ≤ n ∧ n ≤ 60 * t + 6 * L := by
  obtain ⟨i, _hi, hni⟩ := mem_biUnion.mp hn
  rw [normalized_progression ht] at hni
  obtain hni | hni := mem_union.mp hni
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp hni
    have hprod := Nat.mul_le_mul (step_le_six i) (show u ≤ L by have hh := mem_range.mp hu; omega)
    omega
  · have heq := mem_singleton.mp hni
    have hh := step_le_six i
    omega

theorem union_dist {t : ℕ} (ht : 1 ≤ t) {L n m : ℕ}
    (hn : n ∈ valueUnion step (centres t) L) (hm : m ∈ valueUnion step (centres t) L) :
    Nat.dist n m < 10 * (L + 1) := by
  have hnB := union_bounds ht L n hn
  have hmB := union_bounds ht L m hm
  rw [Nat.dist]
  omega

def value (t L : ℕ) (i : Fin 3) (v : Fin (L + 1)) : ℕ := step i * startCompleteVertexLabel (centres t i) L v

theorem value_formula {t : ℕ} (ht : 1 ≤ t) (L : ℕ) (i : Fin 3) (v : Fin (L + 1)) :
    value t L i v = 60 * t - step i + step i * v.val := by
  rw [value, startCompleteVertexLabel_eq_offset (by have hh := centres_ge_two ht i; omega),
    Nat.mul_add, predecessor_formula]

theorem value_mem (t L : ℕ) (i : Fin 3) (v : Fin (L + 1)) : value t L i v ∈ valueUnion step (centres t) L := by
  apply normalized_subset step (centres t) L i
  exact mem_image.mpr ⟨_, mem_values.mpr ⟨v, rfl⟩, rfl⟩

theorem value_bounds {N t L : ℕ} (hN : 10 ≤ N) (ht : t ∈ parameters N) (hLN : L ≤ N)
    (i : Fin 3) (v : Fin (L + 1)) : 0 < value t L i v ∧ value t L i v ≤ 66 * N := by
  have htb := parameter_bounds hN ht
  have hv := union_bounds htb.1 L _ (value_mem t L i v)
  omega

theorem value_injective {N L : ℕ} (hN : 10 ≤ N) (i : Fin 3) (v : Fin (L + 1)) :
    Set.InjOn (fun t ↦ value t L i v) (parameters N) := by
  intro t ht u hu heq
  have htb := parameter_bounds hN ht
  have hub := parameter_bounds hN hu
  change value t L i v = value u L i v at heq
  rw [value_formula htb.1, value_formula hub.1] at heq
  have hs := step_le_six i
  omega

def bad (N L : ℕ) : Finset ℕ :=
  (parameters N).filter fun t ↦ ¬PrivateAbove ((10 * (L + 1) : ℕ) : ℝ) (valueUnion step (centres t) L)

def good (N L : ℕ) : Finset ℕ :=
  (parameters N).filter fun t ↦ PrivateAbove ((10 * (L + 1) : ℕ) : ℝ) (valueUnion step (centres t) L)

def defects (N L : ℕ) (i : Fin 3) (v : Fin (L + 1)) : Finset ℕ :=
  (parameters N).filter fun t ↦ HDefective (10 * (L + 1)) (value t L i v)

theorem bad_cover {N L : ℕ} (hN : 10 ≤ N) :
    bad N L ⊆ (univ : Finset (Fin 3 × Fin (L + 1))).biUnion (fun iv ↦ defects N L iv.1 iv.2) := by
  intro t ht
  obtain ⟨htP, hbad⟩ := mem_filter.mp ht
  have htb := (parameter_bounds hN htP).1
  have heq := NormalizedPrivateDefects.privateAbove_iff_nondefective (valueUnion step (centres t) L)
    (fun _ hn _ hm _ ↦ union_dist htb hn hm)
  rw [heq] at hbad
  push Not at hbad
  obtain ⟨n, hn, hdef⟩ := hbad
  obtain ⟨i, _hi, hni⟩ := mem_biUnion.mp hn
  obtain ⟨m, hm, hmn⟩ := mem_image.mp hni
  obtain ⟨v, rfl⟩ := mem_values.mp hm
  refine mem_biUnion.mpr ⟨(i, v), mem_univ _, mem_filter.mpr ⟨htP, ?_⟩⟩
  change HDefective (10 * (L + 1)) (step i * startCompleteVertexLabel (centres t i) L v)
  rwa [hmn]

theorem defect_card {N L : ℕ} (hN : 10 ≤ N) (hLN : L ≤ N) (i : Fin 3) (v : Fin (L + 1)) :
    (defects N L i v).card ≤ (positiveDefectsBelow (10 * (L + 1)) (66 * N)).card := by
  apply card_le_card_of_injOn (fun t ↦ value t L i v)
  · intro t ht
    obtain ⟨htP, htD⟩ := mem_filter.mp ht
    have hv := value_bounds hN htP hLN i v
    exact mem_positiveDefectsBelow.mpr ⟨hv.1.ne', hv.2, htD⟩
  · intro t ht u hu heq
    exact value_injective hN i v (mem_filter.mp ht).1 (mem_filter.mp hu).1 heq

theorem bad_card {N L : ℕ} (hN : 10 ≤ N) (hLN : L ≤ N) :
    (bad N L).card ≤ 3 * (L + 1) * (positiveDefectsBelow (10 * (L + 1)) (66 * N)).card := by
  have hh := (card_le_card (bad_cover (L := L) hN)).trans
    (card_biUnion_le_card_mul (univ : Finset (Fin 3 × Fin (L + 1)))
      (fun iv ↦ defects N L iv.1 iv.2) (positiveDefectsBelow (10 * (L + 1)) (66 * N)).card
      (fun iv _ ↦ defect_card hN hLN iv.1 iv.2))
  simpa only [card_univ, Fintype.card_prod, Fintype.card_fin] using hh

theorem good_bad_partition (N L : ℕ) : (good N L).card + (bad N L).card = (parameters N).card :=
  card_filter_add_card_filter_not (s := parameters N)
    (fun t ↦ PrivateAbove ((10 * (L + 1) : ℕ) : ℝ) (valueUnion step (centres t) L))

end PaperP1.ThreeSlopePrivatePopulation

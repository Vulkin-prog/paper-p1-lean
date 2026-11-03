module

public import PaperP1.Asymptotics.CriticalFiniteRungeIndependence
public import PaperP1.Arithmetic.EnlargedPairGeometry
public import PaperP1.Arithmetic.EvenIndependentIntersection
public import PaperP1.Model.FiniteRademacher

/-! # Actual fixed-size selected grids on any enlarged aligned pair have the precise even-independence needed by the geometric counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalAlignedSelections

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.FiniteEvenSquareClasses PaperP1.EnlargedPairGeometry

theorem uniform_independent (C : ℝ) (K : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ a b : ℕ, 0 < a → 0 < b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 → Geometric a b y z L →
      ∀ S : Finset ℕ, S ⊆ NormalizedWindowSets.union a b y z L → S.card ≤ K →
        EvenIndependentValues.Independent S := by
  obtain ⟨Ni, _hNi, hi⟩ := CriticalFiniteRungeIndependence.uniform_independent C K 6 4 (by norm_num)
  obtain ⟨Ng, hg⟩ := CriticalPolynomialScale.polynomial_lt_scale C 32 (by norm_num) 4
  refine ⟨max 3 (max Ni Ng), by omega, ?_⟩
  intro N hN L hband
  have hpoly : 32 * (L + 1) ^ 4 < N := by exact_mod_cast hg N (by omega) L hband
  have hordered (y z a b : ℕ) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
      (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hheight : b ≤ (L + 1) ^ 3)
      (hgeom : Geometric a b y z L) (S : Finset ℕ)
      (hS : S ⊆ NormalizedWindowSets.union a b y z L) (hcard : S.card ≤ K) :
      EvenIndependentValues.Independent S := by
    have hrad := radius_height hheight
    have hlarge : 8 * radius b L + 8 ≤ N := by
      have hpow : 0 < (L + 1) ^ 4 := by positivity
      nlinarith only [hrad, hpoly, hpow]
    have hbase := base_geometry hb (mem_Ico.mp hy).1 hlarge
    have hypos : 0 < y := by have h := (mem_Ico.mp hy).1; omega
    have hzpos : 0 < z := by have h := (mem_Ico.mp hz).1; omega
    apply hi N (by omega) L hband (base b y L) (2 * radius b L) hbase.2.1
      (by
        have hpos : 0 < 2 * radius b L := by dsimp [radius]; positivity
        omega)
      (by nlinarith only [hrad]) S hcard
    intro n hn
    exact interval_bounds hab hypos hzpos hgeom hbase.1 n (hS hn)
  intro y z hy hz a b ha hb haH hbH hgeom S hS hcard
  by_cases hab : a ≤ b
  · exact hordered y z a b hy hz ha hb hab hbH hgeom S hS hcard
  · apply hordered z y b a hz hy hb ha (by omega) haH ((geometric_swap a b y z L).mp hgeom) S
      (by rw [union_swap b a z y L]; exact hS) hcard

theorem uniform_selected_directness (C : ℝ) (K : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ a b : ℕ, 0 < a → 0 < b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 → Geometric a b y z L →
      ∀ S T : Finset ℕ, S ⊆ NormalizedWindowSets.values y L → T ⊆ NormalizedWindowSets.values z L →
        S.card + T.card ≤ K → (dilate b S ∩ dilate a T).card ≤ 1 →
        EvenIndependentValues.Independent S ∧ EvenIndependentValues.Independent T ∧ Disjoint (space S) (space T) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_independent C K
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband y z hy hz a b ha hb haH hbH hgeom S T hS hT hcard hoverlap
  have hy2 : 2 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hz2 : 2 ≤ z := by have h := (mem_Ico.mp hz).1; omega
  have hSpos : ∀ n ∈ S, 0 < n := fun n hn ↦ values_positive hy2 n (hS hn)
  have hTpos : ∀ n ∈ T, 0 < n := fun n hn ↦ values_positive hz2 n (hT hn)
  have hsubS : dilate b S ⊆ normalized b y L := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact mem_image.mpr ⟨m, hS hm, rfl⟩
  have hsubT : dilate a T ⊆ normalized a z L := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact mem_image.mpr ⟨m, hT hm, rfl⟩
  have hcardU : (dilate b S ∪ dilate a T).card ≤ K :=
    (card_union_le _ _).trans ((Nat.add_le_add card_image_le card_image_le).trans hcard)
  have hind := hu N hN L hband y z hy hz a b ha hb haH hbH hgeom (dilate b S ∪ dilate a T)
    (union_subset_union hsubS hsubT) hcardU
  have hindS := (EvenIndependentValues.dilate_iff hb S hSpos).mp (hind.mono subset_union_left)
  have hindT := (EvenIndependentValues.dilate_iff ha T hTpos).mp (hind.mono subset_union_right)
  have hdirect := EvenIndependentIntersection.disjoint_of_inter_card_le_one hind hoverlap
  rw [space_dilate S hb hSpos, space_dilate T ha hTpos] at hdirect
  exact ⟨hindS, hindT, hdirect⟩

end PaperP1.CriticalAlignedSelections

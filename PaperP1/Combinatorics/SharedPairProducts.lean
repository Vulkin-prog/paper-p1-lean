module

public import PaperP1.Algebra.ElementarySymmetricBound
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Unordered overlapping edge products are bounded by half the sum of squared rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPairProducts

open Finset

variable {ι : Type*} [DecidableEq ι]

def incident (G : Finset ι) (x : ι) : Finset (Finset ι) :=
  (G.powersetCard 2).filter (fun e ↦ x ∈ e)

def overlapping (G : Finset ι) : Finset (Finset (Finset ι)) := by
  classical
  exact ((G.powersetCard 2).powersetCard 2).filter
    (fun S ↦ ∃ x ∈ G, ∀ e ∈ S, x ∈ e)

theorem overlapping_subset (G : Finset ι) :
    overlapping G ⊆ (G.powersetCard 2).powersetCard 2 := by
  classical
  exact filter_subset _ _

theorem pair_mem_overlapping (G e f : Finset ι)
    (he : e ∈ G.powersetCard 2) (hf : f ∈ G.powersetCard 2) (hef : e ≠ f) :
    {e, f} ∈ overlapping G ↔ ¬Disjoint e f := by
  classical
  constructor
  · intro h
    obtain ⟨_, x, _, hx⟩ := mem_filter.mp h
    intro hd
    exact disjoint_left.mp hd (hx e (by simp)) (hx f (by simp))
  · intro h
    obtain ⟨x, hxe, hxf⟩ := not_disjoint_iff.mp h
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_, by simp [hef]⟩,
      x, (mem_powersetCard.mp he).1 hxe, ?_⟩
    · intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption
    · intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption

theorem incident_eq_image (G : Finset ι) (x : ι) (hx : x ∈ G) :
    incident G x = (G.erase x).image (fun y ↦ {x, y}) := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hxe⟩ := mem_filter.mp he
    obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hecard
    rcases (show x = a ∨ x = b by simpa only [mem_insert, mem_singleton] using hxe) with rfl | rfl
    · exact mem_image.mpr ⟨b, mem_erase.mpr ⟨hab.symm, heG (by simp)⟩, rfl⟩
    · exact mem_image.mpr ⟨a, mem_erase.mpr ⟨hab, heG (by simp)⟩, pair_comm _ _⟩
  · intro he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp he
    obtain ⟨hyx, hyG⟩ := mem_erase.mp hy
    exact mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨by intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption,
        by simp [hyx.symm]⟩, mem_insert_self _ _⟩

theorem incident_sum (G : Finset ι) (x : ι) (hx : x ∈ G)
    (w : Finset ι → ℝ) :
    (∑ e ∈ incident G x, w e) = ∑ y ∈ G.erase x, w {x, y} := by
  rw [incident_eq_image G x hx]
  apply sum_image
  intro y hy z hz heq
  change ({x, y} : Finset ι) = {x, z} at heq
  have hym : y ∈ ({x, z} : Finset ι) := by rw [← heq]; simp
  rcases (show y = x ∨ y = z by simpa only [mem_insert, mem_singleton] using hym) with hyx | hyz
  · exact False.elim ((mem_erase.mp hy).1 hyx)
  · exact hyz

theorem overlapping_cover (G : Finset ι) :
    overlapping G ⊆ G.biUnion (fun x ↦ (incident G x).powersetCard 2) := by
  classical
  intro S hS
  obtain ⟨hS, x, hx, hxe⟩ := mem_filter.mp hS
  obtain ⟨hSE, hcard⟩ := mem_powersetCard.mp hS
  exact mem_biUnion.mpr ⟨x, hx, mem_powersetCard.mpr
    ⟨fun e he ↦ mem_filter.mpr ⟨hSE he, hxe e he⟩, hcard⟩⟩

theorem overlapping_bound (G : Finset ι) (w : Finset ι → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ S ∈ overlapping G, ∏ e ∈ S, w e) ≤
      (∑ x ∈ G, (∑ y ∈ G.erase x, w {x, y}) ^ 2) / 2 := by
  classical
  calc
    _ ≤ ∑ S ∈ G.biUnion (fun x ↦ (incident G x).powersetCard 2), ∏ e ∈ S, w e :=
      sum_le_sum_of_subset_of_nonneg (overlapping_cover G)
        (fun S _ _ ↦ prod_nonneg fun e _ ↦ hw e)
    _ ≤ ∑ x ∈ G, ∑ S ∈ (incident G x).powersetCard 2, ∏ e ∈ S, w e :=
      GraphStarWeights.sum_biUnion_le_nonneg G
        (fun x ↦ (incident G x).powersetCard 2) (fun S ↦ ∏ e ∈ S, w e)
        (fun S ↦ prod_nonneg fun e _ ↦ hw e)
    _ ≤ ∑ x ∈ G, (∑ e ∈ incident G x, w e) ^ 2 / 2 := by
      apply sum_le_sum
      intro x _
      simpa only [SubsetPowerSums.elementary, Nat.factorial_two, Nat.cast_ofNat] using
        ElementarySymmetricBound.elementary_le_power_div w hw (incident G x) 2
    _ = _ := by
      rw [sum_div]
      apply sum_congr rfl
      intro x hx
      rw [incident_sum G x hx]

end PaperP1.SharedPairProducts

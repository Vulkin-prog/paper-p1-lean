module

public import PaperP1.Model.HeterogeneousDirectMaximum

/-! # A retained active configuration is dominated by the shifted direct maximum

Deleting one endpoint of the unique compressed pair is a geometric finite
statement. No numerical exceptional-event estimate enters this argument.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedActiveCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Probability
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.MaximumDirectActive PaperP1.DirectActiveEnvelope

local instance retainedActiveCountDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def activeSet (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) : Finset ℕ :=
  activeSites G (fun x ↦ infiniteStartIndicator x L) ω

def retainedActive (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample) : Prop :=
  RetainedGoodEdges.Retained H N L (activeSet G L ω)

def modified (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample) : ℕ :=
  if retainedActive H N L G ω then infiniteStartCount G L ω else 0

theorem erase_pair_endpoint_zero (L : ℕ) (e I : Finset ℕ) (he : e.card = 2)
    (hcomp : RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e I)
    (x : ℕ) (hx : x ∈ e) : runRelativeNullity L (I.erase x) = 0 := by
  rcases RetainedDependence.compressed_subfamily (fun x ↦ squareClassSpace x L) e I (I.erase x)
    he hcomp (erase_subset x I) with hzero | hcompressed
  · exact hzero
  · exact False.elim ((mem_erase.mp (hcompressed.1 hx)).1 rfl)

theorem large_direct_subfamily (H : ℝ) (N L : ℕ) (I : Finset ℕ)
    (hI : RetainedGoodEdges.Retained H N L I) :
    ∃ D ⊆ I, runRelativeNullity L D = 0 ∧ I.card ≤ D.card + 1 := by
  rcases (CompressedBlocks.sourceRetained_iff (fun x ↦ squareClassSpace x L)
    (GoodEdgeCompression.goodEdges H N L) I).mp hI with hzero | ⟨e, he, hcomp⟩
  · exact ⟨I, subset_refl I, hzero, by omega⟩
  · have hcard := RetainedGoodEdges.good_pair_card H N L e he
    obtain ⟨x, hx⟩ : e.Nonempty := card_pos.mp (by omega)
    have hxI := hcomp.1 hx
    refine ⟨I.erase x, erase_subset x I, erase_pair_endpoint_zero L e I hcard hcomp x hx, ?_⟩
    have h := card_erase_add_one hxI
    omega

theorem retained_empty (H : ℝ) (N L : ℕ) : RetainedGoodEdges.Retained H N L ∅ := by
  apply (CompressedBlocks.sourceRetained_iff (fun x ↦ squareClassSpace x L)
    (GoodEdgeCompression.goodEdges H N L) ∅).mpr
  exact Or.inl (relativeNullityOn_empty _)

theorem not_retained_nonempty (H : ℝ) (N L : ℕ) (I : Finset ℕ)
    (hI : ¬ RetainedGoodEdges.Retained H N L I) : I.Nonempty := by
  apply nonempty_iff_ne_empty.mpr
  intro h
  exact hI (h.symm ▸ retained_empty H N L)

theorem activeSet_card (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) :
    (activeSet G L ω).card = infiniteStartCount G L ω := card_activeSites G _ ω

theorem retained_count_le (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample)
    (hret : retainedActive H N L G ω) : infiniteStartCount G L ω ≤ envelope G L ω := by
  obtain ⟨D, hDA, hzero, hcard⟩ := large_direct_subfamily H N L (activeSet G L ω) hret
  have hDG : D ⊆ G := hDA.trans (filter_subset _ _)
  have hactive : ∀ x ∈ D, infiniteStartIndicator x L ω = true := fun x hx ↦ (mem_filter.mp (hDA hx)).2
  have hDF : D ∈ families G L := mem_families.mpr ⟨hDG, hzero⟩
  have hpop : D ∈ HereditaryActiveMaximum.activeFamilies (families G L)
      (fun x ↦ infiniteStartIndicator x L) ω := HereditaryActiveMaximum.active_mem.mpr ⟨hDF, hactive⟩
  have hmax : D.card ≤ maximum G L ω := le_sup (f := Finset.card) hpop
  rw [activeSet_card] at hcard
  unfold envelope
  omega

theorem retained_subfamily_nullity_bound (H : ℝ) {N L : ℕ} (hN : 2 ≤ N)
    (G : Finset ℕ) (ω : InfiniteSample) (hret : retainedActive H N L G ω)
    (I : Finset ℕ) (hI : I ⊆ activeSet G L ω) : (runRelativeNullity L I : ℝ) ≤ (L : ℝ) / 3 + 1 := by
  have hretI := RetainedGoodEdges.hereditary H N L hI hret
  exact RetainedDependence.retained_nullity_le (fun x ↦ squareClassSpace x L)
    (GoodEdgeCompression.goodEdges H N L) ((L : ℝ) / 3 + 1) (by positivity)
    (fun e he ↦ RetainedGoodEdges.good_pair_nullity_le hN e he) I
    ((CompressedBlocks.sourceRetained_iff (fun x ↦ squareClassSpace x L)
      (GoodEdgeCompression.goodEdges H N L) I).mp hretI)

theorem modified_le_envelope (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample) :
    modified H N L G ω ≤ envelope G L ω := by
  unfold modified
  split_ifs with hret
  · exact retained_count_le H N L G ω hret
  · exact Nat.zero_le _

theorem modified_le_original (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample) :
    modified H N L G ω ≤ infiniteStartCount G L ω := by
  unfold modified
  split_ifs <;> omega

theorem modified_eq_original_iff (H : ℝ) (N L : ℕ) (G : Finset ℕ) (ω : InfiniteSample) :
    modified H N L G ω = infiniteStartCount G L ω ↔ retainedActive H N L G ω := by
  by_cases hret : retainedActive H N L G ω
  · simp only [modified, hret, ite_true]
  · have hne := not_retained_nonempty H N L (activeSet G L ω) hret
    have hpos : 0 < infiniteStartCount G L ω := by simpa only [activeSet_card] using card_pos.mpr hne
    simp only [modified, hret, ite_false, iff_false]
    omega

end PaperP1.RetainedActiveCount

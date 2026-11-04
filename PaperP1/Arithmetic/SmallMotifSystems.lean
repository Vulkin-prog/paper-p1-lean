module

public import PaperP1.Arithmetic.SmallMotifCoefficients
public import PaperP1.Arithmetic.SelectedWindowAdmissibility
public import PaperP1.Asymptotics.CoefficientSelectedDegreeOneHostCount
public import PaperP1.Asymptotics.ManyPlanarSquareProducts

/-! # Small transverse square products give literal admissible degree-one systems -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallMotifSystems

open Finset PaperP1.Arithmetic PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes
  PaperP1.PositiveLineOffsetRoots PaperP1.SplitRadicalPointHeight

def pattern {L k : ℕ} (X : Fin 3 → ℕ) (E : Fin k → Finset (Vertex L)) :
    CoefficientSplitRadicalPatterns.Pattern k :=
  ((fun i ↦ integerOffsets (offsets (E i) 0), fun i ↦ integerOffsets (offsets (E i) 1)),
    fun i ↦ SmallMotifCoefficients.coefficient X (E i))

theorem integer_offsets_card {L : ℕ} (I : Finset (Fin (L + 1))) :
    (integerOffsets I).card = I.card := card_image_of_injective _ (integerOffset_injective L)

theorem integer_offsets_bound {L : ℕ} (I : Finset (Fin (L + 1))) :
    integerOffsets I ⊆ BoundedIntegerMotifs.offsets (L + 1) := by
  intro z hz
  obtain ⟨u, _hu, rfl⟩ := mem_image.mp hz
  rw [BoundedIntegerMotifs.offsets, mem_Icc]
  have hh := u.isLt
  dsimp [integerOffset]
  omega

theorem slice_disjoint {L k : ℕ} (E : Fin k → Finset (Vertex L))
    (hE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) (c : Fin 3) :
    Pairwise (fun i j ↦ Disjoint (integerOffsets (offsets (E i) c))
      (integerOffsets (offsets (E j) c))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hzi
  obtain ⟨v, hv, he⟩ := mem_image.mp hzj
  have hveq : v = u := integerOffset_injective L he
  subst v
  exact disjoint_left.mp (hE hij) ((mem_offsets _ _ _).mp hu) ((mem_offsets _ _ _).mp hv)

theorem target_size {L : ℕ} (E : Finset (Vertex L)) (hE : Transverse E) (hsize : E.card ≤ 5) :
    (integerOffsets (offsets E 0)).card + (integerOffsets (offsets E 1)).card ≤ 4 := by
  rw [integer_offsets_card, integer_offsets_card]
  have hh := (hE 2).card_pos
  have hc := card_decomposition E
  omega

theorem pattern_mem {L H k : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (E : Fin k → Finset (Vertex L))
    (hE : ∀ i, Transverse (E i) ∧ (E i).card ≤ 5 ∧ SquareOutside H X (E i)) :
    pattern X E ∈ CoefficientSplitRadicalPatterns.pool k L 4 (SmallMotifCoefficients.pool (X 2) L H) := by
  rw [CoefficientSplitRadicalPatterns.mem_pool]
  have hsize (i : Fin k) := target_size (E i) (hE i).1 (hE i).2.1
  refine ⟨fun i ↦ ⟨integer_offsets_bound _, by have hi := hsize i; dsimp only [pattern]; omega⟩,
    fun i ↦ ⟨integer_offsets_bound _, by have hi := hsize i; dsimp only [pattern]; omega⟩, ?_⟩
  intro i
  exact SmallMotifCoefficients.coefficient_mem X hX (E i) (hE i).2.1 (hE i).2.2

theorem pattern_valid {L k : ℕ} (X : Fin 3 → ℕ) (E : Fin k → Finset (Vertex L))
    (hdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hE : ∀ i, Transverse (E i) ∧ (E i).card ≤ 5) (a : ℕ) (ha : 0 < a)
    (hleft : ∀ i, (offsets (E i) 0).card = a) (hright : ∀ i, (offsets (E i) 1).card = 1) :
    CoefficientDegreeOneHostCount.Valid 4 (pattern X E) := by
  refine ⟨⟨slice_disjoint E hdisj 0, slice_disjoint E hdisj 1,
    fun i ↦ (hE i).1 0 |>.image _, fun i ↦ (hE i).1 1 |>.image _,
    fun i ↦ target_size (E i) (hE i).1 (hE i).2⟩, a, ha, ?_⟩
  intro i
  exact ⟨by dsimp only [pattern]; rw [integer_offsets_card, hleft],
    by dsimp only [pattern]; rw [integer_offsets_card, hright]⟩

theorem grid_subset {L k : ℕ} (I : Fin k → Finset (Fin (L + 1))) :
    (univ.biUnion fun i ↦ integerOffsets (I i)) ⊆ integerOffsets (univ : Finset (Fin (L + 1))) := by
  intro z hz
  obtain ⟨i, _hi, hzi⟩ := mem_biUnion.mp hz
  obtain ⟨u, _hu, rfl⟩ := mem_image.mp hzi
  exact mem_image.mpr ⟨u, mem_univ _, rfl⟩

theorem pattern_admissible {N L k : ℕ} (hN : 2 ≤ N) (X : Fin 3 → ℕ)
    (hX : ManyPlanarSquareProducts.RegularDirect N L X) (E : Fin k → Finset (Vertex L)) :
    SourceCurvePointCover.Admissible (CoefficientPatternGrids.left (pattern X E))
      (CoefficientPatternGrids.right (pattern X E)) ((X 0 : ℤ), (X 1 : ℤ)) := by
  have hx : 2 ≤ X 0 := hN.trans (mem_Ico.mp (hX.2.1 0).1).1
  have hy : 2 ≤ X 1 := hN.trans (mem_Ico.mp (hX.2.1 1).1).1
  exact SelectedWindowAdmissibility.admissible_mono
    (SelectedWindowAdmissibility.admissible hx hy (hX.2.1 0).2 (hX.2.1 1).2
      (hX.2.2 (by decide)) univ univ) (grid_subset _) (grid_subset _)

theorem pattern_roots {L k : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (E : Fin k → Finset (Vertex L)) :
    ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = CoefficientSplitRadicalPatterns.coefficient (pattern X E) i *
      integerProduct ((pattern X E).1.1 i) (X 0) * integerProduct ((pattern X E).1.2 i) (X 1) := by
  have hs (i : Fin k) : ∃ r : ℤ, r ^ 2 =
      CoefficientSplitRadicalPatterns.coefficient (pattern X E) i *
        integerProduct ((pattern X E).1.1 i) (X 0) * integerProduct ((pattern X E).1.2 i) (X 1) := by
    obtain ⟨r, hr⟩ := SmallMotifCoefficients.square X hX (E i)
    exact ⟨r, by simpa only [pow_two, pattern, CoefficientSplitRadicalPatterns.coefficient] using hr.symm⟩
  choose w hw using hs
  exact ⟨w, hw⟩

end PaperP1.SmallMotifSystems

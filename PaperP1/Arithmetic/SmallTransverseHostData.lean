module

public import PaperP1.Arithmetic.SmallMotifSystems
public import PaperP1.Combinatorics.SmallTransverseSelection
public import PaperP1.Arithmetic.ComponentSixVertexBudget

/-! # Every cover with many small components supplies a literal linear root system

The cover supplies a family and is then forgotten. It is never an index in the
host count. Only a permutation of three centres and the fixed third centre
remain as counting parameters.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallTransverseHostData

open Finset PaperP1.Arithmetic PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes
  PaperP1.SmoothMotifReindex PaperP1.PositiveLineOffsetRoots PaperP1.SplitRadicalPointHeight
  PaperP1.ManyPlanarSquareProducts

def Many (k L H : ℕ) (X : Fin 3 → ℕ) : Prop :=
  ∃ G : Finset (Finset (Vertex L)), (↑G : Set (Finset (Vertex L))).PairwiseDisjoint id ∧
    k ≤ G.card ∧ ∀ E ∈ G, Transverse E ∧ E.card ≤ 5 ∧ SquareOutside H X E

def Oriented (k L H : ℕ) (X : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3)) : Prop :=
  ∃ q ∈ CoefficientSplitRadicalPatterns.pool k L 4 (SmallMotifCoefficients.pool (X (e 2)) L H),
    CoefficientDegreeOneHostCount.Valid 4 q ∧
    SourceCurvePointCover.Admissible (CoefficientPatternGrids.left q) (CoefficientPatternGrids.right q)
      ((X (e 0) : ℤ), (X (e 1) : ℤ)) ∧
    ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = CoefficientSplitRadicalPatterns.coefficient q i *
      integerProduct (q.1.1 i) (X (e 0)) * integerProduct (q.1.2 i) (X (e 1))

theorem regular_reindex {N L : ℕ} (X : Fin 3 → ℕ) (hX : RegularDirect N L X)
    (e : Equiv.Perm (Fin 3)) : RegularDirect N L (X ∘ e) :=
  ⟨hX.1.comp e.injective, fun i ↦ hX.2.1 (e i), fun _ _ hij ↦ hX.2.2 (e.injective.ne hij)⟩

theorem exists_system {N L H k : ℕ} (hN : 2 ≤ N) (hk : 0 < k) (X : Fin 3 → ℕ)
    (hX : RegularDirect N L X) (hmany : Many (24 * k) L H X) :
    ∃ e : Equiv.Perm (Fin 3), Oriented k L H X e := by
  classical
  obtain ⟨G, hdisj, hpop, hdata⟩ := hmany
  obtain ⟨t, F, hFG, hFk, hfit⟩ := SmallTransverseSelection.select G
    (fun E hE ↦ ⟨(hdata E hE).1, (hdata E hE).2.1⟩) k hk hpop
  let f : Fin k ≃ F := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hFk)).symm
  let A : Fin k → Finset (Vertex L) := fun i ↦ (f i).val
  let e := t.1
  let Y := X ∘ e
  let E : Fin k → Finset (Vertex L) := fun i ↦ reindex e (A i)
  have hA (i : Fin k) : A i ∈ G := hFG (f i).property
  have hinj : Function.Injective A := fun _ _ hh ↦ f.injective (Subtype.ext hh)
  have hAdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j)) :=
    fun _ _ hij ↦ hdisj (hA _) (hA _) (hinj.ne hij)
  have hEd := pairwise_disjoint_reindex univ A (fun _ _ _ _ hij ↦ hAdisj hij) e
  have hEdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j)) :=
    fun _ _ hij ↦ hEd (mem_univ _) (mem_univ _) hij
  have hE (i : Fin k) : Transverse (E i) ∧ (E i).card ≤ 5 ∧ SquareOutside H Y (E i) := by
    have hh := hdata (A i) (hA i)
    exact ⟨transverse_reindex e hh.1, by rw [reindex_card]; exact hh.2.1,
      (square_outside_reindex e X (A i)).mpr hh.2.2⟩
  have hleft (i : Fin k) : (offsets (E i) 0).card = t.2.val := (hfit (A i) (f i).property).2.1
  have hright (i : Fin k) : (offsets (E i) 1).card = 1 := (hfit (A i) (f i).property).2.2
  have ha : 0 < t.2.val := (hfit (A ⟨0, hk⟩) (f ⟨0, hk⟩).property).1
  have hY := regular_reindex X hX e
  have hY2 (i : Fin 3) : 2 ≤ Y i := hN.trans (mem_Ico.mp (hY.2.1 i).1).1
  refine ⟨e, SmallMotifSystems.pattern Y E, SmallMotifSystems.pattern_mem Y hY2 E hE,
    SmallMotifSystems.pattern_valid Y E hEdisj (fun i ↦ ⟨(hE i).1, (hE i).2.1⟩)
      t.2.val ha hleft hright,
    SmallMotifSystems.pattern_admissible hN Y hY E, SmallMotifSystems.pattern_roots Y hY2 E⟩

theorem many_of_cover {X : Fin 3 → ℕ} {L H k : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (D : Finset (Vertex L)) (hD : CoverGraphResolution.IsCover (ThreeBlockCoordinates.rows X L H) D)
    (hcount : k ≤ ComponentSixVertexBudget.smallCount X L H D) : Many k L H X := by
  let G := (FullComponentMotifs.family X L H D).filter (fun E ↦ E.card ≤ 5)
  have hsub : G ⊆ FullComponentMotifs.family X L H D := filter_subset _ _
  refine ⟨G, fun E hE F hF hEF ↦ FullComponentMotifs.family_disjoint X L H D (hsub hE) (hsub hF) hEF,
    hcount, ?_⟩
  intro E hE
  have hd := FullComponentMotifs.family_data hX hH D hD E (hsub hE)
  exact ⟨hd.1, (mem_filter.mp hE).2, hd.2⟩

end PaperP1.SmallTransverseHostData

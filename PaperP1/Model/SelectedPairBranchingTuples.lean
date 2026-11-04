module

public import PaperP1.Model.SequentialRetainedWindows
public import PaperP1.Combinatorics.PairPositionEncoding
public import PaperP1.Combinatorics.OrderedSubsetWeights

/-! # Actual selected ordered tuples with their unique dependent source pair

The two source positions, their actual ordered source and every chronological
retained extension are encoded injectively. All masses below are literal sums
over finite sets of distinct original-window tuples.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedPairBranchingTuples

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Probability PaperP1.FiniteFamilyEnumeration PaperP1.SequentialBranchingPaths

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def positions (k : ℕ) : Finset (Finset (Fin (k + 2))) := univ.powersetCard 2

def sources (G : Finset ℕ) (E : Finset (Finset ℕ)) : Finset (OrderedTuple G 2) :=
  OrderedSubsetWeights.population G 2 E

abbrev Code (G : Finset ℕ) (E : Finset (Finset ℕ)) (N L k : ℕ) :=
  ↥(positions k) × (Σ t : sources G E, ↥(SequentialRetainedWindows.paths N L (tupleValues t.val) k))

def encode {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (c : Code G E N L k) : Fin (k + 2) → ℕ :=
  PairPositionEncoding.place c.1.val (mem_powersetCard.mp c.1.property).2
    (fun i ↦ (c.2.1.val i).val) c.2.2.val
    (SequentialBranchingPaths.length _ _ k c.2.2.val c.2.2.property)

def families (G : Finset ℕ) (E : Finset (Finset ℕ)) (N L k : ℕ) : Finset (Fin (k + 2) → ℕ) :=
  univ.image (encode (G := G) (E := E) (N := N) (L := L) (k := k))

def mass (G : Finset ℕ) (E : Finset (Finset ℕ)) (N L k : ℕ) : ℝ :=
  ∑ x ∈ families G E N L k, infiniteJointMoment L (tupleSet x)

theorem source_mem {G : Finset ℕ} {E : Finset (Finset ℕ)} (t : sources G E) : tupleValues t.val ∈ E :=
  (mem_filter.mp t.property).2

theorem encode_support {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (c : Code G E N L k) : tupleSet (encode c) = old (tupleValues c.2.1.val) c.2.2.val :=
  PairPositionEncoding.support _ _ _ _ _

theorem encode_distinct {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (hG : G ⊆ dyadicBlock N) (c : Code G E N L k) : Function.Injective (encode c) := by
  have hdata := SequentialRetainedWindows.data (tupleValues c.2.1.val)
    ((tupleValues_subset _).trans hG) k c.2.2.val c.2.2.property
  exact PairPositionEncoding.injective _ _ _ (Subtype.val_injective.comp c.2.1.val.injective)
    _ _ hdata.2.1 hdata.2.2.1

theorem encode_injective {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (hN : 2 ≤ N) (hG : G ⊆ dyadicBlock N) (hE : ∀ e ∈ E, 0 < runRelativeNullity L e) :
    Function.Injective (encode (G := G) (E := E) (N := N) (L := L) (k := k)) := by
  rintro ⟨P, t, xs⟩ ⟨Q, u, ys⟩ heq
  have huG := (tupleValues_subset u.val).trans hG
  have hsupports := congrArg tupleSet heq
  rw [encode_support, encode_support] at hsupports
  have hsource : tupleValues t.val = tupleValues u.val :=
    SequentialRetainedWindows.unique_dependent_pair hN (tupleValues u.val) (tupleValues_card _) huG
      (hE _ (source_mem u)) k ys.val ys.property (tupleValues t.val)
      ((subset_union_left : tupleValues t.val ⊆ old (tupleValues t.val) xs.val).trans (le_of_eq hsupports))
      (tupleValues_card _) (hE _ (source_mem t))
  have hP := (mem_powersetCard.mp P.property).2
  have hQ := (mem_powersetCard.mp Q.property).2
  have hxlen := SequentialBranchingPaths.length _ _ k xs.val xs.property
  have hylen := SequentialBranchingPaths.length _ _ k ys.val ys.property
  have hword := encode_distinct hG (⟨P, t, xs⟩ : Code G E N L k)
  have hpos := PairPositionEncoding.positions_eq P.val Q.val hP hQ
    (fun i ↦ (t.val i).val) (fun i ↦ (u.val i).val) xs.val ys.val hxlen hylen hword hsource heq
  have hPQ : P = Q := Subtype.ext hpos
  subst Q
  have hsrc := PairPositionEncoding.source_eq P.val hP
    (fun i ↦ (t.val i).val) (fun i ↦ (u.val i).val) xs.val ys.val hxlen hylen heq
  have htu : t = u := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    exact Subtype.ext (congrFun hsrc i)
  subst u
  have hpath := PairPositionEncoding.path_eq P.val hP
    (fun i ↦ (t.val i).val) (fun i ↦ (t.val i).val) xs.val ys.val hxlen hylen heq
  have hxy : xs = ys := Subtype.ext hpath
  subst ys
  rfl

theorem mass_exact {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (hN : 2 ≤ N) (hG : G ⊆ dyadicBlock N) (hE : E ⊆ G.powersetCard 2)
    (hdep : ∀ e ∈ E, 0 < runRelativeNullity L e) :
    mass G E N L k = ((k + 2).choose 2 : ℝ) *
      (2 * ∑ e ∈ E, SequentialRetainedWindows.mass N L e k) := by
  have hsource : (∑ t : sources G E, SequentialRetainedWindows.mass N L (tupleValues t.val) k) =
      2 * ∑ e ∈ E, SequentialRetainedWindows.mass N L e k := by
    have hh := sum_coe_sort (sources G E) (fun t ↦ SequentialRetainedWindows.mass N L (tupleValues t) k)
    exact hh.trans ((OrderedSubsetWeights.weighted_sum G 2 E hE
      (fun e ↦ SequentialRetainedWindows.mass N L e k)).trans (by norm_num))
  unfold mass families
  rw [sum_image (encode_injective hN hG hdep).injOn]
  simp_rw [encode_support]
  calc
    _ = ∑ _P : positions k, ∑ t : sources G E, SequentialRetainedWindows.mass N L (tupleValues t.val) k := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro P _
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro t _
      change (∑ xs : SequentialRetainedWindows.paths N L (tupleValues t.val) k,
        infiniteJointMoment L (old (tupleValues t.val) xs.val)) =
          ∑ xs ∈ SequentialRetainedWindows.paths N L (tupleValues t.val) k,
            infiniteJointMoment L (old (tupleValues t.val) xs)
      exact sum_coe_sort (SequentialRetainedWindows.paths N L (tupleValues t.val) k)
        (fun xs : List ℕ ↦ infiniteJointMoment L (old (tupleValues t.val) xs))
    _ = _ := by
      rw [hsource, sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, positions,
        card_powersetCard, card_univ, Fintype.card_fin]

theorem family_data {G : Finset ℕ} {E : Finset (Finset ℕ)} {N L k : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hG : G ⊆ dyadicBlock N)
    (hE : ∀ e ∈ E, 0 < infiniteJointMoment L e) :
    ∀ x ∈ families G E N L k, Function.Injective x ∧ tupleSet x ⊆ dyadicBlock N ∧
      0 < infiniteJointMoment L (tupleSet x) := by
  intro x hx
  obtain ⟨c, _hc, rfl⟩ := mem_image.mp hx
  have heG := (tupleValues_subset c.2.1.val).trans hG
  have hd := SequentialRetainedWindows.data (tupleValues c.2.1.val) heG k c.2.2.val c.2.2.property
  refine ⟨encode_distinct hG c, ?_, ?_⟩
  · rw [encode_support]
    exact hd.2.2.2
  · rw [encode_support, SequentialRetainedWindows.probability_exact hN hL _ heG k _ c.2.2.property]
    exact mul_pos (pow_pos (by positivity) _) (hE _ (source_mem c.2.1))

end PaperP1.SelectedPairBranchingTuples

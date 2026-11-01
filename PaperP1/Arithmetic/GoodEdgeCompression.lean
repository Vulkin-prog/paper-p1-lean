module

public import PaperP1.Arithmetic.CompressionRank
public import PaperP1.Arithmetic.NormalizedMotifs
public import PaperP1.Model.RegularStarts
public import PaperP1.Model.InfiniteJointMoments

/-! # Article Lemma 3.5 for the actual deterministic leading good-edge family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgeCompression

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

local instance goodEdgePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def PrivateAbove (H : ℝ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, ∃ p : ℕ, Nat.Prime p ∧ H < (p : ℝ) ∧ parityVec n p ≠ 0 ∧
    ∀ m ∈ S, m ≠ n → parityVec m p = 0

def Leading (a b : ℕ) : Prop := (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 4)

def GoodEdge (H : ℝ) (N L x y : ℕ) : Prop :=
  x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ x < y ∧
    0 < infiniteJointMoment L {x, y} ∧ ¬Disjoint (squareClassSpace x L) (squareClassSpace y L) ∧
      ∃ a b : ℕ, Leading a b ∧ PrivateAbove H (union a b x y L)

def goodEdges (H : ℝ) (N L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy ↦ GoodEdge H N L xy.1 xy.2)).image
    (fun xy ↦ ({xy.1, xy.2} : Finset ℕ))

def compressedMap (a b x y L : ℕ) := EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data (union a b x y L))

def Conclusion (a b x y L : ℕ) : Prop :=
  Function.Injective (compressedMap a b x y L) ∧
    LinearMap.range (compressedMap a b x y L) = squareClassSpace x L ⊔ squareClassSpace y L ∧
    Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) = (union a b x y L).card - 1 ∧
    (2 - 1 / (b : ℝ)) * L - 1 ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) : ℝ) ∧
    (NormalizedMotifs.family a b L).card ≤ (L + 1) ^ 2 ∧
      ∃ M ∈ NormalizedMotifs.family a b L, ∃ t : ℤ,
        (union a b x y L).image (fun n : ℕ ↦ (n : ℤ)) = M.image (fun z ↦ t + z) ∧
          ∀ z ∈ M, |z| ≤ (b : ℤ) * L

theorem PrivateAbove.private {H : ℝ} {S : Finset ℕ} (h : PrivateAbove H S) : FiniteEvenSquareClasses.Private S := by
  intro n hn
  obtain ⟨p, _, _, hp, hothers⟩ := h n hn
  exact ⟨p, hp, hothers⟩

theorem leading_properties {a b : ℕ} (h : Leading a b) :
    0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ b ∧ b ≤ 4 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- One normalized coincidence suffices for the complete finite compression. -/
theorem finite_compression {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hle : a ≤ b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hunits : (units a b x y L).Nonempty)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L)) : Conclusion a b x y L := by
  have hinter := CompressionRank.units_intersection_nonempty hunits
  have hfull := FiniteEvenSquareClasses.combination_injective (union a b x y L) hprivate
  refine ⟨EvenImage.evenMap_injective _ hfull, ?_, rank_union ha hb hx hy hinter hprivate,
    CompressionRank.rank_lower_bound ha hb hab hx hy hinter hprivate, NormalizedMotifs.family_card _ _ _, ?_⟩
  · exact space_union ha hb hx hy hinter
  · exact NormalizedMotifs.finite_translation_pattern hle (by omega) (by omega) hunits

theorem goodEdge_regular {H : ℝ} {N L x y : ℕ} (hN : 2 ≤ N) (h : GoodEdge H N L x y) :
    x ∈ RegularStarts.regularStarts N L ∧ y ∈ RegularStarts.regularStarts N L := by
  obtain ⟨hx, hy, _, _, _, a, b, hlead, hprivate⟩ := h
  obtain ⟨ha, hb, _, _, _⟩ := leading_properties hlead
  have hx2 : 2 ≤ x := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hN.trans (mem_Ico.mp hy).1
  have hranks := CompressionRank.private_local_ranks ha hb hx2 hy2 hprivate.private
  exact ⟨RegularStarts.mem_regularStarts.mpr ⟨hx, hranks.1⟩, RegularStarts.mem_regularStarts.mpr ⟨hy, hranks.2⟩⟩

theorem main_3_5 {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (e : Finset ℕ) (he : e ∈ goodEdges H N L) :
    ∃ x y a b : ℕ, e = {x, y} ∧ Leading a b ∧ Conclusion a b x y L := by
  classical
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  have hgood := (mem_filter.mp hxy).2
  obtain ⟨hx, hy, _, _, hdep, a, b, hlead, hprivate⟩ := hgood
  obtain ⟨ha, hb, hab, hle, _⟩ := leading_properties hlead
  have hx2 : 2 ≤ xy.1 := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ xy.2 := hN.trans (mem_Ico.mp hy).1
  have htwo := CompressionRank.dependent_two_units ha hb hx2 hy2 hprivate.private hdep
  refine ⟨xy.1, xy.2, a, b, rfl, hlead, ?_⟩
  exact finite_compression ha hb hab hle hx2 hy2 (card_pos.mp (by omega)) hprivate.private

end PaperP1.GoodEdgeCompression

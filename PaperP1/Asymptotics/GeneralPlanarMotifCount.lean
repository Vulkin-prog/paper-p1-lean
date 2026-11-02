module

public import PaperP1.Asymptotics.OrientedPlanarMotifCount
public import PaperP1.Arithmetic.SmoothMotifReindex
public import PaperP1.Algebra.MixedPlaneNormal
public import PaperP1.Asymptotics.HalfCountSchedule
public import Mathlib.Data.Fintype.Perm

/-! # The complete count for three bounded transverse motifs on arbitrary small integer planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralPlanarMotifCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.TripleCross PaperP1.TransverseMotifs
  PaperP1.SmoothMotifCodes PaperP1.SmoothMotifReindex PaperP1.OrientedPlanarMotifCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def orientedPlanes (F : Finset Plane) (e : Equiv.Perm (Fin 3)) : Finset Plane :=
  (F.filter fun p ↦ 0 < p.1 (e 0) ∧ p.1 (e 1) < 0).image fun p ↦ (p.1 ∘ e, p.2)

def Admissible (F : Finset Plane) (e : Equiv.Perm (Fin 3)) (X : Fin 3 → ℕ) : Prop :=
  ∃ p ∈ F, 0 < p.1 (e 0) ∧ p.1 (e 1) < 0 ∧ dot p.1 (fun j ↦ (X j : ℤ)) = p.2

theorem uniform_count (C : ℝ) (D d k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ F : Finset Plane, F.card ≤ (L + 1) ^ k →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (p.1 j).natAbs ≤ (L + 1) ^ k) ∧ p.2.natAbs ≤ (L + 1) ^ k) →
      ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, (∀ j, X j ∈ dyadicBlock N) ∧
        (∀ j, Function.Injective (evenSquareClassMap (X j) L)) ∧
        Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))) →
      (∀ X ∈ S, ∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2 ∧
        ∃ E : Pattern L, ValidPattern E ∧ ∀ i, (E i).card ≤ d ∧ SquareOutside H X (E i)) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NO, _hNO, ho⟩ := OrientedPlanarMotifCount.uniform_count C D d k (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) k
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 6 (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NO (max NL NA)), by omega, ?_⟩
  intro N hN L H hband hcut F hFcard hF S hS hcover
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlarge : (L + 1) ^ k < N := by
    have hh := hl N (by omega) L hband
    simpa only [one_mul, ← Nat.cast_pow, Nat.cast_lt] using hh
  let U : Equiv.Perm (Fin 3) → Finset (Fin 3 → ℕ) := fun e ↦ S.filter (Admissible F e)
  have hpoint (e : Equiv.Perm (Fin 3)) : ((U e).card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 2) := by
    let T := (U e).image (fun X : Fin 3 → ℕ ↦ X ∘ e)
    have hFecard : (orientedPlanes F e).card ≤ (L + 1) ^ k :=
      card_image_le.trans ((card_le_card (filter_subset _ _)).trans hFcard)
    have hFe : ∀ p ∈ orientedPlanes F e, 0 < p.1 0 ∧ p.1 1 < 0 ∧
        (p.1 0).natAbs ≤ (L + 1) ^ k ∧ (p.1 1).natAbs ≤ (L + 1) ^ k := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨hqF, hpos, hneg⟩ := mem_filter.mp hq
      exact ⟨hpos, hneg, (hF q hqF).2.1 (e 0), (hF q hqF).2.1 (e 1)⟩
    have hTregular : ∀ Y ∈ T, (∀ j, Y j ∈ dyadicBlock N) ∧
        Function.Injective (evenSquareClassMap (Y 0) L) ∧
        Disjoint (squareClassSpace (Y 0) L) (squareClassSpace (Y 1) L) := by
      intro Y hY
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hY
      have hr := hS X (mem_filter.mp hX).1
      have hne : e 0 ≠ e 1 := fun hh ↦ (by decide : (0 : Fin 3) ≠ 1) (e.injective hh)
      exact ⟨fun j ↦ hr.1 (e j), hr.2.1 (e 0), hr.2.2 hne⟩
    have hTcover : ∀ Y ∈ T, ∃ p ∈ orientedPlanes F e, dot p.1 (fun j ↦ (Y j : ℤ)) = p.2 ∧
        ∃ E : Pattern L, ValidPattern E ∧ ∀ i, (E i).card ≤ d ∧ SquareOutside H Y (E i) := by
      intro Y hY
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hY
      obtain ⟨q, hqF, hpos, hneg, hplane⟩ := (mem_filter.mp hX).2
      obtain ⟨_q₀, _hq₀, _hplane₀, E, hvalid, hE⟩ := hcover X (mem_filter.mp hX).1
      refine ⟨(q.1 ∘ e, q.2), mem_image.mpr ⟨q, mem_filter.mpr ⟨hqF, hpos, hneg⟩, rfl⟩, ?_,
        (fun i ↦ reindex e (E i)), ?_, ?_⟩
      · simpa only [Function.comp_def] using
          (MixedPlaneNormal.dot_permutation q.1 (fun j ↦ (X j : ℤ)) e).trans hplane
      · exact ⟨pairwise_disjoint_reindex univ E hvalid.1 e, fun i ↦ transverse_reindex e (hvalid.2 i)⟩
      · intro i
        exact ⟨by rw [reindex_card]; exact (hE i).1, (square_outside_reindex e X (E i)).mpr (hE i).2⟩
    have hcount := ho N (by omega) L H hband hcut (orientedPlanes F e) hFecard hFe T hTregular hTcover
    simpa only [T, card_image_of_injective _ (centres_injective e)] using hcount
  have hsub : S ⊆ (univ : Finset (Equiv.Perm (Fin 3))).biUnion U := by
    intro X hX
    obtain ⟨p, hp, hplane, _E, _hvalid, _hE⟩ := hcover X hX
    have hXlow : ∀ j, (N : ℤ) ≤ (X j : ℤ) := fun j ↦ by
      exact_mod_cast (mem_Ico.mp ((hS X hX).1 j)).1
    have hsmall : p.2.natAbs < N := (hF p hp).2.2.trans_lt hlarge
    obtain ⟨e, hpos, hneg⟩ := MixedPlaneNormal.positive_permutation N p.1
      (fun j ↦ (X j : ℤ)) p.2 (hF p hp).1 hXlow hplane hsmall
    exact mem_biUnion.mpr ⟨e, mem_univ _, mem_filter.mpr ⟨hX, p, hp, hpos, hneg, hplane⟩⟩
  have hcard : (S.card : ℝ) ≤ ∑ e : Equiv.Perm (Fin 3), ((U e).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hperms : (univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
    simp only [card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_num
  calc
    _ ≤ ∑ e : Equiv.Perm (Fin 3), ((U e).card : ℝ) := hcard
    _ ≤ ∑ _e : Equiv.Perm (Fin 3), (N : ℝ) ^ (1 + ε / 2) := sum_le_sum (fun e _ ↦ hpoint e)
    _ = 6 * (N : ℝ) ^ (1 + ε / 2) := by rw [sum_const, nsmul_eq_mul, hperms, Nat.cast_ofNat]
    _ ≤ (N : ℝ) ^ ((1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.GeneralPlanarMotifCount

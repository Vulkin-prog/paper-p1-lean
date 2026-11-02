module

public import PaperP1.Asymptotics.FixedPlaneSplitCount
public import PaperP1.Asymptotics.CriticalMotifBudget
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Algebra.TripleCross

/-! # Aggregate all bounded motifs and small-prime codes on a polynomial family of oriented planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrientedPlanarMotifCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.TripleCross PaperP1.TransverseMotifs
  PaperP1.SmoothMotifCodes PaperP1.CriticalMotifBudget

local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Plane := (Fin 3 → ℤ) × ℤ
abbrev Pattern (L : ℕ) := Fin 3 → Finset (Vertex L)
abbrev Code := Fin 3 → Finset ℕ
abbrev Parameter (L : ℕ) := (Plane × Pattern L) × Code

def ValidPattern {L : ℕ} (E : Pattern L) : Prop :=
  (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint E ∧ ∀ i, Transverse (E i)

def parameters (F : Finset Plane) (L d H : ℕ) : Finset (Parameter L) :=
  (F ×ˢ motifPatterns L d) ×ˢ codePatterns H

def Matches {L : ℕ} (p : Parameter L) (X : Fin 3 → ℕ) : Prop :=
  dot p.1.1.1 (fun j ↦ (X j : ℤ)) = p.1.1.2 ∧ ValidPattern p.1.2 ∧
    ∀ i, code X (p.1.2 i) = p.2 i

theorem uniform_count (C : ℝ) (D d k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ F : Finset Plane, F.card ≤ (L + 1) ^ k →
      (∀ p ∈ F, 0 < p.1 0 ∧ p.1 1 < 0 ∧ (p.1 0).natAbs ≤ (L + 1) ^ k ∧
        (p.1 1).natAbs ≤ (L + 1) ^ k) →
      ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, (∀ j, X j ∈ dyadicBlock N) ∧
        Function.Injective (evenSquareClassMap (X 0) L) ∧
        Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L)) →
      (∀ X ∈ S, ∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2 ∧
        ∃ E : Pattern L, ValidPattern E ∧ ∀ i, (E i).card ≤ d ∧ SquareOutside H X (E i)) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NF, _hNF, hf⟩ := FixedPlaneSplitCount.uniform_count d (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := parameter_budget (α := Plane) C D d k (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) k
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 10 (max NF (max NB (max NL NG))), by omega, ?_⟩
  intro N hN L H hband hcut F hFcard hF S hS hcover
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : L + 1 ≤ N + 1 := by have hh := (hg N (by omega) L hband).2.2.2.1; omega
  have hlarge : (L + 1) ^ k < N := by
    have hh := hl N (by omega) L hband
    simpa only [one_mul, ← Nat.cast_pow, Nat.cast_lt] using hh
  let T := parameters F L d H
  let Z : Parameter L → Finset (Fin 3 → ℕ) := fun p ↦ S.filter (Matches p)
  have hT : (T.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := hb N (by omega) L H hband hcut F hFcard
  have hpoint (p : Parameter L) (hp : p ∈ T) : ((Z p).card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 2) := by
    obtain ⟨hpFM, hpU⟩ := mem_product.mp hp
    obtain ⟨hpF, hpE⟩ := mem_product.mp hpFM
    have hEmem : ∀ i, p.1.2 i ∈ pool L d := Fintype.mem_piFinset.mp hpE
    have hUmem : ∀ i, p.2 i ∈ codePool H := Fintype.mem_piFinset.mp hpU
    by_cases hnon : (Z p).Nonempty
    · obtain ⟨X₀, hX₀⟩ := hnon
      have hvalid : ValidPattern p.1.2 := (mem_filter.mp hX₀).2.2.1
      have hP := offsets_pairwise_disjoint univ p.1.2 hvalid.1 0
      have hQ := offsets_pairwise_disjoint univ p.1.2 hvalid.1 1
      have hPQ (i : Fin 3) : (offsets (p.1.2 i) 0).Nonempty ∧ (offsets (p.1.2 i) 1).Nonempty ∧
          (offsets (p.1.2 i) 0).card + (offsets (p.1.2 i) 1).card ≤ d :=
        ⟨hvalid.2 i 0, hvalid.2 i 1,
          (first_two_card_le (p.1.2 i)).trans ((mem_pool L d (p.1.2 i)).mp (hEmem i))⟩
      let a := (p.1.1.1 0).natAbs
      let b := (p.1.1.1 1).natAbs
      have hdata := hF p.1.1 hpF
      have ha : 0 < a := Int.natAbs_pos.mpr hdata.1.ne'
      have hb' : 0 < b := Int.natAbs_pos.mpr hdata.2.1.ne
      have haN : a ≤ N := hdata.2.2.1.trans hlarge.le
      have hbN : b ≤ N := hdata.2.2.2.trans hlarge.le
      have haInt : (a : ℤ) = p.1.1.1 0 := by
        dsimp only [a]
        rw [← Int.abs_eq_natAbs, abs_of_pos hdata.1]
      have hbInt : (b : ℤ) = -p.1.1.1 1 := by
        dsimp only [b]
        rw [← Int.abs_eq_natAbs, abs_of_neg hdata.2.1]
      have hcoeff (i : Fin 3) : (((p.2 i).prod id : ℕ) : ℤ) ≠ 0 := by
        exact_mod_cast (pool_coefficient_pos (hUmem i)).ne'
      apply hf N (by omega) L a b hLN ha hb' haN hbN (p.1.1.1 2) p.1.1.2
        (fun i ↦ offsets (p.1.2 i) 0) (fun i ↦ offsets (p.1.2 i) 1)
        (fun i ↦ offsets (p.1.2 i) 2) hP hQ hPQ (fun i ↦ (((p.2 i).prod id : ℕ) : ℤ)) hcoeff (Z p)
      intro X hX
      obtain ⟨hXS, hmatch⟩ := mem_filter.mp hX
      have hregular := hS X hXS
      have hline : (b : ℤ) * X 1 = (a : ℤ) * X 0 + p.1.1.1 2 * X 2 - p.1.1.2 := by
        have he := hmatch.1
        change p.1.1.1 0 * X 0 + p.1.1.1 1 * X 1 + p.1.1.1 2 * X 2 = p.1.1.2 at he
        rw [haInt, hbInt]
        linarith only [he]
      refine ⟨hregular.1, hregular.2.1, hregular.2.2, hline, ?_⟩
      intro i
      have hXpos (j : Fin 3) : 2 ≤ X j := by
        have hh := (mem_Ico.mp (hregular.1 j)).1
        omega
      have hsq := square_prescription X hXpos (p.1.2 i)
      have hcoef := congrArg (fun U : Finset ℕ ↦ U.prod id) (hmatch.2.2 i)
      change coefficient X (p.1.2 i) = (p.2 i).prod id at hcoef
      rw [hcoef] at hsq
      exact hsq
    · rw [not_nonempty_iff_eq_empty.mp hnon, card_empty, Nat.cast_zero]
      exact Real.rpow_nonneg hn.le _
  have hsub : S ⊆ T.biUnion Z := by
    intro X hX
    obtain ⟨p, hp, hplane, E, hvalid, hE⟩ := hcover X hX
    let U : Code := fun i ↦ code X (E i)
    have hEmem : E ∈ motifPatterns L d := Fintype.mem_piFinset.mpr
      (fun i ↦ (mem_pool L d (E i)).mpr (hE i).1)
    have hUmem : U ∈ codePatterns H := Fintype.mem_piFinset.mpr
      (fun i ↦ code_mem_pool X (E i) (hE i).2)
    apply mem_biUnion.mpr
    refine ⟨((p, E), U), mem_product.mpr ⟨mem_product.mpr ⟨hp, hEmem⟩, hUmem⟩, ?_⟩
    exact mem_filter.mpr ⟨hX, hplane, hvalid, fun _ ↦ rfl⟩
  have hcount : (S.card : ℝ) ≤ ∑ p ∈ T, ((Z p).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_biUnion_le)
  calc
    _ ≤ ∑ p ∈ T, ((Z p).card : ℝ) := hcount
    _ ≤ ∑ _p ∈ T, (N : ℝ) ^ (1 + ε / 2) := sum_le_sum hpoint
    _ = T.card * (N : ℝ) ^ (1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) :=
      mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.OrientedPlanarMotifCount

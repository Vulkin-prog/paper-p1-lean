module

public import PaperP1.Asymptotics.ThreeLineSplitCount
public import PaperP1.Arithmetic.SaturationPrimes

/-! # A fixed plane and three fixed transverse motifs have at most N^(1+epsilon) hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPlaneSplitCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PositiveLineOffsetRoots PaperP1.LinearKernelFibres

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem offset_bounds {N L x : ℕ} (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1)
    (hx : x ∈ dyadicBlock N) (u : Fin (L + 1)) :
    0 < (x : ℤ) + integerOffset u ∧ value x (integerOffset u) ≤ 3 * N := by
  have hv := SaturationPrimes.value_bounds hN hLN hx u
  have hxl := (mem_Ico.mp hx).1
  have heq : (x : ℤ) + integerOffset u = (SaturationPrimes.value x u : ℤ) := by
    unfold integerOffset SaturationPrimes.value
    omega
  constructor
  · rw [heq]
    exact_mod_cast hv.1
  · unfold value
    rw [heq, Int.natAbs_natCast]
    exact hv.2

theorem scaled_offset_bounds {N L x a : ℕ} (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1)
    (hx : x ∈ dyadicBlock N) (ha : a ≤ N) (u : Fin (L + 1)) :
    0 < (x : ℤ) + integerOffset u ∧ a * value x (integerOffset u) ≤ N ^ 3 := by
  have hv := offset_bounds hN hLN hx u
  refine ⟨hv.1, ?_⟩
  calc
    _ ≤ N * (3 * N) := Nat.mul_le_mul ha hv.2
    _ ≤ N * N ^ 2 := Nat.mul_le_mul_left N (by nlinarith : 3 * N ≤ N ^ 2)
    _ = _ := by ring

def pairFibre (S : Finset (Fin 3 → ℕ)) (z : ℕ) : Finset (ℕ × ℕ) :=
  (S.filter fun X ↦ X 2 = z).image fun X ↦ (X 0, X 1)

theorem pairFibre_card (S : Finset (Fin 3 → ℕ)) (z : ℕ) :
    (pairFibre S z).card = (S.filter fun X ↦ X 2 = z).card := by
  apply card_image_of_injOn
  intro X hX Y hY hh
  have h0 := congrArg Prod.fst hh
  have h1 := congrArg Prod.snd hh
  have h2 := (mem_filter.mp hX).2.trans (mem_filter.mp hY).2.symm
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem uniform_count (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L a b : ℕ, L + 1 ≤ N + 1 →
      0 < a → 0 < b → a ≤ N → b ≤ N → ∀ g h : ℤ,
      ∀ P Q R : Fin 3 → Finset (Fin (L + 1)),
      (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint P →
      (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint Q →
      (∀ i, (P i).Nonempty ∧ (Q i).Nonempty ∧ (P i).card + (Q i).card ≤ d) →
      ∀ D : Fin 3 → ℤ, (∀ i, D i ≠ 0) → ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, (∀ j, X j ∈ dyadicBlock N) ∧
        Function.Injective (evenSquareClassMap (X 0) L) ∧
        Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L) ∧
        (b : ℤ) * X 1 = (a : ℤ) * X 0 + g * X 2 - h ∧
        ∀ i : Fin 3, IsSquare (D i *
          ((∏ u ∈ P i, ((X 0 : ℤ) + integerOffset u)) *
           (∏ v ∈ Q i, ((X 1 : ℤ) + integerOffset v)) *
           (∏ w ∈ R i, ((X 2 : ℤ) + integerOffset w))))) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨NF, _hNF, hf⟩ := ThreeLineSplitCount.uniform_count 3 d ε hε
  refine ⟨max 10 NF, by omega, ?_⟩
  intro N hN L a b hLN ha hb haN hbN g h P Q R hP hQ hPQ D hD S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hslice (z : ℕ) (hz : z ∈ dyadicBlock N) : ((pairFibre S z).card : ℝ) ≤ (N : ℝ) ^ ε := by
    by_cases hnon : (S.filter fun X ↦ X 2 = z).Nonempty
    · obtain ⟨X₀, hX₀⟩ := hnon
      have hX₀S := (mem_filter.mp hX₀).1
      have hX₀z := (mem_filter.mp hX₀).2
      let D' : Fin 3 → ℤ := fun i ↦ D i * ∏ w ∈ R i, ((z : ℤ) + integerOffset w)
      have hD' (i : Fin 3) : D' i ≠ 0 := mul_ne_zero (hD i)
        (Finset.prod_pos (fun w _ ↦ (offset_bounds (by omega : 10 ≤ N) hLN hz w).1)).ne'
      have hx₀ : 2 ≤ X₀ 0 := by have hh := (mem_Ico.mp ((hS X₀ hX₀S).1 0)).1; omega
      have hy₀ : 2 ≤ X₀ 1 := by have hh := (mem_Ico.mp ((hS X₀ hX₀S).1 1)).1; omega
      have hline₀ : (b : ℤ) * X₀ 1 = (a : ℤ) * X₀ 0 + (g * z - h) := by
        have hh := (hS X₀ hX₀S).2.2.2.1
        rw [hX₀z] at hh
        linarith only [hh]
      apply hf N (by omega) L a b ha hb (g * z - h) (X₀ 0) (X₀ 1) hx₀ hy₀
        (hS X₀ hX₀S).2.1 (hS X₀ hX₀S).2.2.1 hline₀ P Q hP hQ hPQ D' hD' (pairFibre S z)
      intro xy hxy
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hxy
      have hXS := (mem_filter.mp hX).1
      have hXz := (mem_filter.mp hX).2
      refine ⟨?_, ?_⟩
      · have hh := (hS X hXS).2.2.2.1
        rw [hXz] at hh
        linarith only [hh]
      · intro i
        refine ⟨fun u _ ↦ scaled_offset_bounds (by omega : 10 ≤ N) hLN ((hS X hXS).1 0) haN u,
          fun v _ ↦ scaled_offset_bounds (by omega : 10 ≤ N) hLN ((hS X hXS).1 1) hbN v, ?_⟩
        have hsq := (hS X hXS).2.2.2.2 i
        dsimp only [D']
        rw [← hXz]
        convert hsq using 1
        ring
    · rw [pairFibre, not_nonempty_iff_eq_empty.mp hnon, image_empty, card_empty, Nat.cast_zero]
      exact Real.rpow_nonneg hn.le _
  have hcardNat : S.card = ∑ z ∈ dyadicBlock N, (pairFibre S z).card := by
    calc
      _ = ∑ z ∈ dyadicBlock N, (S.filter fun X ↦ X 2 = z).card :=
        card_eq_sum_card_fiberwise (fun X hX ↦ (hS X hX).1 2)
      _ = _ := sum_congr rfl (fun z _ ↦ (pairFibre_card S z).symm)
  calc
    _ = ∑ z ∈ dyadicBlock N, ((pairFibre S z).card : ℝ) := by exact_mod_cast hcardNat
    _ ≤ ∑ _z ∈ dyadicBlock N, (N : ℝ) ^ ε := sum_le_sum hslice
    _ = N * (N : ℝ) ^ ε := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]
    _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]

end PaperP1.FixedPlaneSplitCount

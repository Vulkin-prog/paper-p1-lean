module

public import PaperP1.Asymptotics.TernaryWeakCritical
public import PaperP1.Asymptotics.TernaryStrongCritical

/-! # Actual arithmetic hypotheses and the complete three-group budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryBudgetDomain

open Finset PaperP1.TernaryTopProducts PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

structure Admissible (N L R D : ℕ) (base : Fin 3 → ℕ)
    (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ) (X : Fin 3 → ℕ) : Prop where
  box : ∀ i, X i ∈ Ico (base i) (base i + D * N)
  cutoff : 1 ≤ H X ∧ H X ≤ D * (L + 1)
  diameter : ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X
  values : ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ D * N ∧ ((n : ℤ) - X i).natAbs ≤ R
  injective : ∀ i, Function.Injective (data (U X i))
  disjoint : Pairwise (fun i j ↦ Disjoint (space (U X i)) (space (U X j)))

theorem three_group_bound (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (∀ X ∈ F, Admissible N L R D base U H X) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) 3 : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  let δ := ε / 2
  obtain ⟨NW, _hNW, hw⟩ := TernaryWeakCritical.uniform_bound C D 3 δ (by dsimp [δ]; positivity)
  obtain ⟨NS, _hNS, hs⟩ := TernaryStrongCritical.uniform_bound C D δ (by dsimp [δ]; positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 0 δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NW (max NS NF)), by omega, ?_⟩
  intro N hN L R hband hR F U H base T hT hadm hprod
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let weak := F.filter fun X ↦ (topProduct (U X) (H X) 3 : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ)
  let strong := F.filter fun X ↦ (N : ℝ) ^ (6 / 5 : ℝ) < (topProduct (U X) (H X) 3 : ℝ)
  have hwF : weak ⊆ F := filter_subset _ _
  have hsF : strong ⊆ F := filter_subset _ _
  have hweak := hw N (by omega) L R hband hR weak U H base T ((N : ℝ) ^ (6 / 5 : ℝ))
    hT (Real.rpow_nonneg hn.le _) (fun X hX ↦ (hadm X (hwF hX)).box)
    (fun X hX ↦ (hadm X (hwF hX)).diameter) (fun X hX ↦ (hadm X (hwF hX)).values)
    (fun X hX ↦ ⟨hprod X (hwF hX), (mem_filter.mp hX).2⟩)
  have hstrong := hs N (by omega) L R hband hR strong U H base
    (fun X hX ↦ (hadm X (hsF hX)).box) (fun X hX ↦ (hadm X (hsF hX)).cutoff)
    (fun X hX ↦ (hadm X (hsF hX)).diameter) (fun X hX ↦ (hadm X (hsF hX)).values)
    (fun X hX ↦ (hadm X (hsF hX)).injective) (fun X hX ↦ (hadm X (hsF hX)).disjoint)
    (fun _ hX ↦ (mem_filter.mp hX).2)
  have hcover : F ⊆ weak ∪ strong := by
    intro X hX
    rcases le_or_gt (topProduct (U X) (H X) 3 : ℝ) ((N : ℝ) ^ (6 / 5 : ℝ)) with hw | hs
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hX, hw⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hX, hs⟩))
  have hcard : (F.card : ℝ) ≤ weak.card + strong.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le weak strong)
  let B : ℝ := (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hstrong' : (strong.card : ℝ) ≤ (N : ℝ) ^ δ * B := by
    calc
      _ ≤ (N : ℝ) ^ (6 / 5 + δ) := hstrong
      _ = (N : ℝ) ^ δ * (N : ℝ) ^ (6 / 5 : ℝ) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [B]; exact le_add_of_nonneg_left (by positivity)) (by positivity)
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ δ := by simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  calc
    _ ≤ 2 * (N : ℝ) ^ δ * B := by nlinarith [hcard, hweak, hstrong']
    _ ≤ ((N : ℝ) ^ δ * (N : ℝ) ^ δ) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo (by positivity)) hB
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; dsimp [δ]; ring

end PaperP1.TernaryBudgetDomain

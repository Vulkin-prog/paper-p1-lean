module

public import PaperP1.Asymptotics.TernaryPrimeWeakCritical
public import PaperP1.Asymptotics.TernaryBudgetDomain
public import PaperP1.Arithmetic.TernaryTopProductDrop

/-! # The complete fixed-k budget for individual ternary primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeBudget

open Finset PaperP1.TernaryPrimeTopProducts PaperP1.TernaryBudgetDomain

theorem three_prime_tail (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ),
      (∀ X ∈ F, Admissible N L R D base U H X) →
      (∀ X ∈ F, (N : ℝ) ^ (6 / 5 : ℝ) < (topProduct (U X) (H X) 3 : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨NS, _hNS, hs⟩ := TernaryStrongCritical.uniform_bound C D ε hε
  obtain ⟨NF, _hNF, hf⟩ := TernaryGroupScales.forcing_scale C D
  refine ⟨max 2 (max NS NF), by omega, ?_⟩
  intro N hN L R hband hR F U H base hadm hlarge
  apply hs N (by omega) L R hband hR F U H base
    (fun X hX ↦ (hadm X hX).box) (fun X hX ↦ (hadm X hX).cutoff)
    (fun X hX ↦ (hadm X hX).diameter) (fun X hX ↦ (hadm X hX).values)
    (fun X hX ↦ (hadm X hX).injective) (fun X hX ↦ (hadm X hX).disjoint)
  intro X hX
  have hcut := (hf N (by omega) L (H X) hband (hadm X hX).cutoff.2).1
  have hH := (hadm X hX).cutoff.1
  have hsmall : 2 * (D * N) * (H X + 1) ≤ 6 * (D * N) * H X ^ 2 := by
    have hb : 2 * (H X + 1) ≤ 6 * H X ^ 2 := by nlinarith [hH]
    have hm := Nat.mul_le_mul_left (D * N) hb
    nlinarith only [hm]
  have hprimeLarge : 2 * (D * N) * (H X + 1) < topProduct (U X) (H X) 3 := by
    have hsreal : ((2 * (D * N) * (H X + 1) : ℕ) : ℝ) ≤ ((6 * (D * N) * H X ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsmall
    exact_mod_cast (hsreal.trans_lt hcut).trans (hlarge X hX)
  have hbridge := large_three_le_groups (hadm X hX).diameter
    (fun i n hn ↦ ((hadm X hX).values i n hn).1)
    (fun i n hn ↦ ((hadm X hX).values i n hn).2.1)
    (hadm X hX).injective (hadm X hX).disjoint hprimeLarge
  exact (hlarge X hX).trans_le (by exact_mod_cast hbridge)

theorem three_prime_bound (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (∀ X ∈ F, Admissible N L R D base U H X) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) 3 : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  let δ := ε / 2
  obtain ⟨NW, _hNW, hw⟩ := TernaryPrimeWeakCritical.uniform_bound C D 3 δ (by dsimp [δ]; positivity)
  obtain ⟨NS, _hNS, hs⟩ := three_prime_tail C D δ (by dsimp [δ]; positivity)
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
    (fun X hX ↦ (hadm X (hwF hX)).values)
    (fun X hX ↦ ⟨hprod X (hwF hX), (mem_filter.mp hX).2⟩)
  have hstrong := hs N (by omega) L R hband hR strong U H base
    (fun X hX ↦ hadm X (hsF hX)) (fun _ hX ↦ (mem_filter.mp hX).2)
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

theorem uniform_bound (C : ℝ) (D : ℕ) : ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (∀ X ∈ F, Admissible N L R D base U H X) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk ε hε
    by_cases hk3 : k = 3
    · subst k
      exact three_prime_bound C D ε hε
    have hk4 : 4 ≤ k := by omega
    let δ := ε / 2
    obtain ⟨NW, _hNW, hw⟩ := TernaryPrimeWeakCritical.uniform_bound C D k δ (by dsimp [δ]; positivity)
    obtain ⟨NI, _hNI, hi⟩ := ih (k - 1) (by omega) (by omega) δ (by dsimp [δ]; positivity)
    obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 0 δ (by dsimp [δ]; positivity)
    refine ⟨max 2 (max NW (max NI NF)), by omega, ?_⟩
    intro N hN L R hband hR F U H base T hT hadm hprod
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    let weak := F.filter fun X ↦ (topProduct (U X) (H X) k : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ)
    let strong := F.filter fun X ↦ (N : ℝ) ^ (6 / 5 : ℝ) < (topProduct (U X) (H X) k : ℝ)
    have hwF : weak ⊆ F := filter_subset _ _
    have hsF : strong ⊆ F := filter_subset _ _
    have hweak := hw N (by omega) L R hband hR weak U H base T ((N : ℝ) ^ (6 / 5 : ℝ))
      hT (Real.rpow_nonneg hn.le _) (fun X hX ↦ (hadm X (hwF hX)).box)
      (fun X hX ↦ (hadm X (hwF hX)).values)
      (fun X hX ↦ ⟨hprod X (hwF hX), (mem_filter.mp hX).2⟩)
    have hprevious : ∀ X ∈ strong, (N : ℝ) ^ (9 / 10 : ℝ) < (topProduct (U X) (H X) (k - 1) : ℝ) := by
      intro X hX
      have hdrop := FiniteFactorTopProducts.threshold_drop (TernaryIndividualPrimes.pool (U X) (H X)) k N
        (6 / 5) (by omega) (mem_filter.mp hX).2
      have hexp : (6 / 5 : ℝ) * (k - 1 : ℕ) / k = TernaryTopProductDrop.thresholdExponent k := by
        unfold TernaryTopProductDrop.thresholdExponent
        ring
      rw [hexp] at hdrop
      exact (Real.rpow_le_rpow_of_exponent_le hn1 (TernaryTopProductDrop.thresholdExponent_ge k hk4)).trans_lt hdrop
    have hstrong := hi N (by omega) L R hband hR strong U H base ((N : ℝ) ^ (9 / 10 : ℝ))
      (Real.one_le_rpow hn1 (by norm_num)) (fun X hX ↦ hadm X (hsF hX)) hprevious
    have hpower : (N : ℝ) ^ 3 * ((N : ℝ) ^ (9 / 10 : ℝ)) ^ (-2 : ℝ) = (N : ℝ) ^ (6 / 5 : ℝ) := by
      rw [← Real.rpow_mul hn.le, ← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hn]
      congr 1
      norm_num
    rw [hpower] at hstrong
    have hcover : F ⊆ weak ∪ strong := by
      intro X hX
      rcases le_or_gt (topProduct (U X) (H X) k : ℝ) ((N : ℝ) ^ (6 / 5 : ℝ)) with hw | hs
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hX, hw⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hX, hs⟩))
    have hcard : (F.card : ℝ) ≤ weak.card + strong.card := by
      exact_mod_cast (card_le_card hcover).trans (card_union_le weak strong)
    let B : ℝ := (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hstrong' : (strong.card : ℝ) ≤ 2 * (N : ℝ) ^ δ * B := by
      have hb : (N : ℝ) ^ (6 / 5 : ℝ) ≤ B := by dsimp [B]; exact le_add_of_nonneg_left (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (N : ℝ) ^ δ)]
    have hthree : (3 : ℝ) ≤ (N : ℝ) ^ δ := by
      simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
    calc
      _ ≤ 3 * (N : ℝ) ^ δ * B := by nlinarith [hcard, hweak, hstrong']
      _ ≤ ((N : ℝ) ^ δ * (N : ℝ) ^ δ) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hthree (by positivity)) hB
      _ = _ := by rw [← Real.rpow_add hn]; congr 2; dsimp [δ]; ring

end PaperP1.TernaryPrimeBudget

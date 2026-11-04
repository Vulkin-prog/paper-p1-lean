module

public import PaperP1.Asymptotics.PolynomialSplitKernelCount
public import PaperP1.Asymptotics.CriticalGeneralRootPatterns
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Combinatorics.FiniteCoverCount
public import PaperP1.Arithmetic.SplitRadicalPointHeight

/-! # A fixed source and one bounded component with two target vertices give subpower partners

The single-variable theorem has arbitrary nonzero coefficients. Actual smooth
codes and bounded offset patterns are counted separately, before all partners.
No surface-cover or curve-count input is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPartnerPatternCount

open Finset PaperP1.Model PaperP1.GeneralSplitRadicalPatternPool PaperP1.SplitRadicalPointHeight

theorem window_value_bound {N B y : ℕ} (hN : 3 ≤ N) (hB : B < N)
    (hy : y ∈ dyadicBlock N) (a : ℤ) (ha : a.natAbs ≤ B) :
    0 < (y : ℤ) + a ∧ LinearKernelFibres.value y a ≤ N ^ 2 := by
  have hylo : (N : ℤ) ≤ y := by exact_mod_cast (mem_Ico.mp hy).1
  have hyhi : (y : ℤ) < 2 * (N : ℤ) := by exact_mod_cast (mem_Ico.mp hy).2
  have hBZ : (B : ℤ) < N := by exact_mod_cast hB
  have habs : |a| ≤ (B : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hpos : 0 < (y : ℤ) + a := by have hh := abs_le.mp habs; omega
  have hcap : (y : ℤ) + a ≤ ((3 * N : ℕ) : ℤ) := by have hh := abs_le.mp habs; omega
  have hnat : 3 * N ≤ N ^ 2 := by nlinarith only [hN]
  have he : (LinearKernelFibres.value y a : ℤ) = (y : ℤ) + a := by
    change (((y : ℤ) + a).natAbs : ℤ) = _
    rw [Int.natCast_natAbs, abs_of_pos hpos]
  refine ⟨hpos, ?_⟩
  have hh : (LinearKernelFibres.value y a : ℤ) ≤ ((N ^ 2 : ℕ) : ℤ) := by
    rw [he]
    exact hcap.trans (by exact_mod_cast hnat)
  exact_mod_cast hh

theorem fixed_system (C : ℝ) (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      ∀ I J : Finset ℤ, (∀ a ∈ I, a.natAbs ≤ L + 1) →
        2 ≤ J.card → J.card ≤ K → (∀ a ∈ J, a.natAbs ≤ L + 1) →
      ∀ c : ℤ, c ≠ 0 → ∀ S : Finset ℕ, (∀ y ∈ S, y ∈ dyadicBlock N) →
        (∀ y ∈ S, IsSquare (c * integerProduct I (x : ℤ) * integerProduct J (y : ℤ))) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NS, _hNS, hs⟩ := PolynomialSplitKernelCount.single_square_equation 2 K ε hε
  obtain ⟨NB, hb⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) 1
  refine ⟨3 + NS + NB, by omega, ?_⟩
  intro N hN L hband x hx I J hI hJlo hJhi hJ c hc S hS hroots
  have hBN : L + 1 < N := by
    have hh := hb N (by omega) L hband
    have hBR : (((L + 1 : ℕ) : ℝ)) < (N : ℝ) := by simpa only [pow_one, one_mul] using hh
    exact_mod_cast hBR
  have hprod : 0 < integerProduct I (x : ℤ) :=
    prod_pos (fun a ha ↦ (window_value_bound (by omega) hBN hx a (hI a ha)).1)
  apply hs N (by omega) J hJlo hJhi (c * integerProduct I (x : ℤ)) (mul_ne_zero hc hprod.ne') S
  intro y hy
  exact ⟨fun a ha ↦ window_value_bound (by omega) hBN (hS y hy) a (hJ a ha), hroots y hy⟩

theorem uniform_count (C : ℝ) (D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ x ∈ dyadicBlock N, ∀ S : Finset ℕ, (∀ y ∈ S, y ∈ dyadicBlock N) →
      (∀ y ∈ S, ∃ q ∈ pool 1 L H K, 2 ≤ (q.1.2 0).card ∧
        IsSquare (coefficient q 0 * integerProduct (q.1.1 0) (x : ℤ) *
          integerProduct (q.1.2 0) (y : ℤ))) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NP, hp⟩ := CriticalGeneralRootPatterns.uniform_pool C (ε / 2) D 1 K (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := PolynomialSplitKernelCount.single_square_equation 2 K (ε / 2) (by positivity)
  obtain ⟨NB, hb⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) 1
  refine ⟨3 + NP + NS + NB, by omega, ?_⟩
  intro N hN L H hband hH x hx S hS hsystems
  classical
  have hBN : L + 1 < N := by
    have hh := hb N (by omega) L hband
    have hBR : (((L + 1 : ℕ) : ℝ)) < (N : ℝ) := by simpa only [pow_one, one_mul] using hh
    exact_mod_cast hBR
  let P := (pool 1 L H K).filter (fun q ↦ 2 ≤ (q.1.2 0).card)
  let T := fun q : Pattern 1 ↦ S.filter (fun y : ℕ ↦ IsSquare
    (coefficient q 0 * integerProduct (q.1.1 0) (x : ℤ) * integerProduct (q.1.2 0) (y : ℤ)))
  have hcover : ∀ y ∈ S, ∃ q ∈ P, y ∈ T q := by
    intro y hy
    obtain ⟨q, hq, htwo, hr⟩ := hsystems y hy
    exact ⟨q, mem_filter.mpr ⟨hq, htwo⟩, mem_filter.mpr ⟨hy, hr⟩⟩
  have hbound : ∀ q ∈ P, ((T q).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    intro q hq
    obtain ⟨hqpool, htwo⟩ := mem_filter.mp hq
    have hdata := (mem_pool 1 L H K q).mp hqpool
    have hprod : 0 < integerProduct (q.1.1 0) (x : ℤ) :=
      prod_pos (fun a ha ↦ (window_value_bound (by omega) hBN hx a (left_bound hqpool 0 a ha)).1)
    apply hs N (by omega) (q.1.2 0) htwo (hdata.2.1 0).2
      (coefficient q 0 * integerProduct (q.1.1 0) (x : ℤ))
      (mul_ne_zero (coefficient_pos hqpool 0).ne' hprod.ne') (T q)
    intro y hy
    exact ⟨fun a ha ↦ window_value_bound (by omega) hBN (hS y (mem_filter.mp hy).1) a
      (right_bound hqpool 0 a ha), (mem_filter.mp hy).2⟩
  have hh := FiniteCoverCount.cardinal_le S P T ((N : ℝ) ^ (ε / 2)) hcover hbound
  have hP : (P.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (P.card : ℝ) ≤ (pool 1 L H K).card by exact_mod_cast card_filter_le _ _).trans
      (hp N (by omega) L H hband hH)
  calc
    _ ≤ (P.card : ℝ) * (N : ℝ) ^ (ε / 2) := hh
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← Real.rpow_add (by exact_mod_cast (show 0 < N by omega))]; congr 1; ring

end PaperP1.FixedPartnerPatternCount

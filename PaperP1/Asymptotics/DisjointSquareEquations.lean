module

public import PaperP1.Arithmetic.SquareEquationKernel
public import PaperP1.Asymptotics.FixedDegreeKernelCount

/-! # One split square equation of degree at least two, or two disjoint equations

The coefficients are arbitrary nonzero integers. Fixed-degree kernel
fibres give the count, without a general algebraic-curve point estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointSquareEquations

open Finset PaperP1.SplitOffsetProducts

theorem combine {A B : Finset ℤ} (hAB : Disjoint A B) {D E z : ℤ}
    (hA : IsSquare (D * ∏ u ∈ A, (z + u)))
    (hB : IsSquare (E * ∏ u ∈ B, (z + u))) :
    IsSquare ((D * E) * ∏ u ∈ A ∪ B, (z + u)) := by
  rw [prod_union hAB]
  convert hA.mul hB using 1; ring

theorem single_equation (a b : ℝ) (ha : 0 < a) (d : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ, ∀ c : ℤ,
      0 < W → 2 ≤ A.card → A.card ≤ d → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ u ∈ A, u.natAbs ≤ W) → c ≠ 0 → ∀ S : Finset ℕ,
        (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧
          IsSquare (c * ∏ u ∈ A, ((n : ℤ) + u))) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨C, _, hcomp⟩ := ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨NK, hNK⟩ := FixedDegreeKernelCount.real_interval_count a b ha d D A₀ ε hε
  obtain ⟨NW, hNW⟩ := ComparableSplitProductCount.width_lt_centre C D A₀
  refine ⟨max NK NW, ?_⟩
  intro N hN W A c hW hcard hcardhi hwidth hA hc S hS
  apply hNK N (by omega) W (SmallPrimeBudget.squarefreeKernel c.natAbs) A
    hW hcard hcardhi hwidth hA S
  intro n hn
  obtain ⟨hnlo, hnhi, hsquare⟩ := hS n hn
  exact ⟨hnlo, hnhi, SquareEquationKernel.integer_square_to_kernel A n W c hc
    (hNW N (by omega) n W (hcomp N n hnlo hnhi).1 hwidth) hA hsquare⟩

theorem two_equations (a b : ℝ) (ha : 0 < a) (d : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A B : Finset ℤ, ∀ c e : ℤ,
      0 < W → A.Nonempty → B.Nonempty → Disjoint A B → A.card ≤ d → B.card ≤ d →
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ u ∈ A ∪ B, u.natAbs ≤ W) → c ≠ 0 → e ≠ 0 → ∀ S : Finset ℕ,
        (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧
          IsSquare (c * ∏ u ∈ A, ((n : ℤ) + u)) ∧
          IsSquare (e * ∏ u ∈ B, ((n : ℤ) + u))) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := single_equation a b ha (2 * d) D A₀ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN W A B c e hW hAne hBne hAB hAc hBc hwidth hroots hc he S hS
  have hcard : 2 ≤ (A ∪ B).card := by
    rw [card_union_of_disjoint hAB]
    have hA := card_pos.mpr hAne
    have hB := card_pos.mpr hBne
    omega
  have hcardhi : (A ∪ B).card ≤ 2 * d := by rw [card_union_of_disjoint hAB]; omega
  apply hN₀ N hN W (A ∪ B) (c * e) hW hcard hcardhi hwidth hroots (mul_ne_zero hc he) S
  intro n hn
  obtain ⟨hnlo, hnhi, hsqA, hsqB⟩ := hS n hn
  exact ⟨hnlo, hnhi, combine hAB hsqA hsqB⟩

theorem integer_two_equations (a b : ℝ) (ha : 0 < a) (d : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A B : Finset ℤ, ∀ c e : ℤ,
      0 < W → A.Nonempty → B.Nonempty → Disjoint A B → A.card ≤ d → B.card ≤ d →
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ u ∈ A ∪ B, u.natAbs ≤ W) → c ≠ 0 → e ≠ 0 → ∀ S : Finset ℤ,
        (∀ z ∈ S, a * N ≤ z ∧ (z : ℝ) ≤ b * N ∧
          IsSquare (c * ∏ u ∈ A, (z + u)) ∧ IsSquare (e * ∏ u ∈ B, (z + u))) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  classical
  obtain ⟨N₀, hN₀⟩ := two_equations a b ha d D A₀ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN W A B c e hW hAne hBne hAB hAc hBc hwidth hroots hc he S hS
  have hnonneg : ∀ z ∈ S, 0 ≤ z := by
    intro z hz
    have h : (0 : ℝ) ≤ z := (mul_nonneg ha.le (Nat.cast_nonneg N)).trans (hS z hz).1
    exact_mod_cast h
  have hcast : ∀ z ∈ S, (z.toNat : ℤ) = z := fun z hz ↦ Int.toNat_of_nonneg (hnonneg z hz)
  have hinj : Set.InjOn Int.toNat (S : Set ℤ) := by
    intro z hz w hw hzw
    rw [← hcast z hz, ← hcast w hw]
    exact congrArg (fun n : ℕ ↦ (n : ℤ)) hzw
  have hcount := hN₀ N hN W A B c e hW hAne hBne hAB hAc hBc hwidth hroots hc he
    (S.image Int.toNat) (by
      intro n hn
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
      obtain ⟨hzlo, hzhi, hsqA, hsqB⟩ := hS z hz
      have hreal : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hcast z hz
      refine ⟨by rwa [hreal], by rwa [hreal], ?_, ?_⟩
      · simpa only [hcast z hz] using hsqA
      · simpa only [hcast z hz] using hsqB)
  simpa only [card_image_of_injOn hinj] using hcount

end PaperP1.DisjointSquareEquations

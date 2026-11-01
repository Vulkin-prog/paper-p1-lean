module

public import PaperP1.Asymptotics.OffsetLineMajorant

/-! # Companion T20.1 for the actual line population, with uniform thresholds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineTheorem

open Finset PaperP1.OffsetLinePopulation PaperP1.OffsetLineData PaperP1.OffsetLinePrimeProduct
  PaperP1.OffsetLineCount PaperP1.OffsetLineMajorant PaperP1.PrimitiveTripleDirection PaperP1.Arithmetic

def PrimitiveProductBound (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ)) : Prop :=
  ∃ a b : pool N L H X line, point (offsets N L H X line) a ≠ point (offsets N L H X line) b ∧
    ∃ d : Fin 3 → ℤ, Primitive d ∧ height d ≤ L + 1 ∧
      (∀ p : pool N L H X line, ∃ t : ℤ, ∀ i,
        point (offsets N L H X line) p i = point (offsets N L H X line) a i + t * d i) ∧
      (∀ v ∈ line, ∃ t : ℤ, ∀ i, v i = point (offsets N L H X line) a i + t * d i) ∧
      (pool N L H X line).prod id ≤ 6 * N * height d ∧ 6 * N * height d ≤ 6 * N * (L + 1)

def FiniteConclusion (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ)) : Prop :=
  ((points (offsets N L H X line)).card ≤ 1 → (pool N L H X line).prod id ≤ 3 * N) ∧
  (1 < (points (offsets N L H X line)).card → PrimitiveProductBound N L H X line) ∧
  ∀ Y : ℝ, H ≤ Y → ((points (offsets N L Y X line)).card : ℝ) ≤ sourceMajorant N L Y

theorem finite_bounds (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hN : 10 ≤ N) (hB : 2 ≤ L + 1) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hline : CollinearSet line) (hH : ((L + 1 : ℕ) : ℝ) ≤ H) : FiniteConclusion N L H X line := by
  have hP : ∀ p ∈ pool N L H X line, Nat.Prime p := fun p hp ↦ ((mem_pool N L H X line p).mp hp).2.1
  have hdiv : ∀ p : pool N L H X line, ∀ i,
      p.val ∣ PaperP1.SaturationPrimes.value (X i) (offsets N L H X line p i) := by
    intro p i
    exact PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport (offsets_odd N L H X line p i)
  refine ⟨?_, ?_, ?_⟩
  · exact single_point_product_bound X (offsets N L H X line) hN hLN hX hP hdiv
  · intro hsize
    obtain ⟨a, b, hab, d, hd, hheight, hparam, hbound⟩ := line_product_bound X (offsets N L H X line)
      hN hLN hX hP hdiv hinj hdirect (offsets_collinear N L H X line hline) hsize
    obtain ⟨t, ht⟩ := hparam b
    have ht0 : t ≠ 0 := by
      intro hz
      apply hab
      funext i
      have h := ht i
      rw [hz, zero_mul, add_zero] at h
      exact h.symm
    have hwhole : ∀ v ∈ line, ∃ s : ℤ, ∀ i, v i = point (offsets N L H X line) a i + s * d i := by
      intro v hv
      exact PaperP1.IntegralLine.parametrize_line_of_primitive _ _ d hd t ht0 ht v
        (hline _ (offsets_on_line N L H X line a) _ (offsets_on_line N L H X line b) v hv)
    exact ⟨a, b, hab, d, hd, hheight, hparam, hwhole, hbound, Nat.mul_le_mul_left (6 * N) hheight⟩
  · intro Y hY
    have hY1 : 1 < Y := by
      have hBR : (2 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hB
      linarith
    exact distinct_offsets_le_sourceMajorant N L Y X line hN hLN hX hinj hdirect hline hY1

/-- The constant is absolute; the threshold precedes H, the centers, the line and Y. -/
theorem uniform_stronger (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ H : ℝ, ((L + 1 : ℕ) : ℝ) ≤ H → ∀ X : Fin 3 → ℕ,
      (∀ i, X i ∈ Ico N (2 * N)) → Function.Injective (evenSquareClassMap (X 0) L) →
      Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L) →
      ∀ line : Set (Fin 3 → ℤ), CollinearSet line →
      FiniteConclusion N L H X line ∧ ∀ Y : ℝ, H ≤ Y →
        sourceMajorant N L Y ≤ majorantConstant * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) ∧
        sourceMajorant N L Y ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Nmajor, hmajor⟩ := majorant_bound_eventually C
  obtain ⟨Nlittle, hlittle⟩ := majorant_little_o_uniform C ε hε
  refine ⟨max Nfinite (max Nmajor Nlittle), ?_⟩
  intro N hN L hL H hH X hX hinj hdirect line hline
  obtain ⟨hN10, hB, hLN, _, _⟩ := hfinite N (by omega) L hL
  refine ⟨finite_bounds N L H X line hN10 hB hLN hX hinj hdirect hline hH, ?_⟩
  intro Y hY
  exact ⟨hmajor N (by omega) L hL Y (hH.trans hY), hlittle N (by omega) L hL Y (hH.trans hY)⟩

/-- The original three-regular-window specialization of companion Lemma T20.1. -/
theorem companion_T20_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ C C₀ ε : ℝ, 1 < C₀ → 0 < ε → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ X : Fin 3 → ℕ, (∀ i, X i ∈ Ico N (2 * N)) →
      (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) →
      Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
      ∀ line : Set (Fin 3 → ℤ), CollinearSet line →
      FiniteConclusion N L (C₀ * ((L + 1 : ℕ) : ℝ)) X line ∧
      ∀ Y : ℝ, C₀ * ((L + 1 : ℕ) : ℝ) ≤ Y →
        sourceMajorant N L Y ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) ∧
        sourceMajorant N L Y ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  refine ⟨majorantConstant, majorantConstant_pos, ?_⟩
  intro C C₀ ε hC₀ hε
  obtain ⟨N₀, hN₀⟩ := uniform_stronger C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL X hX hrank hpair line hline
  have hH : ((L + 1 : ℕ) : ℝ) ≤ C₀ * ((L + 1 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hC₀.le (Nat.cast_nonneg (α := ℝ) (L + 1))
    simpa only [one_mul] using h
  exact hN₀ N hN L hL _ hH X hX
    (PaperP1.TwoPointSquareClasses.injective_evenMap_of_rank (X 0) L (hrank 0))
    (hpair (by decide : (0 : Fin 3) ≠ 1)) line hline

end PaperP1.OffsetLineTheorem

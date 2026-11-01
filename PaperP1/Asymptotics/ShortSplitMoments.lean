module

public import PaperP1.Asymptotics.SquareTupleCount
public import PaperP1.Model.MultiplicativeMoments

/-! # The actual uniform short split-product moment bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortSplitMoments

open Finset MeasureTheory PaperP1.SplitOffsetProducts PaperP1.SplitKernelStates
open PaperP1.ProfileTupleCount PaperP1.Model.InfiniteRademacher
open PaperP1.Model.MultiplicativeMoments

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

def sumValue (A : Finset ℤ) (S : Finset ℕ) (ω : InfiniteSample) : ℝ :=
  ∑ n ∈ S, (infiniteRandomValue ω (product A n) : ℝ)

theorem uniform_moment (v : ℕ) (hv : 2 ≤ v) (heven : Even v)
    (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N) →
      (∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure) ≤
        (N : ℝ) ^ (mainExponent v c + ε) := by
  classical
  obtain ⟨Nt, hNt⟩ := PaperP1.SquareTupleCount.square_tuple_count (ι := Fin v)
    (by simpa only [Fintype.card_fin] using hv) C hC c D A₀ ε hc hε
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitTupleExposure.source_height C D A₀
  refine ⟨max Nt Nh, ?_⟩
  intro N hN W A hW hAeven hcard hwidth hdegree hA S hS
  have hpos : ∀ n : S, product A n.val ≠ 0 := by
    intro n
    exact (hNh N (by omega) W n.val A (hS n.val n.property).1 (hS n.val n.property).2 hwidth hA).1.ne'
  let X : S → ℕ := fun n ↦ product A n.val
  let U := squareTuples X v
  let f : (Fin v → S) → (Fin v → ℕ) := fun n i ↦ (n i).val
  let T := U.image f
  have hf : Function.Injective f := by
    intro n m hnm
    funext i
    exact Subtype.ext (congrFun hnm i)
  have hT : ∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧ IsSquare (∏ j, kernels A n j) := by
    intro n hnT
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hnT
    have hsq : IsSquare (∏ j, product A (m j).val) := (mem_filter.mp hm).2
    refine ⟨fun j ↦ hS (m j).val (m j).property, ?_⟩
    exact (PaperP1.KernelTuplePatterns.split_kernel_product_square_iff univ A (f m)
      (fun j _ ↦ Nat.pos_of_ne_zero (hpos (m j)))).mpr hsq
  have hcount := hNt N (by omega) W A hW hAeven hcard hwidth hdegree hA T hT
  have hcardT : T.card = U.card := card_image_of_injOn hf.injOn
  rw [hcardT] at hcount
  have hid := infinite_even_moment X hpos v heven
  have hmoment : (∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure) = (U.card : ℝ) := by
    have hobs : (fun ω ↦ |sumValue A S ω| ^ v) =
        (fun ω ↦ |∑ n : S, (infiniteRandomValue ω (product A n.val) : ℝ)| ^ v) := by
      funext ω
      have hs := sum_coe_sort S (fun n ↦ (infiniteRandomValue ω (product A n) : ℝ))
      exact congrArg (fun z : ℝ ↦ |z| ^ v) hs.symm
    rw [hobs]
    exact hid
  rw [hmoment]
  simpa only [Fintype.card_fin] using hcount

theorem uniform_moment_real_bounds (v : ℕ) (hv : 2 ≤ v) (heven : Even v)
    (a b : ℝ) (ha : 0 < a) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      (∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure) ≤
        (N : ℝ) ^ (mainExponent v c + ε) := by
  obtain ⟨C, hC, hcomp⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨N₀, hN₀⟩ := uniform_moment v hv heven C hC c D A₀ ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W A hW hAeven hcard hwidth hdegree hA S hS
  exact hN₀ N hN W A hW hAeven hcard hwidth hdegree hA S
    (fun n hnS ↦ hcomp N n (hS n hnS).1 (hS n hnS).2)

theorem article_9_1 (v : ℕ) (hv : 2 ≤ v) (heven : Even v)
    (a b : ℝ) (ha : 0 < a) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      (∀ n ∈ S, 0 < product A n ∧ (product A n : ℤ) = ∏ a ∈ A, ((n : ℤ) + a) ∧
        0 < ∏ a ∈ A, ((n : ℤ) + a)) ∧
      (∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure) ≤
        (N : ℝ) ^ (mainExponent v c + ε) := by
  obtain ⟨C, hC, hcomp⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨Nm, hNm⟩ := uniform_moment v hv heven C hC c D A₀ ε hc hε
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.source_product_values C D A₀
  refine ⟨max Nm Nv, ?_⟩
  intro N hN W A hW hAeven hcard hwidth hdegree hA S hS
  have hSC : ∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N :=
    fun n hnS ↦ hcomp N n (hS n hnS).1 (hS n hnS).2
  exact ⟨fun n hnS ↦ hNv N (by omega) n W A (hSC n hnS).1 hwidth hA,
    hNm N (by omega) W A hW hAeven hcard hwidth hdegree hA S hSC⟩

end PaperP1.ShortSplitMoments

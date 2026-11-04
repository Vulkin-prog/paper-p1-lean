module

public import PaperP1.Arithmetic.SmallTransverseHostData
public import PaperP1.Asymptotics.SmallMotifCoefficientBounds

/-! # A fixed third centre and actual primitive grids give the missing linear count

Only the existing ordinary surface-cover and normalized curve properties are
unproved arguments. Every coefficient list and actual admissibility condition
is constructed before applying them.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallTransverseHostCount

open Finset PaperP1.Model PaperP1.ManyPlanarSquareProducts PaperP1.SmallTransverseHostData

def pair (e : Equiv.Perm (Fin 3)) (X : Fin 3 → ℕ) : ℤ × ℤ := ((X (e 0) : ℤ), (X (e 1) : ℤ))

theorem pair_injective_on_fibre (e : Equiv.Perm (Fin 3)) (z : ℕ) :
    Set.InjOn (pair e) {X : Fin 3 → ℕ | X (e 2) = z} := by
  intro X hX Y hY hp
  have h0 : X (e 0) = Y (e 0) := by
    have hh := congrArg Prod.fst hp
    change (X (e 0) : ℤ) = (Y (e 0) : ℤ) at hh
    exact_mod_cast hh
  have h1 : X (e 1) = Y (e 1) := by
    have hh := congrArg Prod.snd hp
    change (X (e 1) : ℤ) = (Y (e 1) : ℤ) at hh
    exact_mod_cast hh
  have h2 : X (e 2) = Y (e 2) := hX.trans hY.symm
  have he (i : Fin 3) : X (e i) = Y (e i) := by fin_cases i <;> assumption
  funext j
  simpa only [Equiv.apply_symm_apply] using he (e.symm j)

theorem uniform_oriented (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k 4 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
        ∀ e : Equiv.Perm (Fin 3), ∀ z ∈ dyadicBlock N, ∀ S : Finset (Fin 3 → ℕ),
          (∀ X ∈ S, RegularDirect N L X ∧ X (e 2) = z ∧ Oriented k L H X e) →
          (S.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨A₀, NH, _hNH, hheight⟩ := SmallMotifCoefficientBounds.uniform_height C D
  obtain ⟨k, hk, hroot⟩ := CoefficientSelectedDegreeOneHostCount.uniform_hosts C A₀ ε 4
    (Nat.cast_nonneg A₀) hε
  obtain ⟨NQ, _hNQ, hpool⟩ := SmallMotifCoefficientBounds.uniform_pool C D
    (CriticalCoefficientPatterns.coefficientMargin (ε / 2) k)
    (CriticalCoefficientPatterns.margin_pos (by positivity) k)
  refine ⟨k, hk, ?_⟩
  intro hCover hCurve
  obtain ⟨A, hA, NC, hc⟩ := hroot hCover hCurve
  refine ⟨A, hA, 10 + NH + NQ + NC, by omega, ?_⟩
  intro N hN L H hband hH e z hz S hS
  let Q := SmallMotifCoefficients.pool z L H
  let F := S.image (pair e)
  have hcard : F.card = S.card := card_image_iff.mpr (fun X hX Y hY hp ↦
    pair_injective_on_fibre e z (hS X hX).2.1 (hS Y hY).2.1 hp)
  have hF : ∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧
      p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N := by
    intro p hp
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hp
    have hx := mem_Ico.mp ((hS X hX).1.2.1 (e 0)).1
    have hy := mem_Ico.mp ((hS X hX).1.2.1 (e 1)).1
    dsimp only [pair]
    exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hy.1, hx.2.le, hy.2.le⟩
  have hsystems : ∀ p ∈ F, ∃ q ∈ CoefficientSplitRadicalPatterns.pool k L 4 Q,
      CoefficientDegreeOneHostCount.Valid 4 q ∧
      SourceCurvePointCover.Admissible (CoefficientPatternGrids.left q) (CoefficientPatternGrids.right q) p ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = CoefficientSplitRadicalPatterns.coefficient q i *
        SplitRadicalPointHeight.integerProduct (q.1.1 i) p.1 *
        SplitRadicalPointHeight.integerProduct (q.1.2 i) p.2 := by
    intro p hp
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hp
    have ho := (hS X hX).2.2
    have hzX := (hS X hX).2.1
    unfold Oriented at ho
    rw [hzX] at ho
    exact ho
  have hh := hc N (by omega) L hband Q (hpool N (by omega) L H hband hH z hz)
    (hheight N (by omega) L H hband hH z hz) F hF hsystems
  simpa only [hcard] using hh

theorem uniform_count (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k 4 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
        ∀ S : Finset (Fin 3 → ℕ),
          (∀ X ∈ S, RegularDirect N L X ∧ SmallTransverseHostData.Many (24 * k) L H X) →
          (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε)) := by
  obtain ⟨k, hk, hp⟩ := uniform_oriented C D (ε / 2) (by positivity)
  refine ⟨k, hk, ?_⟩
  intro hCover hCurve
  obtain ⟨A, hA, NC, _hNC, hc⟩ := hp hCover hCurve
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (6 * A) (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NC + NF, by omega, ?_⟩
  intro N hN L H hband hH S hS
  classical
  let I := (univ : Finset (Equiv.Perm (Fin 3))) ×ˢ dyadicBlock N
  let T := fun t : Equiv.Perm (Fin 3) × ℕ ↦ S.filter (fun X ↦ X (t.1 2) = t.2 ∧ Oriented k L H X t.1)
  have hcover : ∀ X ∈ S, ∃ t ∈ I, X ∈ T t := by
    intro X hX
    obtain ⟨e, he⟩ := exists_system (by omega) (by omega) X (hS X hX).1 (hS X hX).2
    exact ⟨(e, X (e 2)), mem_product.mpr ⟨mem_univ _, ((hS X hX).1.2.1 (e 2)).1⟩,
      mem_filter.mpr ⟨hX, rfl, he⟩⟩
  have hbound : ∀ t ∈ I, ((T t).card : ℝ) ≤ A * (N : ℝ) ^ (ε / 2) := by
    intro t ht
    apply hc N (by omega) L H hband hH t.1 t.2 (mem_product.mp ht).2 (T t)
    intro X hX
    exact ⟨(hS X (mem_filter.mp hX).1).1, (mem_filter.mp hX).2⟩
  have hh := FiniteCoverCount.cardinal_le S I T (A * (N : ℝ) ^ (ε / 2)) hcover hbound
  have hdyadic : (dyadicBlock N).card = N := by rw [dyadicBlock, Nat.card_Ico]; omega
  have hperms : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hI : I.card = 6 * N := by rw [card_product, card_univ, hperms, hdyadic]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (I.card : ℝ) * (A * (N : ℝ) ^ (ε / 2)) := hh
    _ = (6 * A) * (N : ℝ) ^ (1 + ε / 2) := by
      rw [hI, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_add hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SmallTransverseHostCount

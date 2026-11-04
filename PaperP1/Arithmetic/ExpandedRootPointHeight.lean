module

public import PaperP1.Arithmetic.OrdinaryRootPointHeight
public import PaperP1.Arithmetic.SourceIntegerPointHeight

/-! # Fixed expansion factors change the lift constant, not its degree or scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedRootPointHeight

open PaperP1.SplitRadicalPointHeight

def constant (Q K D : ℕ) : ℝ := OrdinaryRootPointHeight.constant K D * (Q : ℝ) ^ D

theorem constant_ge_one {Q : ℕ} (K D : ℕ) (hQ : 1 ≤ Q) : 1 ≤ constant Q K D := by
  have hc := OrdinaryRootPointHeight.constant_ge_one K D
  have hq : (1 : ℝ) ≤ (Q : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hQ)
  dsimp [constant]
  nlinarith only [hc, hq]

theorem scaled_height (Q N K D : ℕ) :
    OrdinaryRootPointHeight.constant K D * ((Q * N : ℕ) : ℝ) ^ D = constant Q K D * (N : ℝ) ^ D := by
  rw [Nat.cast_mul, mul_pow, constant, mul_assoc]

theorem ordinary_floor_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ) (Q N K D : ℕ) (A₀ : ℝ)
    (hQ : 1 ≤ Q) (hA₀ : 0 ≤ A₀) (hD : 0 < D) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * (Q * N)) (hy : y.natAbs ≤ 2 * (Q * N))
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    let R := constant Q K D * (N : ℝ) ^ D
    1 ≤ ⌊R⌋₊ ∧ (⌊R⌋₊ : ℝ) ≤ R ∧ OrdinaryIntegerPoints.lift x y w ∈
      OrdinaryIntegerPoints.curvePoints (WeightedOrdinaryAffineIdeal.ordinaryIdeal (fun i ↦ (d i : ℚ)) I J) ⌊R⌋₊ := by
  have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
  have hd' (i) : ((d i).natAbs : ℝ) ≤ ((Q * N : ℕ) : ℝ) ^ A₀ :=
    (hd i).trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNM) hA₀)
  simpa only [scaled_height] using OrdinaryRootPointHeight.point_floor_height I J d w x y (Q * N) K D A₀
    hD (hN.trans hNM) hx hy (fun i z hz ↦ (hI i z hz).trans hNM)
    (fun i z hz ↦ (hJ i z hz).trans hNM) hK hdegree hd' hroot

theorem source_floor_box {ι : Type} [Finite ι]
    (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ) (Q N K D : ℕ) (A₀ : ℝ)
    (hQ : 1 ≤ Q) (hA₀ : 0 ≤ A₀) (hD : 0 < D) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * (Q * N)) (hy : y.natAbs ≤ 2 * (Q * N))
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    let R := constant Q K D * (N : ℝ) ^ D
    1 ≤ ⌊R⌋₊ ∧ (⌊R⌋₊ : ℝ) ≤ R ∧ SourceIntegerLift.point D x y w ∈ SourceIntegerPoints.box D ⌊R⌋₊ := by
  have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
  have hd' (i) : ((d i).natAbs : ℝ) ≤ ((Q * N : ℕ) : ℝ) ^ A₀ :=
    (hd i).trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNM) hA₀)
  simpa only [scaled_height] using SourceIntegerPointHeight.point_floor_box I J d w x y (Q * N) K D A₀
    hD (hN.trans hNM) hx hy (fun i z hz ↦ (hI i z hz).trans hNM)
    (fun i z hz ↦ (hJ i z hz).trans hNM) hK hdegree hd' hroot

end PaperP1.ExpandedRootPointHeight

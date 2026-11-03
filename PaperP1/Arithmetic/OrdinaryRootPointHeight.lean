module

public import PaperP1.Arithmetic.OrdinaryRootEvaluation
public import PaperP1.Algebra.SplitRadicalEmbeddingHeight
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FinCases

/-! # The actual ordinary integer radical lift has a polynomial height independent of the equation count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryRootPointHeight

open PaperP1.OrdinaryIntegerPoints PaperP1.SplitRadicalPointHeight PaperP1.SplitRadicalEmbeddingHeight
  PaperP1.WeightedOrdinaryAffineIdeal

def constant (K D : ℕ) : ℝ := (2 : ℝ) ^ D + (3 : ℝ) ^ K

theorem constant_ge_one (K D : ℕ) : 1 ≤ constant K D :=
  (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans (le_add_of_nonneg_right (by positivity))

theorem coordinates_height {ι : Type*} (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ)
    (N K D : ℕ) (A₀ : ℝ) (hD : 0 < D) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    ∀ t : Fin 3 ⊕ ι, ((lift x y w t).natAbs : ℝ) ≤ constant K D * (N : ℝ) ^ D := by
  have hpow : 0 ≤ (N : ℝ) ^ D := by positivity
  have hbase : (2 : ℝ) ^ D ≤ constant K D := le_add_of_nonneg_right (by positivity)
  have hrad : (3 : ℝ) ^ K ≤ constant K D := le_add_of_nonneg_left (by positivity)
  have hX : (x.natAbs : ℝ) ≤ constant K D * (N : ℝ) ^ D := by
    have hx' := monomial_height x y N 1 0 D hN hx hy (by omega)
    simp only [pow_one, pow_zero, mul_one] at hx'
    have h : (x.natAbs : ℝ) ≤ (2 : ℝ) ^ D * (N : ℝ) ^ D := by exact_mod_cast hx'
    exact h.trans (mul_le_mul_of_nonneg_right hbase hpow)
  have hY : (y.natAbs : ℝ) ≤ constant K D * (N : ℝ) ^ D := by
    have hy' := monomial_height x y N 0 1 D hN hx hy (by omega)
    simp only [pow_one, pow_zero, one_mul] at hy'
    have h : (y.natAbs : ℝ) ≤ (2 : ℝ) ^ D * (N : ℝ) ^ D := by exact_mod_cast hy'
    exact h.trans (mul_le_mul_of_nonneg_right hbase hpow)
  have hOne : 1 ≤ constant K D * (N : ℝ) ^ D := by
    have hNp : (1 : ℝ) ≤ (N : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hN)
    have hC := constant_ge_one K D
    nlinarith
  intro t
  cases t with
  | inl j =>
      fin_cases j
      · exact hY
      · exact hX
      · change ((lift x y w (Sum.inl (2 : Fin 3))).natAbs : ℝ) ≤ constant K D * (N : ℝ) ^ D
        rw [lift_Z, Int.natAbs_one, Nat.cast_one]
        exact hOne
  | inr i =>
      have h := radical_height (I i) (J i) x y (w i) (d i) N K hN hx hy (hI i) (hJ i) (hK i)
        A₀ D hdegree (hd i) (hroot i)
      have h' : ((w i).natAbs : ℝ) ≤ (3 : ℝ) ^ K * (N : ℝ) ^ D := by
        simpa only [Real.rpow_natCast] using h
      exact h'.trans (mul_le_mul_of_nonneg_right hrad hpow)

theorem point_floor_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ) (N K D : ℕ) (A₀ : ℝ)
    (hD : 0 < D) (hN : 1 ≤ N) (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    let R := constant K D * (N : ℝ) ^ D
    1 ≤ ⌊R⌋₊ ∧ (⌊R⌋₊ : ℝ) ≤ R ∧
      lift x y w ∈ curvePoints (ordinaryIdeal (fun i ↦ (d i : ℚ)) I J) ⌊R⌋₊ := by
  let R := constant K D * (N : ℝ) ^ D
  have hR : 1 ≤ R := by
    have hNp : (1 : ℝ) ≤ (N : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hN)
    have hC := constant_ge_one K D
    dsimp [R]
    nlinarith
  have hR0 : 0 ≤ R := by linarith
  refine ⟨(Nat.one_le_floor_iff R).mpr hR, Nat.floor_le hR0, ?_⟩
  apply OrdinaryRootEvaluation.lift_mem d I J x y w ⌊R⌋₊ _ hroot
  intro t
  have ht := coordinates_height I J d w x y N K D A₀ hD hN hx hy hI hJ hK hdegree hd hroot t
  have hnat : (lift x y w t).natAbs ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR0).mpr ht
  have hint : ((lift x y w t).natAbs : ℤ) ≤ (⌊R⌋₊ : ℤ) := by exact_mod_cast hnat
  simpa only [Int.natCast_natAbs] using hint

end PaperP1.OrdinaryRootPointHeight

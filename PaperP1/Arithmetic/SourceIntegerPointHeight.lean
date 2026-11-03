module

public import PaperP1.Arithmetic.SourceIntegerPoints
public import PaperP1.Arithmetic.OrdinaryRootPointHeight

/-! # A coefficient-uniform height for the actual source embedding's literal integer coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerPointHeight

open PaperP1.SourceProjectiveEmbedding PaperP1.SourceIntegerLift PaperP1.SplitRadicalPointHeight

theorem coordinates_height {ι : Type} (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ)
    (N K D : ℕ) (A₀ : ℝ) (hD : 0 < D) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    ∀ g : GeneratorIndex ℚ ι D, ((point D x y w g).natAbs : ℝ) ≤
      OrdinaryRootPointHeight.constant K D * (N : ℝ) ^ D := by
  have hraw := OrdinaryRootPointHeight.coordinates_height I J d w x y N K D A₀ hD hN hx hy hI hJ hK hdegree hd hroot
  intro g
  obtain ⟨t, rfl⟩ := (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D).surjective g
  cases t with
  | inl e =>
    rw [point_base]
    have hsum : e.val 1 + e.val 0 ≤ D := by
      have he := e.property
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at he
      omega
    have hmono : ((x ^ e.val 1 * y ^ e.val 0).natAbs : ℝ) ≤ (2 : ℝ) ^ D * (N : ℝ) ^ D := by
      exact_mod_cast monomial_height x y N (e.val 1) (e.val 0) D hN hx hy hsum
    exact hmono.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity))
  | inr i =>
    rw [point_radical]
    exact hraw (Sum.inr i)

theorem point_floor_box {ι : Type} [Finite ι] (I J : ι → Finset ℤ) (d w : ι → ℤ) (x y : ℤ)
    (N K D : ℕ) (A₀ : ℝ) (hD : 0 < D) (hN : 1 ≤ N)
    (hx : x.natAbs ≤ 2 * N) (hy : y.natAbs ≤ 2 * N)
    (hI : ∀ i, ∀ z ∈ I i, z.natAbs ≤ N) (hJ : ∀ i, ∀ z ∈ J i, z.natAbs ≤ N)
    (hK : ∀ i, (I i).card + (J i).card ≤ K) (hdegree : A₀ + (K : ℝ) ≤ 2 * D)
    (hd : ∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    let R := OrdinaryRootPointHeight.constant K D * (N : ℝ) ^ D
    1 ≤ ⌊R⌋₊ ∧ (⌊R⌋₊ : ℝ) ≤ R ∧ point D x y w ∈ SourceIntegerPoints.box D ⌊R⌋₊ := by
  intro R
  have hR : 1 ≤ R := by
    have hC := OrdinaryRootPointHeight.constant_ge_one K D
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hN)
    dsimp [R]
    nlinarith
  refine ⟨(Nat.one_le_floor_iff R).mpr hR, Nat.floor_le (by linarith), ?_⟩
  apply (SourceIntegerPoints.mem_box D ⌊R⌋₊ _).mpr
  refine ⟨?_, SourceIntegerPoints.point_normalizer D x y w⟩
  intro g
  have hg := coordinates_height I J d w x y N K D A₀ hD hN hx hy hI hJ hK hdegree hd hroot g
  have hfloor : (point D x y w g).natAbs ≤ ⌊R⌋₊ := Nat.le_floor hg
  simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr hfloor

end PaperP1.SourceIntegerPointHeight

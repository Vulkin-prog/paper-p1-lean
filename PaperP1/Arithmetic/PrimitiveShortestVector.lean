module

public import PaperP1.Analysis.BinaryLatticeMinimum

/-! # The actual shortest lattice vector is primitive, with an explicit coordinate bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveShortestVector

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction

theorem image_scaling (T : Matrix (Fin 2) (Fin 2) ℝ) (g : ℤ) (z : Fin 2 → ℤ) :
    realImage T (fun i ↦ g * z i) = fun i ↦ (g : ℝ) * realImage T z i := by
  funext i
  simp only [realImage, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Int.cast_mul]
  ring

theorem energy_scaling (T : Matrix (Fin 2) (Fin 2) ℝ) (g : ℤ) (z : Fin 2 → ℤ) :
    squareNorm (realImage T (fun i ↦ g * z i)) = (g : ℝ) ^ 2 * squareNorm (realImage T z) := by
  rw [image_scaling]
  unfold squareNorm
  ring

theorem shortest_primitive (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ) (hz : z ≠ 0)
    (hmin : ∀ w : Fin 2 → ℤ, w ≠ 0 → squareNorm (realImage T z) ≤ squareNorm (realImage T w)) :
    (z 0).natAbs.Coprime (z 1).natAbs := by
  have hgcd : 0 < Int.gcd (z 0) (z 1) := by
    apply Int.gcd_pos_iff.mpr
    by_cases h0 : z 0 = 0
    · right
      intro h1
      apply hz
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · exact Or.inl h0
  obtain ⟨g, m, n, hg, hcop, hm, hn⟩ := Int.exists_gcd_one' hgcd
  let u : Fin 2 → ℤ := ![m, n]
  have huprim : (u 0).natAbs.Coprime (u 1).natAbs := by
    change m.natAbs.Coprime n.natAbs
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hcop
  have hu : u ≠ 0 := UnimodularBinaryCoordinates.primitive_nonzero u huprim
  have heq : z = fun i ↦ (g : ℤ) * u i := by
    funext i
    fin_cases i
    · change z 0 = (g : ℤ) * m
      rw [hm]
      ring
    · change z 1 = (g : ℤ) * n
      rw [hn]
      ring
  have henergy : squareNorm (realImage T z) = (g : ℝ) ^ 2 * squareNorm (realImage T u) := by
    calc
      _ = squareNorm (realImage T (fun i ↦ (g : ℤ) * u i)) := congrArg (fun v ↦ squareNorm (realImage T v)) heq
      _ = _ := by simpa only [Int.cast_natCast] using energy_scaling T (g : ℤ) u
  have hpositive := image_energy_positive T S hST u hu
  have hminimal := hmin u hu
  have hg1 : g = 1 := by
    by_contra h
    have hg2 : 2 ≤ g := by omega
    have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have hgsq : (1 : ℝ) < (g : ℝ) ^ 2 := by nlinarith [sq_nonneg ((g : ℝ) - 2)]
    have hprod := mul_pos (sub_pos.mpr hgsq) hpositive
    nlinarith
  have hm' : z 0 = m := by simpa only [hg1, Nat.cast_one, mul_one] using hm
  have hn' : z 1 = n := by simpa only [hg1, Nat.cast_one, mul_one] using hn
  rw [hm', hn', Nat.coprime_iff_gcd_eq_one]
  exact hcop

theorem shortest_coordinate_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ)
    (hmin : ∀ w : Fin 2 → ℤ, w ≠ 0 → squareNorm (realImage T z) ≤ squareNorm (realImage T w)) :
    ∀ i, |z i| ≤ ⌈inverseSize S * squareNorm (realImage T ![1, 0]) + 1⌉ := by
  have hu : (![1, 0] : Fin 2 → ℤ) ≠ 0 := by intro h; have h0 := congrFun h 0; norm_num at h0
  exact sublevel_coordinate_bound T S hST _ z (hmin _ hu)

theorem exists_primitive_shortest (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) :
    ∃ z : Fin 2 → ℤ, z ≠ 0 ∧ (z 0).natAbs.Coprime (z 1).natAbs ∧
      (∀ w : Fin 2 → ℤ, w ≠ 0 → squareNorm (realImage T z) ≤ squareNorm (realImage T w)) ∧
      ∀ i, |z i| ≤ ⌈inverseSize S * squareNorm (realImage T ![1, 0]) + 1⌉ := by
  obtain ⟨z, hz, hmin⟩ := exists_shortest T S hST
  exact ⟨z, hz, shortest_primitive T S hST z hz hmin, hmin, shortest_coordinate_bound T S hST z hmin⟩

end PaperP1.PrimitiveShortestVector

module

public import PaperP1.Arithmetic.CutoffSquareLcm
public import PaperP1.Arithmetic.ProductFirstPassage
public import PaperP1.Arithmetic.OffsetValueGeometry

/-! # Actual nearby cutoff quotients yield a square or square-smooth CRT crossing certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelCrossingCertificates

open Finset PaperP1.LinearKernelFibres PaperP1.SmoothModulusHosts PaperP1.CutoffSquareParts
  PaperP1.CutoffSquareLcm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem finite_alternative (Y n W : ℕ) (a : ι → ℤ) (X Z : ℝ)
    (hn : W < n) (ha : ∀ i, (a i).natAbs ≤ W) (hinj : Function.Injective a)
    (hY : 2 * W ≤ Y) (hX : 1 ≤ X)
    (hsquare : ∀ i, ((largeSquarePart Y (value n (a i)) ^ 2 : ℕ) : ℝ) ≤ Z)
    (hlarge : X < ((univ.lcm fun i ↦ quotient Y (value n (a i)) : ℕ) : ℝ)) :
    (∃ r : ℕ, 0 < r ∧ X < ((r ^ 2 : ℕ) : ℝ) ∧ ((r ^ 2 : ℕ) : ℝ) ≤ X * Z ∧
      HasCertificate (ι := ι) (r ^ 2) W n) ∨
    (∃ d : ℕ, 0 < d ∧ X < (d : ℝ) ∧ (d : ℝ) ≤ X * Y ∧
      PaperP1.LargeOddKernel.largeOddKernel Y d = 1 ∧ HasCertificate (ι := ι) d W n) := by
  let v : ι → ℕ := fun i ↦ value n (a i)
  have hv : ∀ i, 0 < v i := fun i ↦ OffsetValueGeometry.value_pos hn (ha i)
  have hvi : Function.Injective v := by
    intro i j heq
    by_contra hij
    exact OffsetValueGeometry.value_ne hn (ha i) (ha j) (fun h ↦ hij (hinj h)) heq
  have hdist : ∀ i j, Nat.dist (v i) (v j) ≤ Y :=
    fun i j ↦ (OffsetValueGeometry.value_dist hn (ha i) (ha j)).trans hY
  have hpair : Pairwise fun i j ↦ Nat.Coprime (largeSquarePart Y (v i)) (largeSquarePart Y (v j)) := by
    intro i j hij
    exact large_square_parts_coprime (fun h ↦ hij (hvi h)) (hdist i j)
  have hcert (d : ℕ) (hd : 0 < d) (hdiv : d ∣ univ.lcm fun i ↦ quotient Y (v i)) :
      HasCertificate (ι := ι) d W n := by
    have hdivv := hdiv.trans (quotient_lcm_dvd_values Y v hv)
    obtain ⟨G, hG, hcop, hprod⟩ := PrimePowerAllocations.exists_allocation_of_dvd_lcm d hd v hv hdivv
    exact ⟨a, ha, G, hcop, hprod, fun i ↦ (hG i).2⟩
  by_cases hbig : X < ((squareProduct Y v : ℕ) : ℝ)
  · have hf : ∀ i ∈ (univ : Finset ι), 1 ≤ largeSquarePart Y (v i) ^ 2 ∧
        ((largeSquarePart Y (v i) ^ 2 : ℕ) : ℝ) ≤ Z :=
      fun i _ ↦ ⟨pow_pos (large_square_part_pos Y (v i)) _, hsquare i⟩
    obtain ⟨T, _hT, hlo, hhi⟩ := ProductFirstPassage.indexed_crossing univ
      (fun i ↦ largeSquarePart Y (v i) ^ 2) X Z hX hf hbig
    let r := T.prod fun i ↦ largeSquarePart Y (v i)
    have hr : 0 < r := prod_pos fun i _ ↦ large_square_part_pos Y (v i)
    have hDr : (T.prod fun i ↦ largeSquarePart Y (v i) ^ 2) = r ^ 2 := by
      simp only [r, Finset.prod_pow]
    have hd : r ^ 2 ∣ univ.lcm fun i ↦ quotient Y (v i) := by
      rw [← hDr]
      exact subset_square_dvd_lcm Y v T hpair
    exact Or.inl ⟨r, hr, by simpa only [hDr] using hlo, by simpa only [hDr] using hhi,
      hcert (r ^ 2) (pow_pos hr _) hd⟩
  · have hsp := smooth_lcm_pos Y v
    have hap := square_product_pos Y v
    have hbig' : X < (((squareProduct Y v) * smoothLcm Y v : ℕ) : ℝ) := by
      rw [Nat.mul_comm (squareProduct Y v) (smoothLcm Y v), ← quotient_lcm Y v hpair]
      exact hlarge
    obtain ⟨d, hd, hds, hlo, hhi⟩ := ProductFirstPassage.smooth_crossing (smoothLcm Y v)
      (squareProduct Y v) Y X hsp hap (le_of_not_gt hbig)
      (fun p hp hpS ↦ smooth_lcm_prime v hp hpS) hbig'
    have hD : squareProduct Y v * d ∣ univ.lcm fun i ↦ quotient Y (v i) := by
      rw [quotient_lcm Y v hpair]
      rw [Nat.mul_comm (smoothLcm Y v) (squareProduct Y v)]
      exact Nat.mul_dvd_mul_left (squareProduct Y v) hds
    have hkernel : PaperP1.LargeOddKernel.largeOddKernel Y (squareProduct Y v * d) = 1 := by
      rw [square_product_eq, Nat.mul_comm]
      apply kernel_one_of_smooth_square Y d _ hd (prod_pos fun i _ ↦ large_square_part_pos Y (v i))
      exact fun p hp hpd ↦ smooth_lcm_prime v hp (hpd.trans hds)
    exact Or.inr ⟨squareProduct Y v * d, Nat.mul_pos hap hd, hlo, hhi, hkernel,
      hcert _ (Nat.mul_pos hap hd) hD⟩

end PaperP1.SmallKernelCrossingCertificates

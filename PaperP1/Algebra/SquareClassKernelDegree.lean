module

public import PaperP1.Algebra.SquareClassRadicalDegreeBound
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! # The entire kernel on square classes has dimension bounded by the actual extension degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareClassKernelDegree

open PaperP1.FieldSquareClasses

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

theorem power_dvd_of_independent_family (U : Submodule (ZMod 2) (Classes K))
    (hU : U ≤ LinearMap.ker (FieldSquareClassMap.map (algebraMap K E)))
    (n : ℕ) (v : Fin n → U) (hv : LinearIndependent (ZMod 2) v) :
    2 ^ n ∣ Module.finrank K E := by
  classical
  choose a ha heq using (fun i : Fin n ↦ FieldSquareClassMap.exists_representative (v i : Classes K))
  have hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)) := by
    rw [linearIndependent_iff']
    intro A g hsum i hi
    have hz : (∑ j ∈ A, g j • v j : U) = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, heq] using hsum
    exact linearIndependent_iff'.mp hv A g hz i hi
  have hsq (i : Fin n) : IsSquare (algebraMap K E (a i)) := by
    apply (FieldSquareClassMap.mem_kernel_iff (algebraMap K E) (a i) (ha i)).mp
    rw [heq]
    exact hU (v i).property
  simpa only [Finset.card_univ, Fintype.card_fin] using
    SquareClassRadicalDegreeBound.power_dvd_degree a ha hli Finset.univ (fun i _ ↦ hsq i)

theorem kernel_finite [Module.Finite K E] :
    Module.Finite (ZMod 2) (LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))) := by
  let U := LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))
  let n := Nat.log 2 (Module.finrank K E) + 1
  have hsmall : Module.rank (ZMod 2) U < (n : Cardinal) := by
    by_contra hn
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (le_of_not_gt hn)
    have hpow : 2 ^ n ≤ Module.finrank K E :=
      Nat.le_of_dvd Module.finrank_pos (power_dvd_of_independent_family U le_rfl n v hv)
    have hle := Nat.le_log_of_pow_le (by decide : 1 < 2) hpow
    omega
  exact Module.rank_lt_aleph0_iff.mp (hsmall.trans Cardinal.natCast_lt_aleph0)

theorem kernel_power_dvd_degree [Module.Finite K E] :
    2 ^ Module.finrank (ZMod 2) (LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))) ∣
      Module.finrank K E := by
  let U := LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))
  let : Module.Finite (ZMod 2) U := kernel_finite
  exact power_dvd_of_independent_family U le_rfl _ (Module.finBasis (ZMod 2) U)
    (Module.finBasis (ZMod 2) U).linearIndependent

theorem kernel_power_le_degree [Module.Finite K E] :
    2 ^ Module.finrank (ZMod 2) (LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))) ≤
      Module.finrank K E := Nat.le_of_dvd Module.finrank_pos kernel_power_dvd_degree

theorem kernel_finrank_le_log [Module.Finite K E] :
    Module.finrank (ZMod 2) (LinearMap.ker (FieldSquareClassMap.map (algebraMap K E))) ≤
      Nat.log 2 (Module.finrank K E) :=
  Nat.le_log_of_pow_le (by decide) kernel_power_le_degree

end PaperP1.SquareClassKernelDegree

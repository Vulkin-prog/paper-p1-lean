module

public import PaperP1.Algebra.EvenImage

/-! # Injectivity of the even-selection map separates every pair of data vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenImageDataRigidity

open Finset

variable {K ι E : Type*} [DivisionRing K] [Fintype ι] [AddCommGroup E] [Module K E]

theorem data_injective (data : ι → E) (hinj : Function.Injective (EvenImage.evenMap (K := K) data)) :
    Function.Injective data := by
  classical
  intro i j hijdata
  by_contra hij
  let w : LinearMap.ker (EvenSupportRank.sumMap K ι) :=
    ⟨Pi.single i 1 - Pi.single j 1, by
      rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply]
      simp only [Pi.sub_apply, sum_sub_distrib, Fintype.sum_pi_single', sub_self]⟩
  have hmap : EvenImage.evenMap data w = 0 := by
    change EvenImage.combination (K := K) data (Pi.single i (1 : K) - Pi.single j 1) = 0
    rw [map_sub]
    simp only [EvenImage.combination, Fintype.linearCombination_apply_single, one_smul, hijdata, sub_self]
  have hw : w = 0 := hinj (hmap.trans (map_zero _).symm)
  have hvalue := congrArg (fun z : LinearMap.ker (EvenSupportRank.sumMap K ι) ↦ z.val i) hw
  have hzero : (1 : K) = 0 := by
    simpa only [w, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero,
      ZeroMemClass.coe_zero, Pi.zero_apply] using hvalue
  exact one_ne_zero hzero

end PaperP1.EvenImageDataRigidity

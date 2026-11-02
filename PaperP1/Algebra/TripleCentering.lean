module

public import PaperP1.Algebra.Centering
public import Mathlib.Tactic.Ring

/-! # Exact heterogeneous three-site centering and incompatible cancellation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleCentering

open Finset PaperP1.Algebra

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

theorem expansion (p : ι → R) (q : Finset ι → R) {x y z : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    centeredCoefficient p q {x, y, z} =
      q {x, y, z} - q {x, y} * p z - q {x, z} * p y - q {y, z} * p x +
      q {x} * p y * p z + q {y} * p x * p z + q {z} * p x * p y - q ∅ * p x * p y * p z := by
  have hpow : ({z} : Finset ι).powerset = {∅, {z}} := by
    ext A
    simp [Finset.subset_singleton_iff]
  rw [centeredCoefficient, sum_powerset_insert (by simp [hxy, hxz])]
  simp_rw [sum_powerset_insert (show y ∉ ({z} : Finset ι) by simp [hyz])]
  simp [hpow, hxy, hxz, hyz,
    Finset.sdiff_singleton_eq_erase, Finset.sdiff_insert, Finset.erase_insert_of_ne]
  ring

theorem normalized (p : ι → R) (q : Finset ι → R) {x y z : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : q ∅ = 1) (hx : q {x} = p x) (hy : q {y} = p y) (hz : q {z} = p z) :
    centeredCoefficient p q {x, y, z} =
      q {x, y, z} - q {x, y} * p z - q {x, z} * p y - q {y, z} * p x + 2 * p x * p y * p z := by
  rw [expansion p q hxy hxz hyz, h0, hx, hy, hz]
  ring

theorem incompatible (p : ι → R) (q : Finset ι → R) {x y z : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : q ∅ = 1) (hx : q {x} = p x) (hy : q {y} = p y) (hz : q {z} = p z)
    (hq : q {x, y, z} = 0) :
    centeredCoefficient p q {x, y, z} = -p x * p y * p z -
      centeredCoefficient p q {x, y} * p z - centeredCoefficient p q {x, z} * p y -
      centeredCoefficient p q {y, z} * p x := by
  rw [normalized p q hxy hxz hyz h0 hx hy hz, hq,
    centeredCoefficient_pair_eq_covariance p q hxy h0 hx hy,
    centeredCoefficient_pair_eq_covariance p q hxz h0 hx hz,
    centeredCoefficient_pair_eq_covariance p q hyz h0 hy hz]
  ring

end PaperP1.TripleCentering

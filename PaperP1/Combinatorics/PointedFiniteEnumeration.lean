module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Option

/-! # A fixed-size actual family can be enumerated with any prescribed anchor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PointedFiniteEnumeration

theorem exists_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hcard : Fintype.card ι = s + 1) (i : ι) :
    ∃ e : Option (Fin s) ≃ ι, e none = i := by
  let e : Option (Fin s) ≃ ι := Fintype.equivOfCardEq (by simpa using hcard.symm)
  exact ⟨e.trans (Equiv.swap (e none) i), by simp⟩

end PaperP1.PointedFiniteEnumeration

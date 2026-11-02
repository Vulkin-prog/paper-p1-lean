/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Wenrong Zou

Minimal adaptation of the option-variable equivalence in
Mathlib/RingTheory/MvPowerSeries/Equiv.lean, commit
9d581dfff2e41de989072ea63abf3daf69311520, blob
29a3a9340ea5d982e0c9af5f3444a9d25c463ca6. This selected correspondence
keeps the project's dependency and disk budget focused on formal series.
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Multivariate series in one additional variable are iterated power series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedPowerSeriesEquiv

open Finset Finsupp MvPowerSeries

variable {σ R : Type*} [CommSemiring R]

def toIterated (f : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n ↦ fun x ↦ f.coeff (x.optionElim n)

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_toIterated (f : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (toIterated f)) = coeff (x.optionElim n) f := by
  rw [toIterated, PowerSeries.coeff_mk]
  exact LinearMap.proj_apply ..

theorem toIterated_monomial (x : Option σ →₀ ℕ) (r : R) :
    toIterated (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) := by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial, coefficient_toIterated, coeff_monomial]
  split_ifs with h1 h2 h3
  · simp [← h1]
  · absurd h2
    rw [← optionElim_apply_none n, h1]
  · replace h1 : ¬y = x.some := fun h ↦ by
      absurd h1
      ext u
      cases u <;> simp_all
    rw [coeff_monomial, ite_eq_right h1]
  · rw [coeff_zero]

theorem toIterated_mul (f g : MvPowerSeries (Option σ) R) :
    toIterated (f * g) = toIterated f * toIterated g := by
  classical
  ext k x
  simp only [coefficient_toIterated, coeff_mul, PowerSeries.coeff_mul, map_sum, sum_sigma']
  refine sum_bij (fun y _ ↦ ⟨(y.1 none, y.2 none), (y.1.some, y.2.some)⟩) ?_ ?_ ?_ ?_
  · intros
    simp_all [Finsupp.ext_iff]
  · intros
    ext t <;> cases t
    all_goals simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨m, n⟩, ⟨u, v⟩⟩ h
    suffices ∃ a b, (a none = m ∧ b none = n) ∧ a.some = u ∧ a + b = optionElim k x ∧
      b.some = v by simpa
    use u.optionElim m, v.optionElim n
    suffices optionElim m u + optionElim n v = optionElim k x by simp_all
    ext t
    cases t <;> simp_all [Finsupp.ext_iff]
  · intros
    simp_all [Finsupp.ext_iff]

def fromIterated (f : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun x ↦ (f.coeff (x none)).coeff x.some

theorem coefficient_fromIterated (f : PowerSeries (MvPowerSeries σ R)) (x : Option σ →₀ ℕ) :
    coeff x (fromIterated f) = (f.coeff (x none)).coeff x.some := rfl

def equiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := toIterated
  invFun := fromIterated
  left_inv _ := by ext; simp [coefficient_fromIterated, coefficient_toIterated]
  right_inv _ := by ext; simp [coefficient_fromIterated, coefficient_toIterated]
  map_mul' := toIterated_mul
  map_add' _ _ := by ext; simp [coefficient_toIterated]

end PaperP1.IteratedPowerSeriesEquiv

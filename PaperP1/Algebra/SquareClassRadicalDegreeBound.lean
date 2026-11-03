module

public import PaperP1.Algebra.IndependentRadicalDegreeBound
public import PaperP1.Algebra.FieldSquareClassMap
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Nat.Log

/-! # The size of an independent family of square classes killed by a finite field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareClassRadicalDegreeBound

open Finset PaperP1.FieldSquareClasses

variable {K E ι : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

omit [CharZero K] in
theorem independent_list (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)))
    (s : List ι) (hs : s.Nodup) : IndependentQuadraticTower.Independent (s.map a) := by
  classical
  intro t ht hne hsq
  obtain ⟨u, hu, rfl⟩ := List.sublist_map_iff.mp ht
  have hu0 : u ≠ [] := by
    intro hz
    exact hne (by rw [hz, List.map_nil])
  have hprod : IsSquare (∏ i ∈ u.toFinset, a i) := by
    rw [List.prod_toFinset a (hs.sublist hu)]
    exact hsq
  have hzero : (∑ i ∈ u.toFinset, ofNonzero (a i) (ha i)) = 0 :=
    (ofNonzero_prod u.toFinset a ha).symm.trans ((ofNonzero_zero_iff _ _).mpr hprod)
  obtain ⟨i, hi⟩ := (List.toFinset_nonempty_iff u).mpr hu0
  have hc := linearIndependent_iff'.mp hli u.toFinset (fun _ ↦ (1 : ZMod 2))
    (by simpa only [one_smul] using hzero) i hi
  exact one_ne_zero hc

theorem power_dvd_degree (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)))
    (A : Finset ι) (hsquare : ∀ i ∈ A, IsSquare (algebraMap K E (a i))) :
    2 ^ A.card ∣ Module.finrank K E := by
  classical
  let s := A.toList.map a
  have hs : IndependentQuadraticTower.Independent s := independent_list a ha hli A.toList A.nodup_toList
  have hall (i : Fin s.length) : IsSquare (algebraMap K E (s.get i)) := by
    have hmem : s.get i ∈ A.toList.map a := List.get_mem s i
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmem
    rw [← heq]
    exact hsquare j (Finset.mem_toList.mp hj)
  choose r hr using hall
  have hroot (i : Fin s.length) : r i ^ 2 = algebraMap K E (s.get i) := by
    simpa only [pow_two] using (hr i).symm
  simpa only [s, List.length_map, Finset.length_toList] using
    IndependentRadicalDegreeBound.power_dvd_degree s hs r hroot

theorem power_le_degree [Module.Finite K E] (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)))
    (A : Finset ι) (hsquare : ∀ i ∈ A, IsSquare (algebraMap K E (a i))) :
    2 ^ A.card ≤ Module.finrank K E := Nat.le_of_dvd Module.finrank_pos (power_dvd_degree a ha hli A hsquare)

theorem card_le_log_degree [Module.Finite K E] (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)))
    (A : Finset ι) (hsquare : ∀ i ∈ A, IsSquare (algebraMap K E (a i))) :
    A.card ≤ Nat.log 2 (Module.finrank K E) :=
  Nat.le_log_of_pow_le (by decide) (power_le_degree a ha hli A hsquare)

end PaperP1.SquareClassRadicalDegreeBound

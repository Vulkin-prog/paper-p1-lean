module

public import PaperP1.Arithmetic.CurveWordMap

/-! # Literal finite supports and the actual binary formal-word space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalWordEncoding

open PaperP1.CurveWordMap

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem encode_apply (I : Finset ℤ) (z : ℤ) : encode I z = if z ∈ I then 1 else 0 := by
  classical
  simp [encode, Finsupp.single_apply, eq_comm]

theorem encode_empty : encode ∅ = 0 := by simp [encode]

theorem encode_support (w : ℤ →₀ ZMod 2) : encode w.support = w := by
  ext z
  rw [encode_apply]
  by_cases hz : z ∈ w.support
  · rw [ite_eq_left hz]
    have hne : w z ≠ 0 := Finsupp.mem_support_iff.mp hz
    have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact ((hbinary (w z)).resolve_left hne).symm
  · rw [ite_eq_right hz]
    exact (Finsupp.notMem_support_iff.mp hz).symm

theorem support_representation (w : Words) : w = (encode w.1.support, encode w.2.support) :=
  Prod.ext (encode_support w.1).symm (encode_support w.2).symm

theorem encode_injective : Function.Injective encode := by
  intro I J h
  apply Finset.ext
  intro z
  have he := congrArg (fun w : ℤ →₀ ZMod 2 ↦ w z) h
  rw [encode_apply, encode_apply] at he
  by_cases hI : z ∈ I <;> by_cases hJ : z ∈ J <;> simp_all

theorem basis_independent {ι : Type*} (V : Submodule (ZMod 2) Words)
    (b : Module.Basis ι (ZMod 2) V) (I J : ι → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i))) (i j : ι) (hij : i ≠ j) :
    PaperP1.BiquadraticWordNorm.Independent (I i) (J i) (I j) (J j) := by
  have hnonempty (k : ι) : (I k, J k) ≠ (∅, ∅) := by
    intro h
    have hI : I k = ∅ := congrArg Prod.fst h
    have hJ : J k = ∅ := congrArg Prod.snd h
    apply b.ne_zero k
    apply Subtype.ext
    rw [hwords, hI, hJ, encode_empty]
    rfl
  have hdistinct : (I i, J i) ≠ (I j, J j) := by
    intro h
    have he := congrArg (fun p : Finset ℤ × Finset ℤ ↦ (encode p.1, encode p.2)) h
    have hb : b i = b j := by
      apply Subtype.ext
      rw [hwords i, hwords j]
      exact he
    exact hij (b.injective hb)
  exact PaperP1.BiquadraticWordNorm.independent_of_distinct (I i) (J i) (I j) (J j)
    (hnonempty i) (hnonempty j) hdistinct

end PaperP1.FormalWordEncoding

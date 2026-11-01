module

public import PaperP1.Arithmetic.OffsetLinePopulation

/-! # The actual shared odd-valuation primes and their unique physical offsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrimeOffsets

open PaperP1.Arithmetic PaperP1.SaturationPrimes PaperP1.OffsetLinePopulation PaperP1.DefectivePredicate
  PaperP1.TruncatedKernelProducts

def Shared {L : ℕ} (H : ℝ) (X : Fin 3 → ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ H < (p : ℝ) ∧
    ∃ v : Fin 3 → Fin (L + 1), ∀ i, p ∈ oddPrimeSupport (value (X i) (v i))

def offset {L : ℕ} {H : ℝ} {X : Fin 3 → ℕ} {p : ℕ} (hp : Shared (L := L) H X p) :
    Fin 3 → Fin (L + 1) := Classical.choose hp.2.2

theorem offset_odd {L : ℕ} {H : ℝ} {X : Fin 3 → ℕ} {p : ℕ} (hp : Shared (L := L) H X p) (i : Fin 3) :
    p ∈ oddPrimeSupport (value (X i) (offset hp i)) := Classical.choose_spec hp.2.2 i

theorem offset_dvd {L : ℕ} {H : ℝ} {X : Fin 3 → ℕ} {p : ℕ} (hp : Shared (L := L) H X p) (i : Fin 3) :
    p ∣ value (X i) (offset hp i) := dvd_of_mem_oddPrimeSupport (offset_odd hp i)

theorem offset_unique {L : ℕ} {H : ℝ} {X : Fin 3 → ℕ} {p : ℕ}
    (hH : ((L + 1 : ℕ) : ℝ) ≤ H) (hp : Shared (L := L) H X p) (v : Fin 3 → Fin (L + 1))
    (hv : ∀ i, p ∈ oddPrimeSupport (value (X i) (v i))) : v = offset hp :=
  odd_offsets_unique H hH hp.1 hp.2.1 X v (offset hp) hv (offset_odd hp)

theorem shared_unique_offset {L : ℕ} {H : ℝ} {X : Fin 3 → ℕ} {p : ℕ}
    (hH : ((L + 1 : ℕ) : ℝ) ≤ H) (hp : Shared (L := L) H X p) :
    ∃! v : Fin 3 → Fin (L + 1), ∀ i, p ∈ oddPrimeSupport (value (X i) (v i)) :=
  ⟨offset hp, offset_odd hp, fun v hv ↦ offset_unique hH hp v hv⟩

theorem shared_iff_occurs_in_each_window {L : ℕ} (H : ℝ) (X : Fin 3 → ℕ) (p : ℕ) :
    Shared (L := L) H X p ↔ Nat.Prime p ∧ H < (p : ℝ) ∧
      ∀ i : Fin 3, ∃ v : Fin (L + 1), p ∈ oddPrimeSupport (value (X i) v) := by
  constructor
  · rintro ⟨hprime, hcut, v, hv⟩
    exact ⟨hprime, hcut, fun i ↦ ⟨v i, hv i⟩⟩
  · rintro ⟨hprime, hcut, hv⟩
    choose v hv using hv
    exact ⟨hprime, hcut, v, hv⟩

end PaperP1.SharedPrimeOffsets

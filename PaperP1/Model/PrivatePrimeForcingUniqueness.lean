module

public import PaperP1.Model.RandomizedPrivatePalmForcing

/-! # A prescribed private word and unchanged nonpivots uniquely determine the prime map -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePrimeForcingUniqueness

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem PaperP1.PrivatePrimeForcing

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem basis_injective (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1) : Function.Injective q := by
  intro i j hij
  by_contra hne
  have h := congrArg (fun p : PrimeUpTo M ↦ valueSystem M v (Pi.single p 1)) hij
  rw [hq i, hq j] at h
  have hc := congrFun h i
  simp [hne] at hc

theorem liftBlock_apply (q : ι → PrimeUpTo M) (hq : Function.Injective q)
    (c : ι → F₂) (i : ι) : liftBlock q c (q i) = c i := by
  classical
  simp [liftBlock, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, hq.eq_iff, smul_eq_mul]

theorem unique_of_preserves (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (ω ω' : SampleSpace M) (hhit : valueSystem M v ω' = word)
    (hout : ∀ p : PrimeUpTo M, (∀ i, p ≠ q i) → ω' p = ω p) :
    ω' = forceWord v q word ω := by
  classical
  have hi := basis_injective v q hq
  let c : ι → F₂ := fun i ↦ ω' (q i) - ω (q i)
  have he : ω' = assemble q ω c := by
    funext p
    by_cases hp : ∃ i, p = q i
    · obtain ⟨i, rfl⟩ := hp
      change ω' (q i) = ω (q i) + liftBlock q c (q i)
      rw [liftBlock_apply q hi]
      dsimp [c]
      abel
    · have hn : ∀ i, p ≠ q i := fun i h ↦ hp ⟨i, h⟩
      rw [hout p hn]
      change ω p = ω p + liftBlock q c p
      simp [liftBlock, Finset.sum_apply, hn]
  have hc : c = word - valueSystem M v ω := (assemble_word_iff v q hq word ω c).mp (by
    rw [← he]
    exact hhit)
  rw [he, hc]
  rfl

theorem randomized_unique {Ξ : Type*} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (F : SampleSpace M → Ξ → SampleSpace M)
    (hhit : ∀ ω ξ, valueSystem M v (F ω ξ) =
      PaperP1.RandomizedPrivatePalmForcing.orientedWord b (g (valueSystem M v ω) ξ))
    (hout : ∀ ω ξ p, (∀ i, p ≠ q i) → F ω ξ p = ω p) (ω : SampleSpace M) (ξ : Ξ) :
    F ω ξ = PaperP1.RandomizedPrivatePalmForcing.force v q b g ω ξ :=
  unique_of_preserves v q hq _ ω (F ω ξ) (hhit ω ξ) (hout ω ξ)

end PaperP1.PrivatePrimeForcingUniqueness

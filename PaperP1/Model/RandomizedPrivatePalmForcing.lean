module

public import PaperP1.Model.PrivatePrimeForcing
public import PaperP1.Probability.FairBinaryMixture

/-! # A fair randomized orientation has the full Palm law on a fully private word

Every original raw source coordinate has its private prime basis vector.
This is the essential hypothesis: a merely unforced defective anchor
does not give a uniform source word after the background is fixed.
The auxiliary law is an arbitrary independent finite probability.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivatePalmForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing PaperP1.UniformFubini PaperP1.Probability PaperP1.Algebra

local instance randomizedPrivatePalmDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {M : ℕ} {ι Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ξ]

def orientedWord (b : ι → F₂) (s : F₂) : ι → F₂ := fun i ↦ b i + s

def force (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂)
    (g : (ι → F₂) → Ξ → F₂) (ω : SampleSpace M) (ξ : Ξ) : SampleSpace M :=
  forceWord v q (orientedWord b (g (valueSystem M v ω) ξ)) ω

omit [Fintype Ξ] in
theorem hits (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (ω : SampleSpace M) (ξ : Ξ) :
    ∃ s : F₂, valueSystem M v (force v q b g ω ξ) = orientedWord b s :=
  ⟨g (valueSystem M v ω) ξ, forceWord_hits v q hq _ ω⟩

omit [Fintype Ξ] in
theorem force_assemble (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (r : SampleSpace M) (c : ι → F₂) (ξ : Ξ) :
    force v q b g (assemble q r c) ξ =
      assemble q r (orientedWord b (g (valueSystem M v r + c) ξ) - valueSystem M v r) := by
  rw [force, forceWord_assemble v q hq]
  simp only [assemble, map_add, value_liftBlock v q hq]

theorem chart_mixture (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (P : FiniteProbability Ξ) (g : (ι → F₂) → Ξ → F₂)
    (hfair : average (fun u : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ))
    (f : SampleSpace M → ℝ) (r : SampleSpace M) :
    average (fun c : ι → F₂ ↦ finiteExpectation P.weight (fun ξ ↦ f (force v q b g (assemble q r c) ξ))) =
      (f (forceWord v q b r) + f (forceWord v q (orientedWord b 1) r)) / 2 := by
  let H : F₂ → ℝ := fun s ↦ f (assemble q r (orientedWord b s - valueSystem M v r))
  have hshift : average (fun c : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g (valueSystem M v r + c) ξ))) = (1 / 2 : ℝ) :=
    (UniformFubini.equiv (Equiv.addLeft (valueSystem M v r))
      (fun u : ι → F₂ ↦ finiteExpectation P.weight
        (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ)))).trans hfair
  calc
    _ = average (fun c : ι → F₂ ↦ finiteExpectation P.weight
        (fun ξ ↦ H (g (valueSystem M v r + c) ξ))) := by
      apply UniformFubini.congr
      intro c
      apply congrArg (finiteExpectation P.weight)
      funext ξ
      rw [force_assemble v q hq]
    _ = (H 0 + H 1) / 2 := PaperP1.FairBinaryMixture.nested P _ hshift H
    _ = _ := by
      dsimp only [H]
      rw [show orientedWord b 0 = b from funext (fun i ↦ add_zero (b i))]
      rfl

theorem uniform_mixture (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (P : FiniteProbability Ξ) (g : (ι → F₂) → Ξ → F₂)
    (hfair : average (fun u : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ))
    (f : SampleSpace M → ℝ) :
    average (fun ω : SampleSpace M ↦ finiteExpectation P.weight (fun ξ ↦ f (force v q b g ω ξ))) =
      (average (fun ω : SampleSpace M ↦ f (forceWord v q b ω)) +
        average (fun ω : SampleSpace M ↦ f (forceWord v q (orientedWord b 1) ω))) / 2 := by
  have ha := uniform_assemble_expectation q
    (fun ω : SampleSpace M ↦ finiteExpectation P.weight (fun ξ ↦ f (force v q b g ω ξ)))
  calc
    _ = average (fun r : SampleSpace M ↦ average (fun c : ι → F₂ ↦ finiteExpectation P.weight
        (fun ξ ↦ f (force v q b g (assemble q r c) ξ)))) := ha.symm
    _ = average (fun r : SampleSpace M ↦
        (f (forceWord v q b r) + f (forceWord v q (orientedWord b 1) r)) / 2) :=
      UniformFubini.congr (chart_mixture v q hq b P g hfair f)
    _ = _ := by
      have he (r : SampleSpace M) :
          (f (forceWord v q b r) + f (forceWord v q (orientedWord b 1) r)) / 2 =
          (1 / 2 : ℝ) * f (forceWord v q b r) + (1 / 2 : ℝ) * f (forceWord v q (orientedWord b 1) r) := by ring
      simp_rw [he]
      simp only [average, finiteExpectation_add, finiteExpectation_const_mul]
      ring

omit [Fintype ι] [DecidableEq ι] in
theorem orbit_iff (b u : ι → F₂) :
    PaperP1.BinaryForcingFlip.orbit b u ↔ u = b ∨ u = orientedWord b 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have hc : ∀ z : F₂, z = 0 ∨ z = 1 := by decide
    rcases hc s with rfl | rfl
    · exact Or.inl (by simpa only [add_zero] using hs)
    · exact Or.inr hs
  · rintro (h | h)
    · exact ⟨0, by simpa only [add_zero] using h⟩
    · exact ⟨1, h⟩

omit [Fintype ι] [DecidableEq ι] in
theorem orientedWord_ne [Nonempty ι] (b : ι → F₂) : b ≠ orientedWord b 1 := by
  intro h
  let i : ι := Classical.choice inferInstance
  have hi : b i = b i + 1 := congrFun h i
  exact one_ne_zero (add_left_cancel (hi.symm.trans (add_zero (b i)).symm))

omit [DecidableEq ι] in
theorem indicator_split [Nonempty ι] (b u : ι → F₂) (r : ℝ) :
    (if PaperP1.BinaryForcingFlip.orbit b u then r else 0) =
      (if u = b then r else 0) + (if u = orientedWord b 1 then r else 0) := by
  by_cases h₀ : u = b
  · have h₁ : u ≠ orientedWord b 1 := by simpa only [h₀] using orientedWord_ne b
    have ho := (orbit_iff b u).mpr (Or.inl h₀)
    rw [ite_eq_left ho, ite_eq_left h₀, ite_eq_right h₁, add_zero]
  · by_cases h₁ : u = orientedWord b 1
    · have ho := (orbit_iff b u).mpr (Or.inr h₁)
      rw [ite_eq_left ho, ite_eq_right h₀, ite_eq_left h₁, zero_add]
    · have ho : ¬PaperP1.BinaryForcingFlip.orbit b u := by rw [orbit_iff]; exact not_or.mpr ⟨h₀, h₁⟩
      rw [ite_eq_right ho, ite_eq_right h₀, ite_eq_right h₁, add_zero]

theorem uniform_conditional [Nonempty ι] (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (P : FiniteProbability Ξ) (g : (ι → F₂) → Ξ → F₂)
    (hfair : average (fun u : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ))
    (f : SampleSpace M → ℝ) :
    average (fun ω : SampleSpace M ↦ finiteExpectation P.weight (fun ξ ↦ f (force v q b g ω ξ))) =
      average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b (valueSystem M v ω)
        then f ω else 0) / (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  rw [uniform_mixture v q hq b P g hfair f, uniform_conditional_expectation v q hq b f,
    uniform_conditional_expectation v q hq (orientedWord b 1) f, ← add_div, div_div]
  have hsum :
      average (fun ω : SampleSpace M ↦ if valueSystem M v ω = b then f ω else 0) +
        average (fun ω : SampleSpace M ↦ if valueSystem M v ω = orientedWord b 1 then f ω else 0) =
      average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b (valueSystem M v ω)
        then f ω else 0) := by
    have he := UniformFubini.congr (fun ω : SampleSpace M ↦ (indicator_split b (valueSystem M v ω) (f ω)).symm)
    simpa only [average, finiteExpectation_add] using he
  rw [hsum]
  congr 1
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hp : (2 ^ Fintype.card ι : ℝ) = 2 * (2 ^ (Fintype.card ι - 1) : ℝ) := by
    conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega, pow_succ]
    ring
  rw [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_ofNat, hp, mul_inv_rev]
  field_simp

omit [Fintype Ξ] [DecidableEq ι] in
theorem preserves_nonpivot (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂)
    (g : (ι → F₂) → Ξ → F₂) (ω : SampleSpace M) (ξ : Ξ) (p : PrimeUpTo M)
    (hp : ∀ i, p ≠ q i) : force v q b g ω ξ p = ω p :=
  forceWord_preserves_nonpivot v q _ ω p hp

theorem weighted_conditional [Nonempty ι] (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (P : FiniteProbability Ξ) (g : (ι → F₂) → Ξ → F₂)
    (hfair : average (fun u : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ))
    (f : SampleSpace M → ℝ) :
    (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ *
      average (fun ω : SampleSpace M ↦ finiteExpectation P.weight (fun ξ ↦ f (force v q b g ω ξ))) =
      average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b (valueSystem M v ω)
        then f ω else 0) := by
  have h := uniform_conditional v q hq b P g hfair f
  have hd : (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ ≠ 0 := by positivity
  simpa only [mul_comm] using (eq_div_iff hd).mp h

theorem event_probability [Nonempty ι] (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ i, valueSystem M v (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (P : FiniteProbability Ξ) (g : (ι → F₂) → Ξ → F₂)
    (hfair : average (fun u : ι → F₂ ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ)) :
    average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b (valueSystem M v ω)
      then (1 : ℝ) else 0) = (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  have h := weighted_conditional v q hq b P g hfair (fun _ ↦ 1)
  have he : finiteExpectation P.weight (fun _ : Ξ ↦ (1 : ℝ)) = 1 := by
    rw [finiteExpectation_const, P.total_weight, one_mul]
  rw [he, UniformFubini.constant, mul_one] at h
  exact h.symm

end PaperP1.RandomizedPrivatePalmForcing

module

public import PaperP1.Probability.PositionalDeterministicMap
public import PaperP1.Probability.PositionalPoissonJump

/-! # Additive configuration pushforwards preserve convolution and exponentials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalAdditivePushforward

open Finset UniformSpace PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalDeterministicMap

variable {ι κ : Type*}

def finiteMap (f : Configuration ι →+ Configuration κ) : FieldLaw ι →+* FieldLaw κ :=
  AddMonoidAlgebra.mapDomainRingHom ℝ f

theorem ofFinite_smul (r : ℝ) (ν : FieldLaw ι) : ofFinite (r • ν) = r • ofFinite ν := by
  change ((r • ν : FieldLaw ι) : Space ι) = r • (ν : Space ι)
  exact Completion.coe_smul r ν

theorem ofFinite_single (v : Configuration ι) (r : ℝ) :
    ofFinite (AddMonoidAlgebra.single v r) = r • ofFinite (atom v) := by
  have hs : AddMonoidAlgebra.single v r = r • (atom v : FieldLaw ι) := by
    simp [atom]
  rw [hs, ofFinite_smul]

theorem push_ofFinite (f : Configuration ι →+ Configuration κ) (ν : FieldLaw ι) :
    push f (ofFinite ν) = ofFinite (finiteMap f ν) := by
  classical
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  rw [Finsupp.sum, map_sum, map_sum]
  have hf : finiteMap f ν = ∑ v ∈ ν.coeff.support,
      AddMonoidAlgebra.single (f v) (ν.coeff v) := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
    simp [finiteMap, Finsupp.sum]
  rw [hf, map_sum]
  apply sum_congr rfl
  intro v _
  rw [ofFinite_single, ofFinite_single, map_smul, push_atom]

theorem push_one (f : Configuration ι →+ Configuration κ) : push f 1 = 1 := by
  rw [← map_one (ofFinite : FieldLaw ι →+* Space ι), push_ofFinite, map_one, map_one]

theorem push_mul (f : Configuration ι →+ Configuration κ) (ν μ : Space ι) :
    push f (ν * μ) = push f ν * push f μ := by
  induction ν, μ using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih ν μ =>
    change push f (ofFinite ν * ofFinite μ) = push f (ofFinite ν) * push f (ofFinite μ)
    rw [← map_mul, push_ofFinite, push_ofFinite, push_ofFinite, map_mul, map_mul]

def pushHom (f : Configuration ι →+ Configuration κ) : Space ι →+* Space κ where
  toFun := push f
  map_zero' := map_zero (push f)
  map_add' := map_add (push f)
  map_one' := push_one f
  map_mul' := push_mul f

theorem push_exp (f : Configuration ι →+ Configuration κ) (ν : Space ι) :
    push f (NormedSpace.exp ν) = NormedSpace.exp (push f ν) :=
  NormedSpace.map_exp (pushHom f) (push f).continuous ν

theorem push_jump (f : Configuration ι →+ Configuration κ) (v : Configuration ι) (μ : ℝ) :
    push f (PositionalPoissonJump.jump v μ) = PositionalPoissonJump.jump (f v) μ := by
  rw [PositionalPoissonJump.jump, push_exp, map_smul, map_sub, push_atom, push_one,
    PositionalPoissonJump.jump]

end PaperP1.PositionalAdditivePushforward

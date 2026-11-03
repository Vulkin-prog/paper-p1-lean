module

public import PaperP1.Asymptotics.PrimitiveSharpMassUnderInputs
public import PaperP1.Asymptotics.ConnectedTriplePositiveUnderInputs
public import PaperP1.Asymptotics.DirectCrossingSeedFamiliesUnderInputs
public import PaperP1.Asymptotics.LowTwoPairSeedsUnderInputs
public import PaperP1.Asymptotics.DensePairCrossingFamiliesUnderInputs
public import PaperP1.Model.PrimitiveConnectedGeometry

/-! # Finite ordinary geometric inputs for the sharp connected seed reduction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpConnectedSeedParameters

structure Parameters (R : ℕ) where
  primitive : Fin (R + 1) → DensePrimitiveTripleMassUnderInputs.Parameters
  triple : FinitePairDeficitInputs.Parameters
  lowPair : FinitePairDeficitInputs.Parameters
  dense : DensePrimitiveTripleMassUnderInputs.Parameters
  densePair : FinitePairDeficitInputs.Parameters
  direct : Fin (R + 1) → DensePrimitiveTripleMassUnderInputs.Parameters
  directPair : Fin (R + 1) → FinitePairDeficitInputs.Parameters

structure Hypotheses {R : ℕ} (p : Parameters R) (ε : ℝ) : Prop where
  primitive : ∀ i, DensePrimitiveTripleMassUnderInputs.Hypotheses (p.primitive i)
  triple : FinitePairDeficitInputs.Hypotheses p.triple (GeneralGraphHostCount.sizeCap (ε / 8192))
  lowPair : FinitePairDeficitInputs.Hypotheses p.lowPair (GeneralGraphHostCount.sizeCap (ε / 32768))
  dense : DensePrimitiveTripleMassUnderInputs.Hypotheses p.dense
  densePair : FinitePairDeficitInputs.Hypotheses p.densePair (GeneralGraphHostCount.sizeCap (ε / 16384))
  direct : ∀ i, DensePrimitiveTripleMassUnderInputs.Hypotheses (p.direct i)
  directPair : ∀ i, FinitePairDeficitInputs.Hypotheses (p.directPair i)
    (GeneralGraphHostCount.sizeCap (ε / 16384))

end PaperP1.SharpConnectedSeedParameters

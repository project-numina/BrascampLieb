import Mathlib.Analysis.InnerProductSpace.PiL2
import BrascampLieb.ToMathlib.LinearAlgebra.Dimension.Constructions

lemma finrank_span_image' {ι 𝕜 M : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] (b : OrthonormalBasis ι 𝕜 M) (I : Finset ι) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (b '' I)) = I.card :=
  finrank_span_image b.toBasis I

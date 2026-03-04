import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank

lemma LinearIsometryEquiv.finrank_map_eq {R E1 E2 : Type*} [Semiring R]
    [SeminormedAddCommGroup E1] [SeminormedAddCommGroup E2]
    [Module R E1] [Module R E2] (e : E1 ≃ₗᵢ[R] E2) (S : Submodule R E1) :
    Module.finrank R (S.map (e )) = Module.finrank R S := -- e : E1 →ₗ[R] E2
  e.toLinearEquiv.finrank_map_eq S

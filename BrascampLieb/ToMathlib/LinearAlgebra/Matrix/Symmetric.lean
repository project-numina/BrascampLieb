import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

lemma Matrix.IsSymm.mulVec_dotProduct_comm {n R : Type*} [Fintype n] [CommRing R]
    {A : Matrix n n R} (hA : A.IsSymm) (x y : n → R) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (A.mulVec y) := by
  classical
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]

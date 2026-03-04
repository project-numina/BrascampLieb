import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- Merged?
lemma Matrix.IsSymm.adjugate {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    {A : Matrix n n R}
    (hA : A.IsSymm) : A.adjugate.IsSymm := by
  rw [IsSymm, adjugate_transpose, hA.eq]

lemma Matrix.IsSymm.inv {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] {A : Matrix n n R}
    (hA : A.IsSymm) : A⁻¹.IsSymm := by
  rw [Matrix.inv_def]
  exact hA.adjugate.smul _

lemma Matrix.IsSymm.mulVec_dotProduct_comm {n R : Type*} [Fintype n] [CommRing R]
    {A : Matrix n n R} (hA : A.IsSymm) (x y : n → R) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (A.mulVec y) := by
  classical
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]

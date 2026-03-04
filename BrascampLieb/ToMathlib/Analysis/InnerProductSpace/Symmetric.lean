import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace LinearMap

lemma isSymmetric_iff_Hermitian {ι 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ (T.toMatrixOrthonormal b).IsHermitian := by
  rw [isSymmetric_iff_isSelfAdjoint, Matrix.IsHermitian, isSelfAdjoint_iff]
  refine ⟨fun h ↦ by simpa [h, eq_comm] using map_star (toMatrixOrthonormal b) T, fun h ↦ ?_⟩
  have h1 := map_star (toMatrixOrthonormal b).symm (T.toMatrixOrthonormal b)
  rwa [(((toMatrixOrthonormal b) T).star_eq_conjTranspose ▸ h : star _ = _),
    (toMatrixOrthonormal b).symm_apply_apply, eq_comm] at h1

lemma IsSymmetric.charpoly_eq {𝕜 E : Type*} [RCLike 𝕜] {n}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (hT.eigenvalues hn i : 𝕜)) := by
  rw [← charpoly_toMatrix T (hT.eigenvectorBasis hn).toBasis]
  convert Matrix.charpoly_diagonal (fun i ↦ (RCLike.ofReal <| hT.eigenvalues hn i))
  ext i j
  simp +contextual [toMatrix_apply, Matrix.diagonal_apply, ← RCLike.ofReal_alg]

lemma IsSymmetric.roots_charpoly_eq_eigenvalues {𝕜 E : Type*} [RCLike 𝕜] {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly.roots = Finset.univ.val.map (fun i ↦ RCLike.ofReal (hT.eigenvalues hn i)) := by
  rw [hT.charpoly_eq hn, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

attribute [local grind .] LinearMap.IsSymmetric.eigenvalues_antitone List.sortedGE_ofFn_iff in
lemma IsSymmetric.eigenvlaues_linearIsometryEquiv_conj {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) (hn' : Module.finrank 𝕜 F = n)
    {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) (f : E ≃ₗᵢ[𝕜] F) : hT.eigenvalues hn =
    ((LinearMap.isSymmetric_linearIsometryEquiv_conj_iff T f).mpr hT).eigenvalues hn' := by
  set hT' := (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff T f).mpr hT with hT'_symm_def
  refine List.ofFn_injective <| List.Perm.eq_of_sortedGE (by grind) (by grind) ?_
  convert congr(Multiset.map RCLike.re $(hT.roots_charpoly_eq_eigenvalues hn ▸
    f.toLinearEquiv.charpoly_conj T ▸ hT'.roots_charpoly_eq_eigenvalues hn'))
  simp [Function.comp_def]

lemma IsSymmetric.toMatrix_eigenvectorBasis_diagonal {E 𝕜 : Type*} {n} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n)
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    LinearMap.toMatrix (hT.eigenvectorBasis hn).toBasis (hT.eigenvectorBasis hn).toBasis T =
    Matrix.diagonal (RCLike.ofReal ∘ (hT.eigenvalues hn)) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.diagonal, Matrix.of_apply]
  split_ifs with hij <;> simp [RCLike.real_smul_eq_coe_mul, hij]

lemma IsSymmetric.det_eq_prod_eigenvalues {E 𝕜 : Type*} {n} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n)
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.det = ∏ i, hT.eigenvalues hn i := by
  simp [← LinearMap.det_toMatrix (hT.eigenvectorBasis hn).toBasis,
    hT.toMatrix_eigenvectorBasis_diagonal]

end LinearMap

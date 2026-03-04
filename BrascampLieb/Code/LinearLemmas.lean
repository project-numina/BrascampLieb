import BrascampLieb.Code.Defs
import BrascampLieb.ToMathlib.Analysis.InnerProductSpace.GramMatrix
import BrascampLieb.ToMathlib.LinearAlgebra.Matrix.Hermitian
import BrascampLieb.ToMathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Matrix.LDL


/-! ## Section 6: Choleski and Hadamard Determinant Bounds -/

namespace LinearMap

open Matrix

open InnerProductSpace in
/--
Choleski determinant bound (Lemma lem:Choleski in blueprint).
For a positive semidefinite symmetric operator Q and a basis (ε₁, ..., εₐ),
det(Q) det(Gram Matrix of ε₁, ..., εₐ) ≤ ∏ₖ inner(Q εₖ, εₖ)⟨Q εₖ, εₖ⟩
The proof requires:
1. For orthonormal basis, use Choleski decomposition Q = L* L
2. For general basis, use Gram-Schmidt to relate to orthonormal case
3. The wedge product norm captures the volume distortion
-/
lemma choleski_det_bound₁ {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {Q : E →ₗ[ℝ] E} (hQ : Q.IsPositive)
    (v : Fin n → E) (hv : Orthonormal ℝ v) : Q.det ≤ ∏ i, inner ℝ (Q (v i)) (v i) :=
  if hQ1 : Q.det = 0 then hQ1 ▸ Finset.prod_nonneg fun _ _ ↦ hQ.inner_nonneg_left _ else by
  by_cases hd1 : n = 0
  · rw [Q.det_eq_one_of_finrank_eq_zero (hn ▸ hd1), @Finset.prod_of_isEmpty _ _ _ _
      (by simp [hd1, Fin.isEmpty]) Finset.univ]
  let b : OrthonormalBasis (Fin n) ℝ E := OrthonormalBasis.mk hv <|
    hv.linearIndependent.span_eq_top_of_card_eq_finrank' (hn ▸ Fintype.card_fin n)|>.symm.le
  let M := LinearMap.toMatrix b.toBasis b.toBasis Q
  have hM1 : M.PosDef := (LinearMap.posSemidef_toMatrix_iff b |>.2 hQ).posDef_iff_isUnit.2
    (M.isUnit_iff_isUnit_det.2 (Q.det_toMatrix b.toBasis ▸
      lt_of_le_of_ne hQ.det_nonneg (Ne.symm hQ1)).ne'.isUnit)
  letI inst1 := M.transpose.toNormedAddCommGroup hM1.transpose
  letI inst2 := M.transpose.toInnerProductSpace hM1.transpose.posSemidef
  have h_gs_tri' (k i : Fin n) (hk : k < i) : gramSchmidt ℝ (Pi.basisFun ℝ (Fin n)) k i = 0 :=
    @gramSchmidt_triangular ℝ (Fin n → ℝ) _ inst1 inst2 (Fin n) _ _ _ k i hk (Pi.basisFun ℝ (Fin n))
  have h_ei_eq (i)
    :
    1 =
    gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin n))) i i +
      ∑ x ∈ Finset.Iio i,
        ⟪gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin n))) x, Pi.single i 1⟫_ℝ /
            ( @norm (Fin n → ℝ) inst1.toNorm (gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin n))) x)) ^ 2 *
          gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin n))) x i
          := by
    simpa using congrFun (@gramSchmidt_def'' ℝ (Fin n → ℝ) _ inst1 inst2 (Fin n)
      _ _ _ (Pi.basisFun ℝ (Fin n)) i) i
  have h_det_L : (LDL.lower hM1).det = 1 := by
    simp only [LDL.lower, det_nonsing_inv]
    convert Ring.inverse_one ℝ using 2
    rw [det_of_lowerTriangular _ (fun _ _ ↦ LDL.lowerInv_triangular hM1)]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    specialize h_ei_eq i
    rwa [Finset.sum_eq_zero (fun k hk ↦ by simp [h_gs_tri' k i (Finset.mem_Iio.mp hk)]),
      add_zero, eq_comm] at h_ei_eq
  rw [show Q.det = M.det from (Q.det_toMatrix b.toBasis).symm]
  simp only [← congr(det $(LDL.lower_conj_diag hM1)), conjTranspose_eq_transpose_of_trivial,
      det_mul, h_det_L, one_mul, det_transpose, mul_one, LDL.diag, det_diagonal]
  refine le_of_le_of_eq (Finset.prod_le_prod (fun i _ => le_of_lt ?_) (fun i _ => ?_))
    (Finset.prod_congr rfl fun i _ ↦ by simp [M, LinearMap.toMatrix_apply,
      OrthonormalBasis.repr_apply_apply, b, real_inner_comm] : ∏ i, M i i = ∏ i, ⟪Q (v i), v i⟫_ℝ)
  · simpa [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using
      hM1.re_dotProduct_pos <| (LDL.lowerInv hM1).linearIndependent_rows_of_invertible.ne_zero i
  · let w := LDL.lowerInv hM1 i
    let e : Fin n → ℝ := Pi.single i 1
    let p := Pi.single i 1 - w
    refine le_of_le_of_eq (by
      nth_rw 1 [dotProduct_comm _ p, ← RCLike.re_to_real (x := p ⬝ᵥ _), ← star_trivial p]
      grw [← hM1.posSemidef.re_dotProduct_nonneg p, add_zero] : _ ≤ _ + (M.mulVec p) ⬝ᵥ p) ?_
    simp only [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp, star_trivial]
    rw [← M.col_apply, ← dotProduct_single_one (M.col i) i, ← one_smul ℝᵐᵒᵖ (M.col i),
      ← MulOpposite.op_one, ← M.mulVec_single i 1, show Pi.single i 1 = w + p by simp [p],
      M.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, add_assoc, add_right_inj,
      ← add_assoc, right_eq_add, hM1.isHermitian.mulVec_dotProduct_comm_of_trivial w p,
      dotProduct_comm _ w, ← two_nsmul, smul_eq_zero_iff_right (by omega), M.mulVec_sub,
      dotProduct_sub, sub_eq_zero]
    have h_rhs : w ⬝ᵥ M.mulVec w = (M.mulVec w) i + ∑ k ∈ Finset.Iio i, w k * (M.mulVec w) k := by
      simpa [dotProduct, Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i), show w i = 1 by
        convert h_ei_eq i |>.symm; exact left_eq_add.2 (Finset.sum_eq_zero fun k hk ↦ by
        simp [h_gs_tri' k i (Finset.mem_Iio.mp hk)]), ← Finset.Iio_union_Ioi,
        Finset.sum_union (Finset.disjoint_Ioi_Iio i).symm, add_comm (M.mulVec w i)] using
        Finset.sum_eq_zero fun k hk ↦ by
        simp +zetaDelta [LDL.lowerInv_triangular hM1 (Finset.mem_Ioi.1 hk)]
    have H (j) (hj : j < n) (h : (⟨j, hj⟩ : Fin n) < i) : (M.mulVec w) ⟨j, hj⟩ = 0 := by
      induction j using Nat.strong_induction_on with
      | _ m ih =>
        set mF : Fin n := ⟨m, hj⟩ with mF_eq
        set f := fun x ↦ LDL.lowerInv hM1 mF x * M.mulVec w x with f_def
        have h_GS_diag : (LDL.lowerInv hM1 ⟨m, hj⟩) ⟨m, hj⟩ = 1 := by
          convert (h_ei_eq ⟨m, hj⟩).symm
          refine left_eq_add.2 (Finset.sum_eq_zero fun k hk' ↦ ?_)
          rw [h_gs_tri' k ⟨m, hj⟩ (Finset.mem_Iio.mp hk'), mul_zero]
        nth_rw 1 [← one_mul (M.mulVec _ _), ← h_GS_diag, ← add_zero (_ * _),
          ← (Finset.Iio mF).sum_eq_zero (f := f) (fun l hl ↦ ih l
            (by simpa using Finset.mem_Iio.1 hl) l.2 (lt_trans (Finset.mem_Iio.1 hl) h) ▸
            mul_zero (LDL.lowerInv hM1 mF l)),
          ← add_zero (_ + _), ← (Finset.Ioi mF).sum_eq_zero (f := f) (fun l hl ↦
            LDL.lowerInv_triangular hM1 (Finset.mem_Ioi.mp hl) ▸ zero_mul (M.mulVec w l)),
            add_assoc, ← Finset.sum_union (.symm <| Finset.disjoint_Ioi_Iio mF),
            Finset.Iio_union_Ioi,
          ← Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ ⟨m, hj⟩) f, ← dotProduct.eq_1]
        simpa [EuclideanSpace.inner_toLp_toLp, hM1.isHermitian.toSymm_of_trivial.eq,
            dotProduct_comm,] using LDL.lowerInv_orthogonal hM1 (ne_of_lt h)
    rw [h_rhs, Finset.sum_eq_zero (fun k hk ↦ H k _ (Finset.mem_Iio.1 hk) ▸ mul_zero (w k)),
      add_zero, ← dotProduct_single_one (M.mulVec w) i,
      hM1.isHermitian.mulVec_dotProduct_comm_of_trivial]

open Module

lemma choleski_det_bound {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {Q : E →ₗ[ℝ] E} (hQ : Q.IsPositive)
    (b : Fin n → E) :
    Q.det * (gram ℝ b).det ≤ ∏ i, inner ℝ (Q (b i)) (b i) := by
  if hn' : n = 0 then simp [det_eq_one_of_finrank_eq_zero (hn ▸ hn'),
      ← Fin.prod_congr' (fun i ↦ inner ℝ (Q (b i)) (b i)) hn'.symm,
      (gram ℝ b).det_eq_one_of_card_eq_zero (hn' ▸ Fintype.card_fin n)] else
  refine (Classical.em (LinearIndependent ℝ b)).casesOn (fun hb ↦ ?_) <| fun h ↦ by
    convert (Finset.prod_nonneg (f := fun i ↦ inner ℝ (Q (b i)) (b i))
      (fun _ _ ↦ hQ.inner_nonneg_left _))
    obtain ⟨i, hi⟩ := by simpa [← posDef_gram_iff_linearIndependent,
      IsHermitian.posDef_iff_eigenvalues_pos (isHermitian_gram ..)] using h
    simp [(isHermitian_gram ℝ b).det_eq_prod_eigenvalues, Finset.prod_eq_zero (Finset.mem_univ i)
      (by simpa using eq_of_le_of_ge hi (PosSemidef.eigenvalues_nonneg (posSemidef_gram ℝ b) i))]
  haveI : Nonempty (Fin n) := ⟨0, Nat.pos_of_ne_zero hn'⟩
  let obasis : OrthonormalBasis (Fin n) ℝ E := hn ▸ stdOrthonormalBasis ℝ E
  let A := obasis.toBasis.toMatrix b
  let Q_mat := toMatrix obasis.toBasis obasis.toBasis Q
  have hAQA_psd := conjTranspose_eq_transpose_of_trivial (obasis.toBasis.toMatrix b) ▸
    ((posSemidef_toMatrix_iff obasis).2 hQ).conjTranspose_mul_mul_same _
  rw [gram_eq_conj_mul b (o := obasis.toBasis) (by simp), det_mul, det_transpose, ← mul_assoc,
    mul_comm Q.det]
  nth_rw 1 [← det_toMatrix obasis.toBasis Q, ← det_transpose, ← det_mul, ← det_mul]
  refine le_of_le_of_eq (b := ∏ i, (Aᵀ * Q_mat * A) i i) (if h : (Aᵀ * Q_mat * A).det = 0 then
    h ▸ Finset.prod_nonneg fun i _ ↦ hAQA_psd.diag_nonneg else ?_) <|
    Finset.prod_congr rfl fun i _ ↦ ?_
  · nth_rw 1 [← toMatrix_toLin obasis.toBasis obasis.toBasis (Aᵀ * Q_mat * A), det_toMatrix]
    refine le_of_le_of_eq (@choleski_det_bound₁ E n _ _ hn _ ((Aᵀ * Q_mat * A).toLin obasis.toBasis
      obasis.toBasis) ((posSemidef_toMatrix_iff obasis).1 <| by simpa) _ obasis.orthonormal) ?_
    exact Finset.prod_congr rfl fun i _ ↦ by
      simp [real_inner_comm, ← toMatrixOrthonormal_apply_apply]
  · rw [← Basis.sum_toMatrix_smul_self obasis.toBasis b i]
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      mul_apply, transpose_apply, Real.ringHom_apply, OrthonormalBasis.coe_toBasis]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Q_mat, toMatrix_apply, OrthonormalBasis.repr_apply_apply, mul_comm, hQ.1 _ _, A]

/-! ## Section 7: Essential Rank Geometric Characterization -/

open RCLike in
/--
Essential rank geometric characterization (Lemma lem:essential_rank_eq in blueprint).
The α-essential rank of ℓ restricted to W equals the minimum dimension of a subspace E
such that the image of the unit ball ℓ(B₁^W) is contained in the α-neighborhood of E.
This bridges the SVD-based definition with the geometric covering property needed
for the greedy construction.
-/
lemma EssRank_eq_geometric {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} {n}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hn : Module.finrank 𝕜 E = n) [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (α : NNReal) (ℓ : E →ₗ[𝕜] F) :
    ℓ.EssentialRank hn α = sInf {d | ∃ (S : Submodule 𝕜 F), Module.finrank 𝕜 S = d ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ S, ‖ℓ x - y‖ ≤ α} := by
  have hℓℓ_pos := ℓ.isPositive_adjoint_comp_self
  have hℓℓ_symm := hℓℓ_pos.isSymmetric
  let basis := hℓℓ_symm.eigenvectorBasis hn
  let eigs := hℓℓ_symm.eigenvalues hn
  let S' : Submodule 𝕜 F :=
    Submodule.span 𝕜 (Set.range (fun i : ℓ.EssRankAux hn α => ℓ (basis i)))
  refine le_antisymm (le_csInf ⟨_, ⊤, finrank_top _ F, fun x _ ↦ ⟨ℓ x, Submodule.mem_top, by simp⟩⟩
    <| fun d ⟨S, hS_rank, hS_cover⟩ ↦ hS_rank ▸ by_contra fun h_lt ↦ ?_) <| Nat.sInf_le
    ⟨S', ⟨finrank_span_eq_card (ℓ.EssRankAux_apply_lindep hn α)|>.trans (Eq.trans
    (Fintype.card_coe _) <| EssentialRank_eq ..), fun x hx_norm ↦
    ⟨∑ i : (ℓ.EssRankAux hn α), inner 𝕜 (basis i.val) x • ℓ (basis i.val), Submodule.sum_mem _
    fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp⟩), ?_⟩⟩⟩
  · let interSub : Submodule 𝕜 F := S' ⊓ Sᗮ
    let supSub : Submodule 𝕜 F := S' ⊔ Sᗮ
    have h_dim_inter_pos : 0 < Module.finrank 𝕜 interSub :=
        (tsub_pos_iff_not_le.2 h_lt).trans_le <| by
      rw [EssentialRank_eq, ← Fintype.card_coe,
        ← finrank_span_eq_card (ℓ.EssRankAux_apply_lindep hn α)]
      grind [S.finrank_add_finrank_orthogonal, supSub.finrank_le,
        S'.finrank_sup_add_finrank_inf_eq Sᗮ]
    obtain ⟨w, hw1, hw2⟩ := interSub.exists_mem_ne_zero_of_ne_bot <| fun h ↦
      h_dim_inter_pos.ne' (h ▸ finrank_bot _ _)
    let c : (ℓ.EssRankAux hn α) → 𝕜 := fun i => inner 𝕜 (ℓ (basis i.val)) w / (eigs i : 𝕜)
    let x : E := ∑ i : (ℓ.EssRankAux hn α), c i • basis i.val
    have hx : ℓ x = w := by
      simp only [x, map_sum, map_smul]
      have h_inner_match (j : ℓ.EssRankAux hn α) : inner 𝕜 (∑ i : ℓ.EssRankAux hn α,
        c i • ℓ (basis ↑i)) (ℓ (basis ↑j)) = inner 𝕜 w (ℓ (basis ↑j)) := by
        rw [sum_inner, Finset.sum_eq_single j (fun i _ hij ↦ by
          rw [inner_smul_left, ℓ.inner_lin_apply_ne hn (Subtype.val_injective.ne hij),
            mul_zero]) (by simp), inner_smul_left]
        simp +zetaDelta only [inner_lin_apply_apply, basis.inner_eq_one, mul_one]
        have h_eigs_ne (j : ℓ.EssRankAux hn α) : (eigs j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr <|
          Real.sqrt_pos.mp (α.coe_nonneg.trans_lt (Finset.mem_filter.mp j.2).2) |>.ne'
        rw [map_div₀, RCLike.conj_ofReal, div_mul_cancel₀ _ (h_eigs_ne j)]
        exact inner_conj_symm w (ℓ (basis ↑j))
      obtain ⟨d, hd⟩ := Submodule.mem_span_range_iff_exists_fun _|>.1 <| S'.sub_mem
        (Submodule.mem_inf.1 hw1).1 (S'.sum_mem fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
      refine sub_eq_zero.1 (hd ▸ ?_) |>.symm
      convert Finset.sum_eq_zero (s := @Finset.univ (ℓ.EssRankAux hn α) _) <|
        fun i hi ↦ zero_smul 𝕜 (ℓ (basis i)) with i _
      refine star_eq_zero.1 <| (mul_eq_zero.mp ?_).resolve_right <| RCLike.ofReal_ne_zero.mpr <|
          Real.sqrt_pos.mp (α.coe_nonneg.trans_lt (Finset.mem_filter.mp i.2).2) |>.ne'
      rw [← sub_self (inner 𝕜 w (ℓ (basis i)))]
      nth_rw 2 [← h_inner_match i]
      rw [← inner_sub_left, ← hd, sum_inner, Finset.sum_eq_single i (fun j _ hij ↦ by
        rw [inner_smul_left, ℓ.inner_lin_apply_ne hn (Subtype.val_injective.ne hij), mul_zero])
        (by simp), inner_smul_left, inner_lin_apply_apply]
      simp
    have h_norm_ineq : ‖w‖^2 > (α : ℝ)^2 * ‖x‖ ^ 2 := by
      conv_lhs => rw [← hx, ← @inner_self_eq_norm_sq 𝕜, map_sum]
      conv_lhs => tactic => simp_rw +zetaDelta [map_smul, inner_sum, sum_inner, inner_smul_left,
        inner_smul_right, inner_lin_apply_apply]
      rw [Finset.sum_comm, map_sum]
      convert_to ∑ i : ℓ.EssRankAux hn α, ‖c i‖^2 * eigs i > _
      · exact Finset.sum_congr rfl fun i _ => by
          rw [map_sum, Finset.sum_eq_single i (fun j _ hji => by
            simp +zetaDelta [basis.orthonormal.inner_eq_zero (Subtype.val_injective.ne hji.symm)])
            (by simp), basis.inner_eq_one, mul_one, ← mul_assoc, RCLike.conj_mul,
            ← ofReal_pow, ← ofReal_mul, ofReal_re]
      erw [← @inner_self_eq_norm_sq 𝕜, (basis.orthonormal.comp Subtype.val
        Subtype.val_injective).inner_sum c c Finset.univ]
      simp only [RCLike.conj_mul, map_sum, re_ofReal_pow, gt_iff_lt]
      rw [mul_comm, Finset.sum_mul, ← sub_pos, ← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      by_contra! hng
      have h1 (i) (h : i ∈ @Finset.univ (ℓ.EssRankAux hn α) _) :=
        mul_nonneg (sq_nonneg ‖c i‖) <| sub_nonneg.2 <| le_of_lt <| ℓ.mem_EssRankAux' hn α i.2
      replace hng := eq_of_le_of_ge hng <| Finset.sum_nonneg h1
      refine (hw2 (hx ▸ map_sum ℓ _ _ ▸ Finset.sum_eq_zero fun i hi ↦ ?_))
      convert (zero_smul 𝕜 (basis i.1)) ▸ map_zero ℓ
      simpa [sub_eq_zero, ← @eq_comm _ ((α : ℝ) ^ 2), ne_of_lt (ℓ.mem_EssRankAux' hn α _)] using
        Finset.sum_eq_zero_iff_of_nonneg h1 |>.1 hng i hi
    let x' : E := (‖x‖⁻¹ : 𝕜) • x
    have h_x'_norm : ‖x'‖ = 1 := by
      simpa [x', norm_smul] using inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.2 <|
        fun h ↦ hw2 (hx ▸ by simp [h])) : ‖x‖ ≠ 0)
    have h_dist_ℓx'_S : ∀ y ∈ S, ‖ℓ x' - y‖ ≥ ‖ℓ x'‖ := fun y hy => by
      rw [← Real.sqrt_sq (norm_nonneg _), ← @Real.sqrt_sq ‖ℓ _‖ (norm_nonneg _)]
      gcongr 1
      simp [@norm_sub_sq 𝕜, x', hx, S.inner_left_of_mem_orthogonal hy (by
        simpa [x', hx] using Sᗮ.smul_mem (‖x‖ : 𝕜)⁻¹ (Submodule.mem_inf.1 hw1).2)]
    have h_ℓx'_norm_gt_α : ‖ℓ x'‖ > α := by
      rw [show ‖ℓ x'‖ = ‖w‖ / ‖x‖ by simp [x', hx, norm_smul, mul_comm, div_eq_mul_inv],
        gt_iff_lt, lt_div_iff₀ (norm_pos_iff.2 fun h ↦ hw2 (hx ▸ by simp [h]))]
      nlinarith [h_norm_ineq, sq_nonneg ((α : ℝ) * ‖x‖ + ‖w‖),
        sq_nonneg ((α : ℝ) * ‖x‖ - ‖w‖), NNReal.coe_nonneg α, norm_nonneg x, norm_nonneg w]
    obtain ⟨y, hy1, hy2⟩ := hS_cover x' (le_of_eq h_x'_norm)
    exact (not_le.2 (h_ℓx'_norm_gt_α.trans_le <| h_dist_ℓx'_S y hy1)) <| hy2
  · have h_bad_bound (i) (hi : i ∈ (ℓ.EssRankAux hn α)ᶜ) : eigs i ≤ (α : ℝ) ^ 2 := by
      rw [show eigs i = (√(eigs i)) ^ 2 from symm <| Real.sq_sqrt (hℓℓ_pos.nonneg_eigenvalues hn i)]
      exact sq_le_sq' ((neg_le.2 ((@neg_zero ℝ _).symm ▸ α.coe_nonneg)).trans
        (Real.sqrt_nonneg _)) <| by simpa [EssRankAux] using Finset.mem_compl.1 hi
    nth_rw 1 [← basis.sum_repr' x, map_sum]
    simp_rw [map_smul]
    rw [Finset.univ_eq_attach, Finset.sum_attach _ (fun i ↦ inner 𝕜 (basis i) _ • ℓ (basis i)),
      ← Finset.sum_add_sum_compl (ℓ.EssRankAux hn α), add_sub_cancel_left,
      ← Real.sqrt_sq (norm_nonneg _), ← @inner_self_eq_norm_sq 𝕜 F, inner_sum]
    simp_rw [sum_inner, inner_smul_left, inner_smul_right]
    rw [Finset.sum_congr rfl fun i hi ↦ Finset.sum_eq_single i (fun j _ hij ↦
      (ℓ.inner_lin_apply_ne hn hij).symm ▸ by simp) (fun hi' => (hi' hi).elim)]
    conv_lhs =>
      enter [1, 2, 2, i] ; rw [show _ = (eigs i : 𝕜) * _ from ℓ.inner_lin_apply_apply hn i i,
      basis.inner_eq_one, mul_one, ← mul_assoc, RCLike.conj_mul, ← ofReal_pow, ← ofReal_mul]
    simp_rw [map_sum, ofReal_re]
    grw [Finset.sum_le_sum fun i hi ↦ by grw [h_bad_bound i hi], ← Finset.sum_mul,
      Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg _),
      basis.sum_sq_norm_inner_right x, hx_norm]
    rw [one_pow, one_mul, Real.sqrt_sq α.coe_nonneg]

lemma EssRankRestrict_eq_geometric {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} {m}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (α : NNReal) (ℓ : E →ₗ[𝕜] F) (W : Submodule 𝕜 E) (hm : Module.finrank 𝕜 W = m) :
    ℓ.EssentialRankRestrict α W hm =
    sInf {d | ∃ (S : Submodule 𝕜 F), Module.finrank 𝕜 S = d ∧
      ∀ x ∈ W, ‖x‖ ≤ 1 → ∃ y ∈ S, ‖ℓ x - y‖ ≤ α} := by
  rw [LinearMap.EssentialRankRestrict, LinearMap.EssRank_eq_geometric]
  refine congr(sInf $(Set.ext fun d ↦ ⟨fun h ↦ ?_, by simp⟩))
  exact ⟨h.choose, h.choose_spec.1, fun x hx1 hx2 ↦ h.choose_spec.2 ⟨x, hx1⟩ (by simpa using hx2)⟩

lemma EssRankRestrict_eq_geometric' {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} {m}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (α : NNReal) (ℓ : E →ₗ[𝕜] F) (W : Submodule 𝕜 E) (hm : finrank 𝕜 W = m) :
    ℓ.EssentialRankRestrict α W hm = sInf {d | ∃ (S : Submodule 𝕜 F), finrank 𝕜 S ≤ d ∧
      ∀ x ∈ W, ‖x‖ ≤ 1 → ∃ y ∈ S, ‖ℓ x - y‖ ≤ α} := ℓ.EssRankRestrict_eq_geometric α W hm ▸ by
  refine csInf_eq_csInf_of_forall_exists_le ?_ <| fun _ ⟨S, h', h⟩ ↦ ⟨finrank 𝕜 S, ⟨S, rfl, h⟩, h'⟩
  exact fun n ⟨S, h', h⟩ ↦ ⟨n, ⟨S, h' ▸ le_rfl, h⟩, le_rfl⟩

/-! ## About essential rank -/

lemma EssRankRestrict_top {𝕜 E F : Type*} [RCLike 𝕜] {n : ℕ} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (hn : Module.finrank 𝕜 E = n) (α : NNReal) (l : E →ₗ[𝕜] F)
    (hn' : Module.finrank 𝕜 (⊤ : Submodule 𝕜 E) = n) :
    l.EssentialRankRestrict α ⊤ hn' = l.EssentialRank hn α := by
  rw [EssRankRestrict_eq_geometric, EssRank_eq_geometric]
  exact congr_arg sInf <| Set.ext fun x ↦ by simp

lemma EssentialRank_comp_Isometry {𝕜 E1 E2 F : Type*} {n m} [RCLike 𝕜]
    [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1] (hn : Module.finrank 𝕜 E1 = n)
    [FiniteDimensional 𝕜 E1] [NormedAddCommGroup E2] [InnerProductSpace 𝕜 E2]
    (hm : Module.finrank 𝕜 E2 = m) [FiniteDimensional 𝕜 E2] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (e : E1 ≃ₗᵢ[𝕜] E2) {α : NNReal} (l : E2 →ₗ[𝕜] F) :
    l.EssentialRank hm α = (l ∘ₗ e.toLinearMap).EssentialRank hn α := by
  rw [EssRank_eq_geometric, EssRank_eq_geometric]
  refine congr(sInf $(Set.ext fun x ↦ ⟨?_, ?_⟩))
  all_goals refine fun ⟨S, hS1, hS2⟩ ↦ ⟨S, hS1, fun x hx ↦ ?_⟩
  · exact hS2 (e x) (e.norm_map x ▸ hx)
  · simpa using hS2 (e.symm x) (e.symm.norm_map x ▸ hx)

lemma EssentialRankRestrict_comp_Isometry {𝕜 E F G : Type*} [RCLike 𝕜] {n m}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (l : F →ₗ[𝕜] G) (U : E ≃ₗᵢ[𝕜] F) (α : NNReal) (W : Submodule 𝕜 E)
    (hn : Module.finrank 𝕜 W = n) (hm : Module.finrank 𝕜 (W.map U) = m) :
    l.EssentialRankRestrict α (W.map U.toLinearMap) hm =
    (l.comp U.toLinearMap).EssentialRankRestrict α W hn := by
  unfold EssentialRankRestrict
  rw [EssRank_eq_geometric, EssRank_eq_geometric]
  refine congr(sInf $(Set.ext fun x ↦ ⟨?_, ?_⟩))
  all_goals refine fun ⟨S, hS1, hS2⟩ ↦ ⟨S, hS1, fun ⟨w, hw1⟩ hw2 ↦ ?_⟩
  · simpa using hS2 ⟨U w, by simp [hw1]⟩ (by simpa using hw2)
  · obtain ⟨x, hx1, hx2⟩ := hw1
    simp only [← hx2, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      AddSubgroupClass.coe_norm, LinearIsometryEquiv.norm_map] at hw2
    obtain ⟨y, hy1, hy2⟩ := hS2 ⟨x, hx1⟩ (by simpa using hw2)
    exact ⟨y, hy1, by simpa [← hx2] using hy2⟩

end LinearMap

import BrascampLieb.Code.LinearLemmas
import BrascampLieb.Code.LogicLemmas
import BrascampLieb.ToMathlib.Algebra.BigOperators.Fin
import BrascampLieb.ToMathlib.Algebra.BigOperators.Group.Finset.Piecewise
import BrascampLieb.ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Background Lemmas for Brascamp-Lieb Upper Bound

This file contains helper lemmas needed for the Brascamp-Lieb upper bound theorem.
-/

namespace LinearMap

open BrascampLieb

/-! ## Section 1: Positive Definiteness Lemmas -/

-- open EuclideanSpace in
-- /-- Adding a positive semidefinite operator to a positive definite operator
--     preserves positive definiteness. -/
-- lemma IsPosDef.add_IsPositive {n : Type*} [Fintype n] [DecidableEq n]
--     {T S : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n}
--     (hT : T.IsPosDef) (hS : S.IsPositive) : (T + S).IsPosDef := by
--   obtain ⟨hT1, hT2⟩ := hT
--   refine ⟨hT1.add hS, (T + S).det_toMatrix (basisFun n ℝ).toBasis ▸ (Matrix.PosDef.add_posSemidef
--     (Matrix.PosSemidef.posDef_iff_isUnit ?_ |>.2 ?_) ?_).det_pos.ne'⟩
--   all_goals try exact posSemidef_toMatrix_iff (basisFun n ℝ) |>.2 <| by assumption
--   · erw [Matrix.isUnit_iff_isUnit_det, T.det_toMatrix (basisFun n ℝ).toBasis]
--     exact hT2.isUnit

end LinearMap

namespace BrascampLieb

variable {J E F : Type*} {n m} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] (hm : Module.finrank ℝ F = m) [FiniteDimensional ℝ F] {α : NNReal}

/-! ## Section 8: Greedy Index Set Construction -/
open EuclideanSpace

omit [FiniteDimensional ℝ F] in
/--
Greedy index set construction.
Given a basis (e₁,...,eₐ) and threshold ε, construct I_j by processing indices
from d down to 1, including i if dist(ℓ_j eᵢ, span{ℓ_j eₖ : k ∈ I_j, k > i}) ≥ ε.
Algorithm:
1. Start with I = ∅
2. For i from d down to 1:
    - Let S = {ℓ(e_k) : k ∈ I, k > i}
    - If dist(ℓ(e_i), span(S)) ≥ ε, add i to I
3. Return I
-/
lemma greedy_index_set_exists {d : ℕ} (hα : 0 < α)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) : ∃ I : Finset (Fin d),
    (∀ i ∈ I, Metric.infDist (ℓ (single i 1)) (ℓ '' Submodule.span ℝ (basisFun (Fin d) ℝ ''
      (I ∩ Finset.Ioi i))) ≥ α / NNReal.sqrt d) ∧ (∀ i, Metric.infDist (ℓ (single i (1 : ℝ)))
      (ℓ '' Submodule.span ℝ (basisFun (Fin d) ℝ '' (I ∩ Finset.Ici i))) < α / NNReal.sqrt d) := by
  if hn : d = 0 then refine ⟨∅, by simp, hn ▸ by simp⟩ else
  convert Fin.greedyIndexSet (fun i I ↦ Metric.infDist (ℓ (single i 1)) (ℓ ''
    (Submodule.span ℝ (basisFun (Fin d) ℝ '' I))) < (α : ℝ) / (NNReal.sqrt d : ℝ))
    fun i I hi ↦ (Metric.infDist_zero_of_mem ?_).trans_lt (by positivity)
  · simp
  · simp
  · simp only [basisFun_apply, Set.mem_image, SetLike.mem_coe]
    exact ⟨EuclideanSpace.single i 1, Submodule.subset_span (Set.mem_image_of_mem _ hi), rfl⟩

omit [FiniteDimensional ℝ F] in
noncomputable def greedy_index_set {d : ℕ} (hα : 0 < α)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) : Finset (Fin d) :=
  greedy_index_set_exists hα ℓ|>.choose

attribute [local instance] Fintype.ofFinite in
lemma essRank_le_ncard_inter_greedy {d n : ℕ} (hα : 0 < α)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) (i)
    (hn1 : Module.finrank ℝ ↥(Submodule.span ℝ
      (basisFun (Fin d) ℝ '' (SetLike.coe (Finset.Ici i)))) = n) :
    ℓ.EssentialRankRestrict α (Submodule.span ℝ (basisFun (Fin d) ℝ '' Finset.Ici i)) hn1 ≤
    Finset.card (greedy_index_set hα ℓ ∩ Finset.Ici i) := by
  classical if hd : d = 0 then subst hd; exact Fin.elim0 i else
  rw [LinearMap.EssRankRestrict_eq_geometric']
  let S := Submodule.map ℓ (Submodule.span ℝ (basisFun (Fin d) ℝ ''
    (SetLike.coe (greedy_index_set hα ℓ ∩ Finset.Ici i))))
  refine Nat.sInf_le ⟨S, ?_, fun x hx1 hx2 ↦ ?_⟩
  · unfold S
    grw [LinearMap.map_span, finrank_span_le_card, Set.toFinset_image, Finset.card_image_le,
      Set.toFinset_image, Finset.toFinset_coe, Finset.card_image_le]
  · have h_approx (j) : ∃ approx ∈ ℓ '' (Submodule.span ℝ (basisFun (Fin d) ℝ ''
      (greedy_index_set hα ℓ ∩ Finset.Ici j))), dist (ℓ (basisFun (Fin d) ℝ j)) approx <
      (α : ℝ) / Real.sqrt d := by
      refine Metric.infDist_lt_iff ?_ |>.1 <| by simpa [greedy_index_set] using
        (greedy_index_set_exists hα ℓ).choose_spec.2 j
      exact ⟨0, 0, Submodule.zero_mem _, map_zero ℓ⟩
    choose f hf1 hf2 using h_approx
    let y : F := ∑ j : Fin d, x j • f j
    refine ⟨∑ j : Fin d, x j • f j, Submodule.sum_mem _ fun j _ ↦ if h : i ≤ j then S.smul_mem (x j)
      ?_ else (?_ : x j = 0) ▸ zero_smul ℝ (f j) ▸ S.zero_mem, ?_⟩
    · obtain ⟨z, hz1, hz2⟩ := hf1 j
      refine hz2 ▸ Submodule.mem_map_of_mem <| Submodule.span_mono ?_ hz1
      simp only [← Finset.coe_inter, greedy_index_set]
      grw [Finset.Ici_subset_Ici.2 h]
    · rw [← one_mul (x j), ← star_trivial (x j), ← starRingEnd_apply, ← inner_single_right]
      clear hx2
      induction hx1 using Submodule.span_induction with
      | mem x h =>
        obtain ⟨k, hk1, hk2⟩ := h
        simpa [← hk2, inner_single_left] using ((not_le.1 h).trans_le (by simpa using hk1)).ne'
      | zero => simp
      | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
      | smul a x _ hx => simp [inner_smul_left, hx]
    nth_rw 1 [← (basisFun (Fin d) ℝ ).sum_repr x, map_sum]
    simp only [basisFun_repr, basisFun_apply, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
    grw [norm_sum_le, ← one_mul (α : ℝ), ← mul_le_mul_of_nonneg_right hx2 α.coe_nonneg]
    simp only [norm_smul, Real.norm_eq_abs, norm_eq, sq_abs]
    grw [Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
      (_ : ‖ℓ (single j 1) - f j‖ ≤ ↑α / √↑d) (abs_nonneg _), ← Finset.sum_mul,
      (_ : ∑ i, |x i| ≤ (Real.sqrt (∑ j, (x j)^ 2)) * Real.sqrt d), mul_assoc, mul_div_cancel₀]
    · exact Real.sqrt_ne_zero'.2 <| Nat.cast_pos.2 <| by omega
    · simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j ↦ |x j|) 1
    · exact fun j _ ↦ LT.lt.le <| by convert hf2 j using 1; simp [dist_eq_norm]


/- Volume bound for greedy sets (Lemma 2.3 in blueprint, line 164)
   The tex file states: ‖∧_{i∈I_j} ℓ_j e_i‖ ≥ d^{-|I_j|/2}
   With threshold α/√n, this gives: det(Gram) ≥ (α/√n)^{2|I|} = (α²/n)^|I| -/
lemma greedy_index_set_volume_bound {d : ℕ} (hα : 0 < α) (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) :
    ((α : ℝ) / Real.sqrt d) ^ (2 * (greedy_index_set hα ℓ).card) ≤ (@Matrix.gram _
      (greedy_index_set hα ℓ) ℝ _ (ℓ ∘ basisFun (Fin d) ℝ ∘ Subtype.val)).det := by
  rw [Matrix.det_gram_eq_prod_infDist (ℓ ∘ basisFun (Fin d) ℝ ∘ Subtype.val), mul_comm 2, pow_mul,
    ← Fintype.card_coe, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ ↦ sq_nonneg _) fun ⟨i, hi⟩ _ ↦ sq_le_sq₀ (by positivity)
    Metric.infDist_nonneg |>.2 <| (by simp : Real.sqrt d = (NNReal.sqrt d)) ▸ ?_
  grw [← (greedy_index_set_exists hα ℓ).choose_spec.1 i hi]
  convert Metric.infDist_le_infDist_of_subset (fun x hx ↦ ?_ : (Submodule.span ℝ (ℓ ∘
    (basisFun (Fin d) ℝ) ∘ Subtype.val '' Set.Ioi ⟨i, hi⟩) : Set F) ⊆ _) ⟨0, by simp⟩
  · simp
  induction (SetLike.mem_coe.1 hx) using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, hj1, hj2, rfl⟩ := h
    exact ⟨single j 1, Submodule.subset_span ⟨j, ⟨j.2, Finset.coe_Ioi i ▸ hj1⟩,
      basisFun_apply _ _ _⟩, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y h1 h2 h h' =>
    obtain ⟨x', hx1, rfl⟩ := h h1
    obtain ⟨y', hy1, rfl⟩ := h' h2
    exact ⟨x' + y', Submodule.add_mem _ (by assumption) (by assumption), map_add ..⟩
  | smul a x _ hx' =>
    obtain ⟨x', hx', rfl⟩ := hx' (by assumption)
    exact ⟨a • x', Submodule.smul_mem _ _ (by assumption), map_smul ..⟩

open LinearMap

/-- Cardinality of greedy_index_set is equal to the dimension of the image -/
lemma card_greedy_eq_of_essRank_eq {d : ℕ} (hm : Module.finrank ℝ F = m) (hα : 0 < α)
    {ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F} (hℓ : ℓ.EssentialRank finrank_euclideanSpace_fin α = m) :
    Finset.card (greedy_index_set hα ℓ) = Module.finrank ℝ F := by
  if hd : d = 0 then
    subst hd;
    simpa [hm, ← hℓ, EssentialRank, EssRankAux] using Finset.ext fun x ↦ Fin.elim0 x else
  let v : greedy_index_set hα ℓ → _ := ℓ ∘ (basisFun (Fin d) ℝ) ∘ Subtype.val
  apply le_antisymm
  · rw [← Fintype.card_coe]
    refine (Matrix.posDef_gram_iff_linearIndependent (v := v).1 ?_).fintype_card_le_finrank
    rw [(Matrix.posSemidef_gram ℝ v).posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact  Ne.isUnit <| ne_of_gt <| by grw [← greedy_index_set_volume_bound hα ℓ]; positivity
  · haveI : NeZero d := ⟨hd⟩
    let E : Finset (Fin d) → _:= Submodule.span ℝ ∘ Set.image (basisFun (Fin d) ℝ) ∘ SetLike.coe
    convert
      (by simpa only [show Finset.Ici (0 : Fin d) = ⊤ by ext; simp, Finset.top_eq_univ,
        Finset.coe_univ, Set.image_univ, Finset.inter_univ] using
          essRank_le_ncard_inter_greedy hα ℓ 0
            (by simp [finrank_span_image' (basisFun (Fin d) ℝ)] : _ = d))
    conv_lhs => rw [hm, ← hℓ]
    conv_rhs => enter [3]; erw [(basisFun (Fin d) ℝ).toBasis.span_eq]
    exact ℓ.EssRankRestrict_top finrank_euclideanSpace_fin α _ |>.symm

include hn hm in
lemma det_greedy_control (b : OrthonormalBasis (Fin n) ℝ E) (hα : 0 < α) {ℓ : E →ₗ[ℝ] F}
    (hℓ : ℓ.EssentialRank hn α = m) {Q : F →ₗ[ℝ] F} (hQ : Q.IsPositive) :
    Q.det * (α ^ 2 / n) ^ m ≤ ∏ i ∈ (greedy_index_set hα (ℓ ∘ₗ b.repr.symm.toLinearMap)),
      inner ℝ (Q (ℓ (b i))) (ℓ (b i)) := by
  let I := greedy_index_set hα (ℓ ∘ₗ b.repr.symm.toLinearMap)
  let v : Fin n → F := (ℓ ∘ₗ b.repr.symm.toLinearMap) ∘ basisFun (Fin n) ℝ
  have hI : Finset.card I = m := by
    refine hm ▸ card_greedy_eq_of_essRank_eq hm hα <| hℓ ▸ symm ?_
    exact ℓ.EssentialRank_comp_Isometry finrank_euclideanSpace_fin hn b.repr.symm
  have h0 := greedy_index_set_volume_bound hα (ℓ ∘ₗ b.repr.symm.toLinearMap)
  have h_equiv : Fin m ≃ I := (Fintype.equivFinOfCardEq (by simp [hI])).symm
  have h1 := Q.choleski_det_bound hm hQ (v ∘ Subtype.val ∘ h_equiv)
  conv_lhs at h1 => rw [← Function.comp_assoc, ← Matrix.submatrix_gram']
  rw [Matrix.det_submatrix_equiv_self, Fintype.prod_equiv h_equiv (fun i ↦ inner ℝ (Q ((v ∘
    Subtype.val ∘ h_equiv) i)) ((v ∘ Subtype.val ∘ h_equiv) i)) (fun i ↦ inner ℝ (Q (v i)) (v i))
    (fun _ ↦ rfl), Finset.prod_coe_sort I (fun i ↦ inner ℝ (Q (v i)) (v i))] at h1
  rw [pow_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg' n), hI] at h0
  grw (transparency := default) [h0, h1]
  · simp +zetaDelta
  · exact hQ.det_nonneg

/-! ## Section 9: Eigenvalue Telescoping -/

attribute [local grind! .] Real.rpow_pos_of_pos in
lemma prod_rpow_eq_first_times_ratio_prod' {d : ℕ} [NeZero d] (l : Fin (d + 1) → ℝ)
    (hl1 : ∀ i, 0 < l i) (c : Fin (d + 1) → ℝ) : ∏ i : Fin (d + 1), l i ^ c i =
    l 0 ^ (∑ i, c i) * ∏ k : Fin d, (l k.succ / l k.castSucc) ^ (∑ i ∈ Finset.univ.filter
      (fun i : Fin (d + 1) => k.castSucc < i), c i) := by
  let r : Fin d → ℝ := fun k => l k.succ / l k.castSucc
  let I (k : Fin d) : Finset (Fin (d + 1)) := Finset.univ.filter (fun i ↦ k.castSucc < i)
  let I' (i : Fin (d + 1)) : Finset (Fin d) := Finset.univ.filter (fun k ↦ k.castSucc < i)
  have hr (i) : 0 < r i := div_pos (hl1 _) (hl1 _)
  have hl2 (i) : Real.log (l i) =
      Real.log (l 0) + ∑ k ∈ I' i, Real.log (l k.succ / l k.castSucc) := by
    simp_rw [Real.log_div (hl1 _).ne' (hl1 _).ne', ← Function.comp_apply (f := Real.log)]
    rw [Finset.sum_sub_succ_cancel (Real.log ∘ l) i]
    simp
  have h1 (i) : 0 < l i ^ c i := by grind
  have h2 (k) : 0 < r k ^ (∑ i ∈ I k, c i) := by grind
  refine Real.log_injOn_pos.eq_iff (Set.mem_Ioi.2 ?_) (Set.mem_Ioi.2 <| mul_pos ?_ ?_) |>.1 ?_
  all_goals try exact Finset.prod_pos (fun i _ ↦ by grind)
  · grind
  · rw [Real.log_prod fun i _ ↦ (h1 i).ne', Real.log_mul (by grind) (Finset.prod_pos fun i _ ↦
      h2 i).ne', Real.log_prod fun i _ ↦ (h2 i).ne', Real.log_rpow (hl1 0)]
    simp_rw [Real.log_rpow (hr _), Real.log_rpow (hl1 _)]
    conv_lhs => enter [2, x]; rw [hl2, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm' fun i j ↦ by simp [I', I]

set_option linter.unusedVariables false in
lemma telescoping_product_bound' {d : ℕ} [NeZero d] (l : Fin (d + 1) → ℝ)
    (hl1 : ∀ i j : Fin (d + 1), i ≤ j → l j ≤ l i) (hl2 : ∀ i, 0 < l i)
    (c : Fin (d + 1) → ℝ) (S β : ℝ) (h_sum : ∑ i, c i = S)
    (ht : ∀ k (hk : k.1 < d), ∑ i ∈ Finset.univ.filter (fun i : Fin (d + 1) => k < i), c i ≥ -β) :
    ∏ i : Fin (d + 1), l i ^ c i ≤ l 0 ^ (S + β) * l (Fin.last d) ^ (-β) := by
  let r : Fin d → ℝ := fun k ↦ l k.succ / l k.castSucc
  have hr_pos (k) : 0 < r k := div_pos (hl2 _) (hl2 _)
  let t : Fin d → ℝ := fun k ↦ ∑ i ∈ Finset.univ.filter (fun i ↦ k.castSucc < i), c i
  have hprod_bound : ∏ k : Fin d, r k ^ t k ≤ l 0 ^ β * (l (Fin.last d)) ^ (-β) := by
    grw [(Finset.prod_le_prod (fun _ _ ↦ Real.rpow_nonneg (hr_pos _).le _) (fun k _ ↦
      Real.antitone_rpow_of_base_le_one (hr_pos k) (div_le_one_of_le₀ (hl1 _ _ <| by
        simp [Fin.le_iff_val_le_val]) (hl2 _).le) (ht _ (by simp))) : _ ≤ ∏ i, r i ^ (- β)),
      Real.finset_prod_rpow _ r (by grind), Fin.prod_div_succ (by grind),
      Real.div_rpow (by grind) (by grind), Real.rpow_neg (hl2 0).le, div_inv_eq_mul, mul_comm]
  grw [prod_rpow_eq_first_times_ratio_prod' l hl2 c, h_sum, hprod_bound, ← mul_assoc,
    ← Real.rpow_add (hl2 _)]
  exact Real.rpow_nonneg (hl2 0).le _

lemma eigenvalue_telescoping' {d : ℕ} (l : Fin (d + 1) → ℝ) (hl1 : Antitone l) (hl2 : ∀ i, 0 < l i)
    (I : J → Finset (Fin (d + 1))) (q : J → NNReal) (β : NNReal) (Ac : NNReal)
    (h_card : ∑ j, q j * (I j).card = Ac) (h_percep : ∀ i : Fin (d + 1), (∑ j, q j *
    (I j ∩ Finset.Ici i).card) ≥ ((d + 1) - i : ℝ) - β) :
    ∏ j, (∏ i ∈ I j, l i) ^ (q j : ℝ) ≤ l 0 ^ (Ac - (d + 1) + β : ℝ) * (l (Fin.last d)) ^
      (- (β : ℝ)) * ∏ i, l i := by
  if hd : d = 0 then
  subst hd
  simp_all only [Nat.reduceAdd, Fin.forall_fin_one, Fin.isValue, NNReal.coe_sum, NNReal.coe_mul,
    NNReal.coe_natCast, CharP.cast_eq_zero, zero_add, Fin.val_eq_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, Fin.last_zero, Finset.univ_unique, Fin.default_eq_zero,
    Finset.prod_singleton]
  rw [← Real.rpow_add hl2, ← sub_eq_add_neg, add_sub_cancel_right]
  nth_rw 2 [← Real.rpow_one (l 0)]
  rw [← Real.rpow_add hl2, sub_add_cancel]
  have h (x) : I x = if 0 ∈ I x then {0} else ∅ := Finset.ext fun i ↦ by
    split_ifs with h1; all_goals fin_cases i; simpa
  conv_lhs => enter [2, x]; rw [h]
  simp only [Nat.reduceAdd, Fin.isValue, Finset.ite_prod, Finset.prod_singleton, Finset.prod_empty,
    ite_pow, Real.one_rpow, Finset.prod_ite, Finset.prod_const_one, mul_one]
  simp_rw +singlePass [h, Finset.card_ite] at h_card
  simp only [Nat.reduceAdd, Fin.isValue, Finset.card_singleton, Finset.card_empty, Nat.cast_ite,
    Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite] at h_card
  simp [← Real.rpow_sum_of_pos hl2, ← h_card] else
  simp_rw [← Real.finset_prod_rpow _ _ (fun _ _ ↦ (hl2 _).le)]
  rw [show _ = ∏ y, ∏ x with y ∈ I x, _ from Finset.prod_comm' (fun i j ↦ by simp)]
  simp_rw [← Real.rpow_sum_of_pos (hl2 _), Finset.sum_filter]
  conv_lhs =>
    enter [2, x]; rw [← sub_add_cancel (∑ a, _) 1, Real.rpow_add (hl2 _), Real.rpow_one]
    enter [1, 2, 1, 2, a]; rw [← mul_one (q a : ℝ), ← mul_ite_zero]
  rw [Finset.prod_mul_distrib]
  let c : Fin (d + 1) → ℝ := fun i => (∑ j, (q j : ℝ) * if i ∈ I j then (1 : ℝ) else 0) - 1
  haveI : NeZero d := ⟨by omega⟩
  grw [telescoping_product_bound' l hl1 hl2 c ((Ac : ℝ) - (d + 1)) (β : ℝ) (by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, sub_left_inj, c]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_one,
        add_zero, ← NNReal.coe_natCast, ← NNReal.coe_mul, ← NNReal.coe_sum, ← h_card]
      simp) <| fun k hk ↦ by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ge_iff_le,
      neg_le_sub_iff_le_add, c]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
    have := h_percep ⟨k.1 + 1, by omega⟩
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
      add_sub_add_right_eq_sub, ge_iff_le, tsub_le_iff_right (b := (β : ℝ))] at this
    conv_rhs => enter [1, 2, x, 2, 1, 1]; rw [Finset.inter_comm]
    convert this with j
    · rw [← Nat.cast_sub (by omega)]
      norm_cast
      convert Fin.card_Ioi k using 2
      grind
    · simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      grind [Fin.le_def, Fin.lt_def]]
  exact Finset.prod_nonneg fun i _ => le_of_lt (hl2 i)

end BrascampLieb

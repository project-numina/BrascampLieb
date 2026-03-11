import BrascampLieb.Code.BackgroundLemmas
import BrascampLieb.Code.NNRealLemmas
import BrascampLieb.ToMathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.FreeModule.Determinant

namespace BrascampLieb

open EuclideanSpace in
lemma upperBound_single_term {J E : Type*} {n} [Fintype J] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E]
    {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    {m : J → ℕ} (hm : ∀ j, Module.finrank ℝ (F j) = m j) (hE : n ≠ 0)
    (D : locRegDatum E F) (α : J → NNReal) (β : NNReal)
    (hα : ∀ i, 0 < α i) (hP : D.IsMetricPercep α β)
    (hS : ∀ j : J, (D.map j).EssentialRank hn (α j) = m j)
    (A : (j : J) → F j →ₗ[ℝ] F j)
    (hA : ∀ j, (A j).IsPosDef ∧ A j ≤ D.reg j) :
    let M_max := (D.loc + ∑ j, (D.weight j) • (D.map j).adjoint ∘ₗ (D.reg j) ∘ₗ (D.map j))
    loc_constant_g_of D.tolocDatum A (fun j => (hA j).1) ≤
      (n : NNReal) ^ (D.Acuity / 2 : ℝ) *
      (∏ j, (D.weight j)^(- (D.weight j : ℝ) * m j / 2)) *
      (∏ j, (α j)^(- (D.weight j : ℝ) * m j)) *
      ‖M_max.toContinuousLinearMap‖₊^((D.Acuity.toReal - n + β) / 2) *
      ‖(D.loc.equivOfDetNeZero D.pos_loc.2).symm.toContinuousLinearMap‖₊^(β.toReal / 2) := by
  intro M_max
  set T_inv := (D.loc.equivOfDetNeZero D.pos_loc.2).symm
  rw [NNReal.sqrt_le_iff_le_sq]
  simp only [mul_pow, ← Finset.prod_pow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul,
    Nat.cast_ofNat, div_mul_cancel_of_invertible]
  apply NNReal.div_le_of_le_mul
  set M := D.loc + ∑ j, (D.weight j) • (D.map j).adjoint ∘ₗ (A j) ∘ₗ (D.map j)
  have hM : M.IsPosDef := loc_c_PosDef D.1 A (fun j ↦ (hA j).1)
  let lam : Fin n → NNReal := fun i ↦ ⟨hM.1.1.eigenvalues hn i, hM.1.nonneg_eigenvalues hn i⟩
  let basis := hM.1.1.eigenvectorBasis hn
  -- ℓ' j is the D.map j precomposed with the isometry from ℝ^d to E
  let ℓ' := fun j ↦ D.map j ∘ₗ basis.repr.symm.toLinearMap
  -- Greedy index sets
  let I := fun j ↦ greedy_index_set (hα j) (ℓ' j)
  have cardI j : Finset.card (I j) = m j := hm j ▸
    card_greedy_eq_of_essRank_eq (hm j) _ (hS j ▸ ((D.map j).EssentialRank_comp_Isometry ..).symm)
  rw [mul_assoc, mul_assoc]
  apply le_mul_of_le_mul_left (c := ∏ j, (∏ i ∈ I j, lam i) ^ (D.weight j : ℝ))
  -- show _ ≤ _ * ∏ j, (∏ i ∈ I j, lam i) ^ (D.weight j : ℝ)
  · simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast, neg_mul]
    rw [NNReal.rpow_sum (by norm_cast), ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (by simp) fun j _ ↦ ?_
    · if hq : D.weight j = 0 then simp [hq] else
      rw [hm]
      apply mainlem2 (D.weight _).2 (by grind [Nat.cast_pos] : 0 < (n : ℝ))
        (pos_iff_ne_zero.2 hq) (hα j)
      simp only [NNReal.rpow_natCast, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_mk, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_prod]
      refine mul_le_of_mul_le_of_nonneg_left (b := ∏ i ∈ I j, inner ℝ (A j (D.map j (basis i)))
        (D.map j (basis i))) ?_ (det_greedy_control hn (hm j) basis (hα j) (hS j) (hA j).1.1) <|
        pow_nonneg (D.weight j).2 _
      rw [← cardI, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ ↦ mul_nonneg (D.weight j).2 ?_) fun i _ ↦ ?_
      · exact (hA j).1.1.inner_nonneg_left _
      · rw [← LinearMap.adjoint_inner_left, ← real_inner_smul_left, ← NNReal.smul_def]
        grw [(by
          simp only [LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply, inner_add_left,
            sum_inner, M]
          grw [← D.pos_loc.1.inner_nonneg_left, zero_add, Finset.single_le_sum
          (f := fun k ↦ inner ℝ ((D.weight k) • (D.map k).adjoint (A k ((D.map k) (basis i)))) _)
          (fun i _ ↦ by
            simp only [← LinearMap.comp_apply, NNReal.smul_def, real_inner_smul_left]
            exact mul_nonneg (D.weight _).2 (LinearMap.IsPositive.inner_nonneg_left
                (.adjoint_conj (hA _).1.1 (D.map _)) _)) (Finset.mem_univ j)] :
            inner ℝ _ _ ≤ inner ℝ (M (basis i)) (basis i))]
        simp [lam, basis, hM.1.1.apply_eigenvectorBasis hn i, inner_smul_left]
  haveI : NeZero n := ⟨hE⟩
  let p : Fin n := Fin.pred (Fin.last n) (by simp [hE])
  have hp : p = ⟨n - 1, Nat.pred_lt hE⟩ := by ext; simp [p]
  trans lam 0 ^ (D.Acuity - n + β : ℝ) * (lam p) ^ (-(β : ℝ)) * ∏ i, lam i
  · rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_prod, NNReal.coe_rpow, NNReal.coe_mk, NNReal.coe_sum, NNReal.coe_mul,
      NNReal.coe_natCast, lam]
    obtain ⟨mm, rfl⟩ : ∃ mm, n = mm + 1 := ⟨n - 1, symm <| n.sub_one_add_one (by omega)⟩
    simp only [Nat.cast_add, Nat.cast_one]
    convert eigenvalue_telescoping' (hM.1.1.eigenvalues hn) (hM.1.1.eigenvalues_antitone hn)
      (hM.eigenvalues_pos hn) I D.weight β D.Acuity (by simp [Datum.Acuity, hm, cardI]) fun i ↦ ?_
    · simp [Datum.Acuity]
    · let W := Submodule.span ℝ ((basisFun (Fin (mm + 1)) ℝ) '' (Finset.Ici i))
      trans ∑ j, (D.weight j) * ((ℓ' j).EssentialRankRestrict (α j) W (finrank_span_image'
        (basisFun (Fin (mm + 1)) ℝ) (Finset.Ici i)))
      · simp_rw [← NNReal.coe_natCast, ← NNReal.coe_mul, ← NNReal.coe_sum]
        gcongr with j
        simp only [Fin.card_Ici, W]
        exact essRank_le_ncard_inter_greedy _ _ i _
      · have hW :
            Module.finrank ℝ (Submodule.map (basis.repr.symm.toLinearMap) W) = (mm + 1) - i := by
          rw [LinearIsometryEquiv.finrank_map_eq]
          simp [W, finrank_span_image']
        have h := hW ▸ hP (Submodule.map basis.repr.symm.toLinearMap W) hW
        simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_sum,
          NNReal.coe_mul, Nat.cast_tsub, Nat.cast_add, Nat.cast_one, Datum.AcuityWithin,
          tsub_le_iff_right, Fin.card_Ici, ge_iff_le, ← NNReal.coe_le_coe] at h ⊢
        convert h
        exact (D.map _).EssentialRankRestrict_comp_Isometry .. |>.symm
  rw [← mul_assoc]
  refine mul_le_mul' (mul_le_mul' (NNReal.rpow_le_rpow ?_ ?_) ?_) ?_
  · rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_mk, coe_nnnorm, lam, ← hM.1.opNorm_eq_top_eigenvalue hn]
    · refine hM.1.opNorm_le_of_le hn (?_ : LinearMap.IsPositive _)
      convert (LinearMap.IsPositive.sum fun j ↦ .smul_of_nonneg (.adjoint_conj (hA j).2 (D.map j))
        (D.weight j).2)
      simp [M, M_max, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← smul_sub,
        LinearMap.comp_sub, LinearMap.sub_comp, NNReal.smul_def]
  · suffices n ≤ D.Acuity.toReal + β.toReal by linarith
    rw [← hn, ← finrank_top, ← NNReal.coe_add, ← NNReal.coe_natCast, NNReal.coe_le_coe]
    convert hP ⊤ (hn ▸ finrank_top ℝ E : _ = n)
    simp [Datum.AcuityWithin, Datum.Acuity, (D.map _).EssRankRestrict_top hn, hS, hm]
  · rw [NNReal.rpow_neg, ← NNReal.inv_rpow]
    refine NNReal.rpow_le_rpow ?_ β.coe_nonneg
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_inv, coe_nnnorm]
    rw [D.pos_loc.opNorm_inv_eq hn hE, inv_le_inv₀ (by simpa using hM.eigenvalues_pos hn _)
      (D.pos_loc.eigenvalues_pos hn _)]
    · refine D.pos_loc.isPositive.bot_eigenvalue_le_of_le hn hE (?_ : LinearMap.IsPositive _)
      simp only [M, add_sub_cancel_left]
      exact .sum fun j ↦ .smul_of_nonneg (.adjoint_conj (hA j).1.1 (D.map j)) (D.weight j).2
  · simpa [← NNReal.coe_le_coe, lam] using le_of_eq
      (LinearMap.IsSymmetric.det_eq_prod_eigenvalues hn hM.isSymmetric).symm

/-!
# Main Brascamp-Lieb Upper Bound Theorem

This file contains the proof of the effective upper bound for the localized regularized
Brascamp-Lieb constant (Theorem 1.4 from Bénard-He 2023).

The proof follows these main steps:
1. Reduction to α = 1 for all j
2. Show M is positive definite
3. Construct greedy index sets I_j
4. Apply Hadamard determinant bound
5. Use eigenvalue telescoping
6. Combine all bounds
-/
theorem upperBound {J E : Type*} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (hE : Module.finrank ℝ E ≠ 0)
    (D : locRegDatum E F) (α : J → NNReal) (β : NNReal) (hα : ∀ i, 0 < α i)
    (hP : D.IsMetricPercep α β)
    (hS : ∀ j : J, (D.map j).EssentialRank rfl (α j) = Module.finrank ℝ (F j)) :
    let M_max := (D.loc + ∑ j, (D.weight j) • (D.map j).adjoint ∘ₗ (D.reg j) ∘ₗ (D.map j))
    loc_reg_constant_g D ≤
      (Module.finrank ℝ E : NNReal)^(D.Acuity / 2 : ℝ) *
      (∏ j, (D.weight j)^(- (D.weight j : ℝ) * Module.finrank ℝ (F j) / 2)) *
      (∏ j, (α j)^(- (D.weight j : ℝ) * Module.finrank ℝ (F j))) *
      ‖M_max.toContinuousLinearMap‖₊^((D.Acuity.toReal - Module.finrank ℝ E + β) / 2) *
      ‖(D.loc.equivOfDetNeZero D.pos_loc.2).symm.toContinuousLinearMap‖₊^(β.toReal / 2) := by
  intro M_max
  refine iSup_le fun A ↦ le_trans (ENNReal.coe_le_coe.2 (upperBound_single_term rfl (fun _ ↦ rfl) hE
    D α β hα hP hS A.1 A.2)) ?_
  simp only [ENNReal.coe_mul, ENNReal.coe_finset_prod, ENNReal.coe_natCast]
  gcongr <;> refine le_of_eq ?_
  · exact (ENNReal.coe_rpow_of_nonneg _ (div_nonneg D.Acuity.2 (by norm_num)))
  · refine (ENNReal.coe_rpow_of_ne_zero ?_ _)
    rw [ne_eq, nnnorm_eq_zero];
    intro h0
    have hM_zero : M_max = 0 := by
      simpa using congr_arg (LinearMap.toContinuousLinearMap (E := E) (F' := E)).symm h0
    have h : (∑ j, D.weight j • (D.map j).adjoint ∘ₗ D.reg j ∘ₗ D.map j).IsPositive :=
      .sum fun j => .smul_of_nonneg (.adjoint_conj (D.pos_reg j).1 (D.map j))
                        (D.weight j).coe_nonneg
    have hinner_zero : ∀ x, inner ℝ (D.loc x) x = 0 := fun x => by
      have := show inner ℝ (D.loc x) x +
          inner ℝ ((∑ j, D.weight j • (D.map j).adjoint ∘ₗ D.reg j ∘ₗ D.map j) x) x = 0 by
        simp only [M_max, ← inner_add_left, ← LinearMap.add_apply] at *; simp [hM_zero]
      linarith [D.pos_loc.1.inner_nonneg_left x, h.inner_nonneg_left x, this]
    have hT_zero : D.loc = 0 := D.pos_loc.1.isSymmetric.inner_map_self_eq_zero.mp hinner_zero
    haveI : Nontrivial E := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hE)
    exact D.pos_loc.2 (hT_zero ▸ LinearMap.det_zero'')
  · exact (ENNReal.coe_rpow_of_nonneg _ (div_nonneg β.2 (by norm_num)))
/- golfed -/

end BrascampLieb

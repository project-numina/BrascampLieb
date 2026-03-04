import BrascampLieb.ToMathlib.Analysis.InnerProductSpace.PosDef
import BrascampLieb.ToMathlib.Analysis.InnerProductSpace.SingularValue

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] {n} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n) [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (α : NNReal) (l : E →ₗ[𝕜] F)

lemma inner_lin_apply_apply (i j) :
    inner 𝕜 (l (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn i))
      (l (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn j)) =
    (l.isPositive_adjoint_comp_self.1.eigenvalues hn j : 𝕜) * inner 𝕜
      (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn i)
      (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn j) := by
  set l' := l.isPositive_adjoint_comp_self.1
  rw [← l.adjoint_inner_right, ← comp_apply, l'.apply_eigenvectorBasis, inner_smul_right]

lemma inner_lin_apply_ne {i j} (hij : i ≠ j) :
    inner 𝕜 (l (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn i))
      (l (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn j)) = 0 := by
  simp [l.inner_lin_apply_apply hn i j,
    (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn).inner_eq_zero hij]

noncomputable def EssRankAux :=
  Finset.univ.filter (fun i ↦ (α : ℝ) < l.singularValues hn i)

/- (by claude) Modified to count with multiplicity (number of indices with σ > α)
   rather than distinct values. This matches the geometric characterization in
   EssentialRank_eq_geometric and aligns with standard approximation theory definitions. -/
noncomputable def EssentialRank : ℕ := Finset.card <| l.EssRankAux hn α

lemma EssentialRank_eq : l.EssentialRank hn α = (l.EssRankAux hn α).card := rfl

@[simp]
lemma mem_EssRankAux {i} : i ∈ l.EssRankAux hn α ↔ (α : ℝ) < l.singularValues hn i := by
  simp [EssRankAux]

lemma mem_EssRankAux' {i} (hi : i ∈ l.EssRankAux hn α) :
    (α : ℝ) ^ 2 < (l.isPositive_adjoint_comp_self.1.eigenvalues hn i) := by
  convert (sq_lt_sq₀ α.coe_nonneg (Real.sqrt_nonneg _) |>.2 ((l.mem_EssRankAux hn α).1 hi)) using 1
  exact Real.sq_sqrt (l.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i) |>.symm

lemma mem_EssRank_pos {i} (hi : i ∈ l.EssRankAux hn α) :
    0 < l.singularValues hn i :=
  α.coe_nonneg.trans_lt <| by simpa [mem_EssRankAux] using hi

lemma mem_EssRankAux_apply_ne_zero {i} (hi : i ∈ l.EssRankAux hn α) :
    l ((l.isPositive_adjoint_comp_self).1.eigenvectorBasis hn i) ≠ 0 := fun h ↦ by
  let hl := l.isPositive_adjoint_comp_self.1
  refine (ne_of_gt <| Real.sqrt_pos.1 (α.coe_nonneg.trans_lt (l.mem_EssRankAux hn α |>.1 hi))) <| ?_
  rw [← RCLike.ofReal_re (K := 𝕜) (IsSymmetric.eigenvalues ..),
    ← mul_one (RCLike.ofReal _), ← (hl.eigenvectorBasis hn).inner_eq_one,
    ← inner_lin_apply_apply, inner_self_eq_norm_sq, h, sq_eq_zero_iff, norm_zero]

lemma EssRankAux_apply_lindep : LinearIndependent 𝕜 (fun i : l.EssRankAux hn α ↦
    l (l.isPositive_adjoint_comp_self.1.eigenvectorBasis hn i.1)) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => l.mem_EssRankAux_apply_ne_zero hn α i.2)
    <| fun ⟨i, _⟩ ⟨j, _⟩ hij => by simp [inner_lin_apply_apply,
      OrthonormalBasis.inner_eq_zero _ (Subtype.val_injective.ne hij)]

noncomputable def EssentialRankRestrict {m} (W : Submodule 𝕜 E)
    (hm : Module.finrank 𝕜 W = m) : ℕ :=
  (l.domRestrict W).EssentialRank hm α

end LinearMap

namespace BrascampLieb

structure Datum {J : Type*} [Fintype J]
    (E : Type*) [AddCommGroup E] [Module ℝ E]
    (F : J → Type*) [(i : J) → AddCommGroup (F i)] [(i : J) → Module ℝ (F i)]
  where
  map : (j : J) → E →ₗ[ℝ] (F j)
  weight : J → NNReal

noncomputable def Datum.AcuityWithin {J : Type*} [Fintype J] {E : Type*} {F : J → Type*} {m}
    [NormedAddCommGroup E] [(i : J) → NormedAddCommGroup (F i)]
    [InnerProductSpace ℝ E] [(i : J) → InnerProductSpace ℝ (F i)]
    [FiniteDimensional ℝ E] [(i : J) → FiniteDimensional ℝ (F i)]
    (D : Datum E F) (α : J → NNReal) (W : Submodule ℝ E) (hm : Module.finrank ℝ W = m) : NNReal :=
  ∑ j, D.weight j * (D.map j).EssentialRankRestrict (α j) W hm

noncomputable abbrev Datum.Acuity {J : Type*} [Fintype J]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : J → Type*} [(i : J) → AddCommGroup (F i)] [(i : J) → Module ℝ (F i)]
    (D : Datum E F) : NNReal :=
  ∑ j, D.weight j * Module.finrank ℝ (F j)

noncomputable def Datum.IsMetricPercep {J : Type*} [Fintype J] {E : Type*} {F : J → Type*}
    [NormedAddCommGroup E] [(i : J) → NormedAddCommGroup (F i)]
    [InnerProductSpace ℝ E] [(i : J) → InnerProductSpace ℝ (F i)]
    [FiniteDimensional ℝ E] [(i : J) → FiniteDimensional ℝ (F i)]
    (D : Datum E F) (α : J → NNReal) (β : NNReal) :=
  ∀ {m} (W : Submodule ℝ E) (hm : Module.finrank ℝ W = m),
    Module.finrank ℝ W ≤ D.AcuityWithin α W hm + β

structure locDatum {J : Type*} [Fintype J]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : J → Type*) [(j : J) → AddCommGroup (F j)] [(j : J) → Module ℝ (F j)]
  extends Datum E F where
  loc : E →ₗ[ℝ] E
  pos_loc : LinearMap.IsPosDef loc

structure locRegDatum {J : Type*} [Fintype J]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : J → Type*) [(j : J) → NormedAddCommGroup (F j)] [(j : J) → InnerProductSpace ℝ (F j)]
  extends locDatum E F where
  reg : (j : J) → F j →ₗ[ℝ] F j
  pos_reg: (j : J) → LinearMap.IsPosDef (reg j)

lemma loc_c_PosDef {J : Type*} [Fintype J]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (D : locDatum E F) (A : (j : J) → (F j) →ₗ[ℝ] (F j))
    (hA : (j : J) → LinearMap.IsPosDef (A j)) :
    (D.loc + ∑ j, (D.weight j : ℝ) • ((D.map j).adjoint ∘ₗ A j ∘ₗ D.map j)).IsPosDef :=
  .add_Positive D.pos_loc <| .sum fun i ↦ .smul_of_nonneg
    (.adjoint_conj (hA i).1 _) NNReal.zero_le_coe

noncomputable abbrev loc_constant_g_of {J : Type*} [Fintype J]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (D : locDatum E F) (A : (j : J) → (F j) →ₗ[ℝ] (F j))
    (hA : (j : J) → LinearMap.IsPosDef (A j)) : NNReal :=
  NNReal.sqrt ((∏ j : J, ⟨(A j).det, by classical exact (hA j).1.det_nonneg⟩ ^ (D.weight j : ℝ)) /
    ⟨LinearMap.det <| D.loc + ∑ j, (D.weight j : ℝ) • ((D.map j).adjoint ∘ₗ A j ∘ₗ D.map j),
    (loc_c_PosDef D A hA).det_pos.le⟩)

-- g stands for gaussian
noncomputable abbrev loc_reg_constant_g {J : Type*} [Fintype J] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {F : J → Type*}
    [(j : J) → NormedAddCommGroup (F j)] [(j : J) → InnerProductSpace ℝ (F j)]
    [(j : J) → FiniteDimensional ℝ (F j)] (D : locRegDatum E F) : ENNReal :=
  iSup <| fun A : {A : (j : J) → F j →ₗ[ℝ] F j // ∀ j,
    LinearMap.IsPosDef (A j) ∧ A j ≤ D.reg j } ↦
    loc_constant_g_of D.tolocDatum A (fun j ↦ (A.prop j).1)

end BrascampLieb

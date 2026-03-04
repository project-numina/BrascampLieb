import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! ## Section 3: Utility lemmas for NNReal and ENNReal -/

lemma NNReal.mul_inv_rev {a b : NNReal} : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact _root_.mul_inv_rev a b

lemma mainlem2 {a b c f g : NNReal} {q s : ℝ} (hq : 0 ≤ q) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (h : c ^ s * (a * (f ^ 2 / b) ^ s) ≤ g) :
    a ^ q ≤ b ^ (q * s) * c ^ (-(q * s)) * f ^ (-(q * s * 2)) * g ^ q := by
  apply_fun (NNReal.rpow · q) at h using NNReal.monotone_rpow_of_nonneg hq
  simp only [← mul_assoc, NNReal.mul_rpow, mul_comm _ (a ^ q)] at h
  rw [mul_assoc, ← le_mul_inv_iff₀ (mul_pos (NNReal.rpow_pos <| NNReal.rpow_pos hc)
    (NNReal.rpow_pos <| NNReal.rpow_pos (div_pos (sq_pos_of_pos hf) hb))), mul_comm] at h
  convert h using 2
  simp only [mul_comm q s, ← NNReal.rpow_mul, div_eq_mul_inv, NNReal.mul_rpow, NNReal.inv_rpow,
    ← NNReal.rpow_neg, neg_mul, NNReal.mul_inv_rev, neg_neg, ← mul_assoc,
    mul_comm _ (c ^ (-(s * q)))]
  congr 1
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, mul_comm, mul_neg, Nat.cast_two]

theorem NNReal.rpow_sum {x : NNReal} (hx : x ≠ 0)
  {ι : Type*} [Fintype ι] (y : ι → ℝ) : x^(∑ i, y i) = ∏ i, x ^ (y i) := by
  classical
  induction Finset.univ (α := ι) using Finset.induction_on <;> simp [*, NNReal.rpow_add hx]

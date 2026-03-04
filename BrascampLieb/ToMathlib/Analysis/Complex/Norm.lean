
import Mathlib.Analysis.Complex.Norm

open ComplexConjugate

theorem Complex.norm_sq_div_eq_conj {z : ℂ} :
    ‖z‖ ^ 2 / z = conj z := by
  by_cases h : z = 0
  · simp_all
  field_simp [h, <-Complex.normSq_eq_conj_mul_self]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem Complex.inv_eq_conj_div_norm_sq {z : ℂ} :
    z⁻¹ = conj z / ‖z‖ ^ 2 := by
  by_cases h : (‖z‖ : ℂ) ^ 2 = 0
  · simp_all
  have : z ≠ 0 := fun hz ↦ h (by simp [hz])
  field_simp
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, this]

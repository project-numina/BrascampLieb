import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Localization.Integer

open IsLocalization

theorem isInteger_neg {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {a : S}
    (ha : IsInteger R a) : IsInteger R (-a) :=
  ⟨- ha.choose, (algebraMap R S).map_neg _ ▸ congr_arg _ ha.choose_spec⟩

theorem isInteger_pow {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {a : S}
    (ha : IsInteger R a) (n : ℕ) : IsInteger R (a ^ n) :=
  Nat.recAux (pow_zero a ▸ isInteger_one) (fun _ ih ↦ pow_succ a _ ▸ (isInteger_mul ih ha)) n

lemma Rat.isInteger_of_exists_integer (q : ℚ) : IsInteger ℤ q ↔ ∃ x : ℤ, x = q := Iff.rfl

lemma Rat.isInteger_of_Nat (n : ℕ) : IsInteger ℤ (n : ℚ) := ⟨n, by norm_cast⟩

lemma Finset.sum_IsInteger {ι} [Fintype ι] (R R' : Type*) [CommSemiring R]
    [CommSemiring R'] [Algebra R R'] (f : ι → R') (h : ∀ i : ι, IsInteger R (f i)) :
    IsInteger R (∑ i, f i) := ⟨∑ i, (h i).choose, (map_sum (algebraMap R R') _ _) ▸
  (sum_congr rfl fun i _ ↦ (h i).choose_spec)⟩

theorem IsInteger_one_div_mul_of_dvd (n : ℕ) (x : ℤ) (hab : x ∣ n) (ha : 0 < x) :
    IsInteger ℤ (1 / x * n : ℚ) :=
  ⟨n / x, by simpa only [one_div_mul_eq_div] using Int.cast_div hab (by aesop)⟩

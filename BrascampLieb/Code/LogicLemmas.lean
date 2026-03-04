import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Finset.Fin

/-- Abstraction of the greedy index set construction
  The key is a decreasing induciton -/
lemma Fin.greedyIndexSet {n : ℕ} (p : Fin n → Finset (Fin n) → Prop)
    (hp : ∀ i, ∀ I, i ∈ I → p i I) :
    ∃ I : Finset (Fin n), (∀ i ∈ I, ¬ p i (I ∩ Finset.Ioi i)) ∧
    ∀ i : Fin n, p i (I ∩ Finset.Ici i) := by
  /- (by claude) Strengthen q to include constraint that I only contains indices ≥ k -/
  suffices ∀ m, m ≤ n → ∃ I : Finset (Fin n),
    (∀ i ∈ I, i ≥ m) ∧ (∀ i ∈ I, ¬ p i (I ∩ Finset.Ioi i)) ∧
    (∀ i : Fin n, i ≥ m → p i (I ∩ Finset.Ici i)) by
    obtain ⟨I, hI_ge, hI_neg, hI_pos⟩ := this 0 (Nat.zero_le n)
    exact ⟨I, hI_neg, by grind⟩
  intro m hm
  induction hm using Nat.decreasingInduction with
  | of_succ k hk ih =>
    obtain ⟨I, hI_ge, hI_neg, hI_pos⟩ := ih
    by_cases hpk : p ⟨k,hk⟩ I
    · /- Case: p ⟨k,hk⟩ I holds, so we don't add k to I -/
      refine ⟨I, by grind, hI_neg,
        fun i hik => (eq_or_lt_of_le hik).casesOn ?_ (fun h ↦ hI_pos i h)⟩
      · exact fun _ ↦ by convert hpk <;> grind
    · /- Case: ¬p ⟨k,hk⟩ I, so we add k to I -/
      refine ⟨insert ⟨k,hk⟩ I, by grind, ?_, by grind⟩
      simpa using ⟨by convert hpk; grind, fun i hi ↦ by convert hI_neg i hi using 2; grind⟩
  | self => exact ⟨∅, by simp⟩

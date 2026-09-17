import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
Counting components by their occurrences. Surjectivity ensures that every
component contains an occurrence. A component with more than one occurrence
uses at least two; only singleton fibers can save one in that accounting.
-/

namespace DeletionCode.ComponentFibers

open scoped BigOperators

/-- Exactly one occurrence maps to this component. -/
def SingletonFiber {A C : Type*} (f : A → C) (c : C) : Prop :=
  ∃ a, f a = c ∧ ∀ b, f b = c → b = a

noncomputable instance singletonFibersFintype {A C : Type*} [Fintype C]
    (f : A → C) : Fintype {c : C // SingletonFiber f c} := by
  classical
  exact Fintype.ofFinite _

noncomputable def fiber {A C : Type*} [Fintype A] (f : A → C) (c : C) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => f a = c)

@[simp] theorem mem_fiber {A C : Type*} [Fintype A] (f : A → C) (c : C) (a : A) :
    a ∈ fiber f c ↔ f a = c := by
  classical
  simp [fiber]

/-- The witness-based definition agrees with the cardinality of the actual fiber. -/
theorem fiber_card_eq_one_iff {A C : Type*} [Fintype A] (f : A → C) (c : C) :
    (fiber f c).card = 1 ↔ SingletonFiber f c := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hamem : a ∈ fiber f c := by rw [ha]; exact Finset.mem_singleton_self a
    refine ⟨a, (mem_fiber f c a).mp hamem, ?_⟩
    intro b hb
    have hbmem := (mem_fiber f c b).mpr hb
    rw [ha] at hbmem
    exact Finset.mem_singleton.mp hbmem
  · rintro ⟨a, ha, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨a, ?_⟩
    ext b
    simp only [mem_fiber, Finset.mem_singleton]
    constructor
    · exact huniq b
    · intro hb
      simpa only [hb] using ha

/-- The total size of the fibers is the number of occurrences. -/
theorem sum_fiber_card {A C : Type*} [Fintype A] [Fintype C] (f : A → C) :
    (∑ c : C, (fiber f c).card) = Fintype.card A := by
  classical
  simpa only [fiber, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
      (Finset.univ : Finset C) f

/-- Non-singleton components use at least two occurrences; surjectivity rules
out empty fibers, rather than assuming this lower bound on the count. -/
theorem singleton_fiber_count_bound {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (hsurj : Function.Surjective f) :
    2 * Fintype.card C ≤ Fintype.card A + Fintype.card {c : C // SingletonFiber f c} := by
  classical
  have hlocal (c : C) :
      2 ≤ (fiber f c).card + if SingletonFiber f c then 1 else 0 := by
    obtain ⟨a, ha⟩ := hsurj c
    have hpos : 0 < (fiber f c).card :=
      Finset.card_pos.mpr ⟨a, (mem_fiber f c a).mpr ha⟩
    by_cases hc : SingletonFiber f c
    · rw [ite_eq_left hc]
      omega
    · have hne : (fiber f c).card ≠ 1 := fun h => hc ((fiber_card_eq_one_iff f c).mp h)
      rw [ite_eq_right hc]
      omega
  have hsingle : (∑ c : C, if SingletonFiber f c then 1 else 0) =
      Fintype.card {c : C // SingletonFiber f c} := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    2 * Fintype.card C = ∑ _ : C, (2 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ c : C, ((fiber f c).card + if SingletonFiber f c then 1 else 0) :=
      Finset.sum_le_sum (fun c _ => hlocal c)
    _ = (∑ c : C, (fiber f c).card) + (∑ c : C, if SingletonFiber f c then 1 else 0) :=
      Finset.sum_add_distrib
    _ = Fintype.card A + Fintype.card {c : C // SingletonFiber f c} := by
      rw [sum_fiber_card, hsingle]

/-- The component bound used in the manuscript's savings-from-a-relation lemma. -/
theorem component_count_bound {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (hsurj : Function.Surjective f) (t R : ℕ)
    (hA : Fintype.card A = 2 * t * R)
    (hsingle : Fintype.card {c : C // SingletonFiber f c} ≤ 2 * t) :
    Fintype.card C ≤ t * R + t := by
  have h := singleton_fiber_count_bound f hsurj
  rw [hA, Nat.mul_assoc] at h
  omega

#print axioms fiber_card_eq_one_iff
#print axioms sum_fiber_card
#print axioms singleton_fiber_count_bound
#print axioms component_count_bound

end DeletionCode.ComponentFibers

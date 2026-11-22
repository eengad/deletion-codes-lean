import DeletionCode.Explicit.CoreCatalogue
import Mathlib.Data.List.FinRange

/-! Explicit serialization order for the finite replay-slot catalogue. -/

namespace DeletionCode.Explicit.CoreWeight.ReplayData

variable {ℓ q n t r₀ Γ : ℕ} (D : ReplayData ℓ q n t r₀ Γ)

private theorem sigma_nodup {α : Type*} {β : α → Type*} (xs : List α)
    (hn : xs.Nodup) (f : (a : α) → List (β a)) (hf : ∀ a, (f a).Nodup) :
    (xs.flatMap fun a => (f a).map (Sigma.mk a)).Nodup := by
  change List.Pairwise (· ≠ ·) _
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => (hf a).map (fun x y h => by cases h; rfl),?_⟩
  apply hn.imp
  intro a b hab x hx y hy
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
  exact fun h => hab (congrArg Sigma.fst h)

/-- List every slot in rule-count, description, and anchor order. -/
def slots (ℓ t r₀ Γ : ℕ) : List (Slot ℓ t r₀ Γ) :=
  (List.finRange r₀).flatMap fun r =>
    ((List.finRange Γ).product (List.finRange (ℓ^(t*(r.val+1))))).map (Sigma.mk r)

theorem slots_nodup : (slots ℓ t r₀ Γ).Nodup :=
  sigma_nodup _ (List.nodup_finRange _) _ (fun _ => (List.nodup_finRange _).product (List.nodup_finRange _))

@[simp] theorem mem_slots (r : Slot ℓ t r₀ Γ) : r ∈ slots ℓ t r₀ Γ := by
  obtain ⟨i,d,a⟩ := r
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr
    ⟨(d,a),List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩,rfl⟩⟩

private def assignments (k : Slot ℓ t r₀ Γ) : List (↥(D.support k) → Fin q) :=
  (List.finRange (q^(D.support k).card)).map fun i =>
    finFunctionFinEquiv.symm i ∘ ((D.support k).orderIsoOfFin rfl).symm

private theorem assignments_nodup (k : Slot ℓ t r₀ Γ) : (D.assignments k).Nodup := by
  apply (List.nodup_finRange _).map
  intro a b h
  apply finFunctionFinEquiv.symm.injective
  funext i
  simpa only [Function.comp_apply,OrderIso.symm_apply_apply] using
    congrFun h ((D.support k).orderIsoOfFin rfl i)

private theorem mem_assignments (k : Slot ℓ t r₀ Γ) (x : ↥(D.support k) → Fin q) :
    x ∈ D.assignments k := by
  unfold assignments
  refine List.mem_map.mpr ⟨finFunctionFinEquiv (x ∘ (D.support k).orderIsoOfFin rfl),List.mem_finRange _,?_⟩
  rw [Equiv.symm_apply_apply]
  funext p
  simp

/-- All assignment candidates, including any that fail their local replay checks. -/
def candidates : List D.Candidate :=
  (slots ℓ t r₀ Γ).flatMap fun k => (D.assignments k).map (Sigma.mk k)

theorem candidates_nodup : D.candidates.Nodup :=
  sigma_nodup _ slots_nodup D.assignments D.assignments_nodup

@[simp] theorem mem_candidates (i : D.Candidate) : i ∈ D.candidates := by
  obtain ⟨k,x⟩ := i
  exact List.mem_flatMap.mpr ⟨k,mem_slots k,List.mem_map.mpr ⟨x,D.mem_assignments k x,rfl⟩⟩

/-- The chronological catalogue loop emits each admissible index exactly once. -/
def indices : List D.Index :=
  D.candidates.filterMap fun c => if h : D.admissible c = true then some ⟨c,h⟩ else none

theorem indices_nodup : D.indices.Nodup := by
  unfold indices
  apply D.candidates_nodup.filterMap
  intro a b i ha hb
  split at ha
  next ha' =>
    split at hb
    next hb' =>
      have h₁ : ⟨a,ha'⟩ = i := by simpa using ha
      have h₂ : ⟨b,hb'⟩ = i := by simpa using hb
      exact congrArg Subtype.val (h₁.trans h₂.symm)
    next => simp at hb
  next => simp at ha

@[simp] theorem mem_indices (i : D.Index) : i ∈ D.indices := by
  apply List.mem_filterMap.mpr
  exact ⟨i.val,D.mem_candidates i.val,by simp [i.property]⟩

theorem sum_indices {A : Type*} [AddCommMonoid A] (f : D.Index → A) :
    (D.indices.map f).sum = ∑ i, f i := by
  classical
  have h : D.indices.toFinset = Finset.univ := by
    ext i
    simp
  rw [← List.sum_toFinset _ D.indices_nodup,h]

def table : List (Object ℓ q n) := D.indices.map D.object

#print axioms indices_nodup
#print axioms mem_indices

end DeletionCode.Explicit.CoreWeight.ReplayData

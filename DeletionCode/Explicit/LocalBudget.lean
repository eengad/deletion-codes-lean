import DeletionCode.Explicit.LetterSequence
import DeletionCode.Explicit.RulePatchCore

/-! Patch counting for `d:local-budget`. -/

namespace DeletionCode.Explicit.LocalBudget

open LetterSequence
open scoped BigOperators

variable {ℓ m c : ℕ} {α : Type*}

/-- A patch is a closed interval of original positions. Its marks are
the original positions removed by its gates. The patch labels run left to right. -/
structure Patches (ℓ c : ℕ) where
  first : Fin c → ℕ
  last : Fin c → ℕ
  inside : ∀ p, last p < ℓ
  ordered : ∀ {p q}, p < q → last p < first q
  marks : Fin c → Finset ℕ
  marks_inside : ∀ p, marks p ⊆ Finset.Icc (first p) (last p)

def Patches.positions (P : Patches ℓ c) (p : Fin c) : Finset ℕ :=
  Finset.Icc (P.first p) (P.last p)

def Patches.unmarked (P : Patches ℓ c) (p : Fin c) : Finset ℕ :=
  P.positions p \ P.marks p

theorem Patches.disjoint (P : Patches ℓ c) {p q : Fin c} (h : p ≠ q) :
    Disjoint (P.positions p) (P.positions q) := by
  rw [Finset.disjoint_left]
  intro a hp hq
  obtain ⟨hp₁,hp₂⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_Icc.mp hq
  rcases lt_or_gt_of_ne h with hpq | hqp
  · exact (not_lt_of_ge (hq₁.trans hp₂)) (P.ordered hpq)
  · exact (not_lt_of_ge (hp₁.trans hq₂)) (P.ordered hqp)

private def gateOf : Letter ℓ α → Option ℕ
  | .original _ => none
  | .fresh gate _ _ => some gate

/-- Fresh offsets charged to the patch containing their gate. -/
def freshIn (u : Lift ℓ m α) (owner : ℕ → Option (Fin c)) (p : Fin c) : Finset (Fin m) :=
  Finset.univ.filter fun i => (gateOf (u.letters i)).bind owner = some p

theorem mem_freshIn_iff {u : Lift ℓ m α} {owner : ℕ → Option (Fin c)} {i : Fin m} {p : Fin c} :
    i ∈ freshIn u owner p ↔ ∃ g k x, u.letters i = .fresh g k x ∧ owner g = some p := by
  constructor
  · intro h
    have hm := (Finset.mem_filter.mp h).2
    cases he : u.letters i with
    | original => simp [he,gateOf] at hm
    | fresh g k x => exact ⟨g,k,x,rfl,by simpa [he,gateOf] using hm⟩
  · rintro ⟨g,k,x,he,hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [he]
    exact hp

def encountered (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c)) :
    Finset (Fin c) :=
  Finset.univ.filter fun p => (u.positions ∩ P.positions p).Nonempty ∨ (freshIn u owner p).Nonempty

def middle (Q : Finset (Fin c)) : Finset (Fin c) :=
  Q.filter fun p => (∃ l ∈ Q, l < p) ∧ (∃ r ∈ Q, p < r)

theorem card_le_middle_add_two (Q : Finset (Fin c)) : Q.card ≤ (middle Q).card+2 := by
  by_cases h : Q.Nonempty
  · let l := Q.min' h
    let r := Q.max' h
    have hsub : Q ⊆ insert l (insert r (middle Q)) := by
      intro p hp
      by_cases hl : p = l
      · simp [hl]
      by_cases hr : p = r
      · simp [hr]
      have hlt : l < p := lt_of_le_of_ne (Q.min'_le _ hp) (Ne.symm hl)
      have hgt : p < r := lt_of_le_of_ne (Q.le_max' _ hp) hr
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨hp,⟨l,Q.min'_mem h,hlt⟩,⟨r,Q.max'_mem h,hgt⟩⟩))
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_insert_le l (insert r (middle Q))
    have h₃ := Finset.card_insert_le r (middle Q)
    omega
  · have h' : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [h']

private theorem positions_card_le (u : Lift ℓ m α) : u.positions.card ≤ m := by
  classical
  have h (p : ↥u.positions) : ∃ i : Fin m, (u.letters i).position.map Fin.val = some p.val := by
    obtain ⟨i,q,hq,he⟩ := u.mem_positions.mp p.property
    exact ⟨i,by simp [hq,he]⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro p q eq
    apply Subtype.ext
    exact Option.some.inj ((hf p).symm.trans (by rw [eq]; exact hf q))
  simpa using Fintype.card_le_of_injective f hinj

private theorem unmarked_lower (P : Patches ℓ c) {L cap : ℕ}
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hmark : ∀ p, (P.marks p).card ≤ cap)
    (hcap : 4*cap ≤ L) (p : Fin c) :
    L ≤ 4*(P.unmarked p).card := by
  have hsub : P.marks p ⊆ P.positions p := P.marks_inside p
  rw [Patches.unmarked,Finset.card_sdiff_of_subset hsub]
  have hw := hwidth p
  have hm := hmark p
  have hle := Finset.card_le_card (P.marks_inside p)
  change (P.marks p).card ≤ (P.positions p).card at hle
  omega

theorem at_most_twelve_middle (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    {L cap : ℕ} (hL : 0 < L) (hlen : m ≤ 3*L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hmark : ∀ p, (P.marks p).card ≤ cap) (hcap : 4*cap ≤ L)
    (hpresent : ∀ p ∈ middle (encountered u P owner), P.unmarked p ⊆ u.positions) :
    (middle (encountered u P owner)).card ≤ 12 := by
  classical
  let M := middle (encountered u P owner)
  have hdisj : (↑M : Set (Fin c)).PairwiseDisjoint P.unmarked := by
    intro p _ q _ hpq
    exact (P.disjoint hpq).mono Finset.sdiff_subset Finset.sdiff_subset
  have hsub : M.biUnion P.unmarked ⊆ u.positions := by
    intro a ha
    obtain ⟨p,hp,ha'⟩ := Finset.mem_biUnion.mp ha
    exact hpresent p hp ha'
  have hsum : ∑ p ∈ M, (P.unmarked p).card ≤ 3*L := by
    rw [← Finset.card_biUnion hdisj]
    exact (Finset.card_le_card hsub).trans ((positions_card_le u).trans hlen)
  have hlow : M.card * L ≤ 4 * (∑ p ∈ M, (P.unmarked p).card) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using
      (Finset.sum_le_sum (s := M) (fun p _ => unmarked_lower P hwidth hmark hcap p))
  have hbound : M.card * L ≤ 12*L := by omega
  exact Nat.le_of_mul_le_mul_right hbound hL

private theorem card_charged {β : Type*} [DecidableEq β] (Q : Finset (Fin c))
    (S : Finset β) (F : Fin c → Finset β) (cap : ℕ)
    (hS : S ⊆ Q.biUnion F) (hF : ∀ p ∈ Q, (F p).card ≤ cap)
    (hQ : Q.card ≤ 14) : S.card ≤ 14*cap := by
  calc
    S.card ≤ (Q.biUnion F).card := Finset.card_le_card hS
    _ ≤ ∑ p ∈ Q, (F p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Q, cap := Finset.sum_le_sum hF
    _ = Q.card * cap := by simp
    _ ≤ 14*cap := Nat.mul_le_mul_right cap hQ

/-- If every omitted position was marked, it belongs to an encountered
patch. An omitted position whose patch contains neither bounding original
letter would put the whole patch between them. Its unmarked letters then
occur on the lift. -/
theorem omissions_charged (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    (hmarked : u.omissions ⊆ (Finset.univ.biUnion P.marks))
    {L cap : ℕ} (hL : 0 < L) (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hmark : ∀ p, (P.marks p).card ≤ cap) (hcap : 4*cap ≤ L) :
    u.omissions ⊆ (encountered u P owner).biUnion P.marks := by
  intro a ha
  obtain ⟨p,_,hap⟩ := Finset.mem_biUnion.mp (hmarked ha)
  have he : p ∈ encountered u P owner := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,Or.inl ?_⟩
    by_contra hmiss
    have avoid (z : ℕ) (hz : z ∈ u.positions) : z ∉ P.positions p :=
      fun hm => hmiss ⟨z,Finset.mem_inter.mpr ⟨hz,hm⟩⟩
    obtain ⟨_,_,⟨lo,hlo,hla⟩,⟨hi,hhi,hah⟩⟩ := Finset.mem_filter.mp ha
    obtain ⟨hfa,hal⟩ := Finset.mem_Icc.mp (P.marks_inside p hap)
    have ll : lo < P.first p := by
      by_contra! he
      exact avoid lo hlo (Finset.mem_Icc.mpr ⟨he,by omega⟩)
    have hh : P.last p < hi := by
      by_contra! he
      exact avoid hi hhi (Finset.mem_Icc.mpr ⟨by omega,he⟩)
    have hpos : 0 < (P.unmarked p).card := by
      have := unmarked_lower P hwidth hmark hcap p
      omega
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzi,hzm⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzl,hzh⟩ := Finset.mem_Icc.mp hzi
    have hzpos : z ∈ u.positions := by
      by_contra hn
      have hzo : z ∈ u.omissions := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hzh.trans_lt (P.inside p)),hn,⟨lo,hlo,by omega⟩,⟨hi,hhi,by omega⟩⟩
      obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp (hmarked hzo)
      by_cases eq : p = q
      · subst q
        exact hzm hq
      · exact (Finset.disjoint_left.mp (P.disjoint eq)) hzi (P.marks_inside q hq)
    exact avoid z hzpos hzi
  exact Finset.mem_biUnion.mpr ⟨p,he,hap⟩

/-- The counting conclusion of `d:local-budget`. Geography enters only
through the unmarked letters of intermediate patches and the global
fact that omissions are marked. `cap` is the per-patch gate bound `s*b*R`. -/
theorem local_budget (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    {L cap : ℕ} (hL : 0 < L) (hlen : m ≤ 3*L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card) (hcap : 4*cap ≤ L)
    (hmark : ∀ p, (P.marks p).card ≤ cap)
    (hfresh : ∀ p, (freshIn u owner p).card ≤ cap)
    (howner : ∀ gate a symbol i, u.letters i = .fresh gate a symbol → ∃ p, owner gate = some p)
    (hmarked : u.omissions ⊆ (Finset.univ.biUnion P.marks))
    (hpresent : ∀ p ∈ middle (encountered u P owner), P.unmarked p ⊆ u.positions) :
    u.freshOffsets.card ≤ 14*cap ∧ u.omissions.card ≤ 14*cap := by
  let Q := encountered u P owner
  have hmid := at_most_twelve_middle u P owner hL hlen hwidth hmark hcap hpresent
  have hQ : Q.card ≤ 14 := (card_le_middle_add_two Q).trans (Nat.add_le_add_right hmid 2)
  have hc : u.freshOffsets ⊆ Q.biUnion (freshIn u owner) := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    cases hv : u.letters i with
    | original p => simp [hv,Letter.position] at hn
    | fresh gate a symbol =>
      obtain ⟨p,hp⟩ := howner gate a symbol i hv
      have hh : i ∈ freshIn u owner p := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        rw [hv]
        exact hp
      have hq : p ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ⟨i,hh⟩⟩
      exact Finset.mem_biUnion.mpr ⟨p,hq,hh⟩
  exact ⟨card_charged Q _ _ cap hc (fun p _ => hfresh p) hQ,
    card_charged Q _ _ cap (omissions_charged u P owner hmarked hL hwidth hmark hcap)
      (fun p _ => hmark p) hQ⟩

#print axioms at_most_twelve_middle
#print axioms omissions_charged
#print axioms local_budget

section Cuts

/-- A cut at an unmarked original position. Along the path the letters
before the cut form a prefix. The first edge leaving that prefix reaches
the original letter at the cut. The two ownership conditions situate fresh
letters whose patches lie entirely on one side of the cut. -/
structure OriginalCut (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    (z : Fin ℓ) where
  before : Letter ℓ α → Bool
  original : ∀ p, before (.original p) = decide (p < z)
  left_fresh : ∀ i gate k symbol p, u.letters i = .fresh gate k symbol →
    owner gate = some p → P.last p < z.val → before (.fresh gate k symbol) = true
  right_fresh : ∀ i gate k symbol p, u.letters i = .fresh gate k symbol →
    owner gate = some p → z.val < P.first p → before (.fresh gate k symbol) = false
  prefix_closed : ∀ i j, i ≤ j → before (u.letters j) = true → before (u.letters i) = true
  exit : ∀ i j : Fin m, j.val = i.val+1 →
    before (u.letters i) = true → before (u.letters j) = false → u.letters j = .original z

private theorem OriginalCut.visited {u : Lift ℓ m α} {P : Patches ℓ c}
    {owner : ℕ → Option (Fin c)} {z : Fin ℓ} (C : OriginalCut u P owner z)
    {i j : Fin m} (hi : C.before (u.letters i) = true)
    (hj : C.before (u.letters j) = false) : z.val ∈ u.positions := by
  have hij : i < j := by
    by_contra h
    have := C.prefix_closed j i (le_of_not_gt h) hi
    simp_all
  by_contra hmiss
  have hrun (k : ℕ) (hk : k < m) (hik : i.val ≤ k) :
      C.before (u.letters ⟨k,hk⟩) = true := by
    induction k with
    | zero =>
      have e : (⟨0,hk⟩ : Fin m) = i := Fin.ext (by change 0 = i.val; omega)
      simpa only [e] using hi
    | succ k ih =>
      by_cases hh : i.val ≤ k
      · have hprev : k < m := by omega
        have hp := ih hprev hh
        cases hc : C.before (u.letters ⟨k+1,hk⟩) with
        | true => rfl
        | false =>
          have hletter := C.exit ⟨k,hprev⟩ ⟨k+1,hk⟩ rfl hp hc
          exact (hmiss (u.mem_positions.mpr
            ⟨⟨k+1,hk⟩,z,by rw [hletter]; rfl,rfl⟩)).elim
      · have e : (⟨k+1,hk⟩ : Fin m) = i := Fin.ext (by change k+1 = i.val; omega)
        simpa only [e] using hi
  have ht : C.before (u.letters j) = true := hrun j.val j.isLt hij.le
  simp [hj] at ht

private theorem unmarked_globally (P : Patches ℓ c) {p : Fin c} {z : ℕ}
    (hz : z ∈ P.unmarked p) : z ∉ Finset.univ.biUnion P.marks := by
  intro hm
  obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨hzp,hzn⟩ := Finset.mem_sdiff.mp hz
  by_cases h : p = q
  · subst q
    exact hzn hq
  · exact (Finset.disjoint_left.mp (P.disjoint h)) hzp (P.marks_inside q hq)

private theorem OriginalCut.patch_left {u : Lift ℓ m α} {P : Patches ℓ c}
    {owner : ℕ → Option (Fin c)} {z : Fin ℓ} (C : OriginalCut u P owner z)
    {p : Fin c} (hp : p ∈ encountered u P owner) (h : P.last p < z.val) :
    ∃ i, C.before (u.letters i) = true := by
  rcases (Finset.mem_filter.mp hp).2 with ⟨a,ha⟩ | ⟨i,hi⟩
  · obtain ⟨ha₁,ha₂⟩ := Finset.mem_inter.mp ha
    obtain ⟨i,t,ht,ht'⟩ := u.mem_positions.mp ha₁
    have horig : u.letters i = .original t := by
      cases he : u.letters i <;> simp_all [Letter.position]
    have hp : t < z := by
      have hbound := (Finset.mem_Icc.mp ha₂).2
      change t.val < z.val
      omega
    exact ⟨i,by simp [horig,C.original,hp]⟩
  · have hm := (Finset.mem_filter.mp hi).2
    cases he : u.letters i with
    | original => simp [he,gateOf] at hm
    | fresh g k x =>
      exact ⟨i,by simpa only [he] using C.left_fresh i g k x p he (by simpa [he,gateOf] using hm) h⟩

private theorem OriginalCut.patch_right {u : Lift ℓ m α} {P : Patches ℓ c}
    {owner : ℕ → Option (Fin c)} {z : Fin ℓ} (C : OriginalCut u P owner z)
    {p : Fin c} (hp : p ∈ encountered u P owner) (h : z.val < P.first p) :
    ∃ i, C.before (u.letters i) = false := by
  rcases (Finset.mem_filter.mp hp).2 with ⟨a,ha⟩ | ⟨i,hi⟩
  · obtain ⟨ha₁,ha₂⟩ := Finset.mem_inter.mp ha
    obtain ⟨i,t,ht,ht'⟩ := u.mem_positions.mp ha₁
    have horig : u.letters i = .original t := by
      cases he : u.letters i <;> simp_all [Letter.position]
    have hp : ¬ t < z := by
      have hbound := (Finset.mem_Icc.mp ha₂).1
      change ¬ t.val < z.val
      omega
    exact ⟨i,by simp [horig,C.original,hp]⟩
  · have hm := (Finset.mem_filter.mp hi).2
    cases he : u.letters i with
    | original => simp [he,gateOf] at hm
    | fresh g k x =>
      exact ⟨i,by simpa only [he] using C.right_fresh i g k x p he (by simpa [he,gateOf] using hm) h⟩

/-- The same path-cut invariant supplies both geometric facts used by the
local count, including when the path's first or last letter is fresh. -/
theorem local_budget_of_cuts (u : Lift ℓ m α) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    {L cap : ℕ} (hL : 0 < L) (hlen : m ≤ 3*L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card) (hcap : 4*cap ≤ L)
    (hmark : ∀ p, (P.marks p).card ≤ cap)
    (hfresh : ∀ p, (freshIn u owner p).card ≤ cap)
    (howner : ∀ gate a symbol i, u.letters i = .fresh gate a symbol → ∃ p, owner gate = some p)
    (hcut : ∀ z : Fin ℓ, z.val ∉ Finset.univ.biUnion P.marks → Nonempty (OriginalCut u P owner z)) :
    u.freshOffsets.card ≤ 14*cap ∧ u.omissions.card ≤ 14*cap := by
  apply local_budget u P owner hL hlen hwidth hcap hmark hfresh howner
  · intro z hz
    by_contra h
    obtain ⟨hzr,hnot,⟨lo,hlo,hlz⟩,⟨hi,hhi,hzh⟩⟩ := Finset.mem_filter.mp hz
    let p : Fin ℓ := ⟨z,Finset.mem_range.mp hzr⟩
    obtain ⟨C⟩ := hcut p h
    obtain ⟨i,i₀,hi₀,he⟩ := u.mem_positions.mp hlo
    obtain ⟨j,j₀,hj₀,he'⟩ := u.mem_positions.mp hhi
    have ei : u.letters i = .original i₀ := by cases k : u.letters i <;> simp_all [Letter.position]
    have ej : u.letters j = .original j₀ := by cases k : u.letters j <;> simp_all [Letter.position]
    have hilt : i₀ < p := by change i₀.val < z; omega
    have hjlt : ¬ j₀ < p := by change ¬ j₀.val < z; omega
    exact hnot (C.visited (i := i) (j := j) (by simp [ei,C.original,hilt])
      (by simp [ej,C.original,hjlt]))
  · intro p hp z hz
    obtain ⟨_,⟨l,hl,hlp⟩,⟨r,hr,hpr⟩⟩ := Finset.mem_filter.mp hp
    obtain ⟨hzp,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzl,hzr⟩ := Finset.mem_Icc.mp hzp
    let q : Fin ℓ := ⟨z,hzr.trans_lt (P.inside p)⟩
    obtain ⟨C⟩ := hcut q (unmarked_globally P hz)
    obtain ⟨i,hi⟩ := C.patch_left hl ((P.ordered hlp).trans_le hzl)
    obtain ⟨j,hj⟩ := C.patch_right hr (hzr.trans_lt (P.ordered hpr))
    exact C.visited hi hj

#print axioms local_budget_of_cuts

end Cuts

section GateCounts

open RulePatch

variable {d s b R : ℕ}

/-- At most `s*R` bubble edges can touch a patch when its component has
at most `R` rule vertices. Multiplicity is retained by the edge indices. -/
theorem gates_per_patch (a : Incidence d s c) (p : Fin c)
    (rules : Finset (Fin d)) (hr : rules.card ≤ R)
    (hcomponent : ∀ i, (graph a).Reachable (.inl i) (.inr p) → i ∈ rules) :
    (atPatch a Finset.univ p).card ≤ s*R := by
  have hsub : atPatch a Finset.univ p ⊆ edges (s := s) rules := by
    intro e he
    have h := (Finset.mem_filter.mp he).2
    have hadj : (graph a).Adj (.inl e.1) (.inr p) := by
      change (SimpleGraph.fromRel (fun x y : Fin d ⊕ Fin c =>
        ∃ f : Fin d × Fin s, Sum.inl f.1 = x ∧ Sum.inr (a f) = y)).Adj _ _
      exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by simp,Or.inl ⟨e,rfl,congrArg Sum.inr h⟩⟩
    exact Finset.mem_product.mpr ⟨hcomponent e.1 hadj.reachable,Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [edges,Finset.card_product,Finset.card_univ,Fintype.card_fin] at hcard
  exact hcard.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left s hr)

/-- Charge the size of a patch inventory to its individual gates. -/
theorem sum_over_gates {β : Type*} [DecidableEq β] (a : Incidence d s c) (p : Fin c)
    (F : Fin d × Fin s → Finset β)
    (hgate : (atPatch a Finset.univ p).card ≤ s*R)
    (hsize : ∀ e ∈ atPatch a Finset.univ p, (F e).card ≤ b) :
    ((atPatch a Finset.univ p).biUnion F).card ≤ s*b*R := by
  calc
    _ ≤ ∑ e ∈ atPatch a Finset.univ p, (F e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ atPatch a Finset.univ p, b := Finset.sum_le_sum hsize
    _ = (atPatch a Finset.univ p).card*b := by simp
    _ ≤ s*R*b := Nat.mul_le_mul_right b hgate
    _ = s*b*R := by ring

/-- Marks gained in a patch are the union of the marks of its gates. -/
theorem marks_per_patch (a : Incidence d s c) (p : Fin c)
    (mark : Fin d × Fin s → Finset ℕ)
    (hgate : (atPatch a Finset.univ p).card ≤ s*R)
    (hmark : ∀ e, (mark e).card ≤ b) :
    ((atPatch a Finset.univ p).biUnion mark).card ≤ s*b*R :=
  sum_over_gates a p mark hgate (fun e _ => hmark e)

/-- The path offsets carrying fresh letters inserted by the given gate. -/
def freshAtGate (u : Lift ℓ m α) (gate : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => gateOf (u.letters i) = some gate

private theorem freshAtGate_le (u : Lift ℓ m α) (gate : ℕ)
    (hindex : ∀ i g k x, u.letters i = .fresh g k x → k < b)
    (hnorepeat : ∀ i j g k x y, u.letters i = .fresh g k x → u.letters j = .fresh g k y → i = j) :
    (freshAtGate u gate).card ≤ b := by
  let f (i : Fin m) := match u.letters i with
    | .original _ => 0
    | .fresh _ k _ => k
  have getu (i : Fin m) (hi : i ∈ freshAtGate u gate) :
      ∃ k x, u.letters i = .fresh gate k x := by
    have hm := (Finset.mem_filter.mp hi).2
    cases he : u.letters i with
    | original => simp [he,gateOf] at hm
    | fresh g k x =>
      have hg : g = gate := by simpa [he,gateOf] using hm
      subst g
      exact ⟨k,x,rfl⟩
  have hcard : (freshAtGate u gate).card ≤ (Finset.range b).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      obtain ⟨k,x,he⟩ := getu i hi
      exact Finset.mem_range.mpr (by simpa [f,he] using hindex i gate k x he)
    · intro i hi j hj he
      obtain ⟨k,x,h⟩ := getu i hi
      obtain ⟨k',y,h'⟩ := getu j hj
      have hk : k = k' := by simpa [f,h,h'] using he
      subst k'
      exact hnorepeat i j gate k x y h h'
  simpa using hcard

/-- A path has at most `s*b*R` fresh letters from a single patch if each
gate inserts at most `b` and an inserted letter is visited at most once. -/
theorem fresh_per_patch (a : Incidence d s c) (p : Fin c) (u : Lift ℓ m α)
    (id : Fin d × Fin s → ℕ) (owner : ℕ → Option (Fin c))
    (hgate : (atPatch a Finset.univ p).card ≤ s*R)
    (hindex : ∀ i g k x, u.letters i = .fresh g k x → k < b)
    (hnorepeat : ∀ i j g k x y, u.letters i = .fresh g k x → u.letters j = .fresh g k y → i = j)
    (hid : ∀ g, owner g = some p → ∃ e, a e = p ∧ id e = g) :
    (freshIn u owner p).card ≤ s*b*R := by
  have hsub : freshIn u owner p ⊆ (atPatch a Finset.univ p).biUnion (fun e => freshAtGate u (id e)) := by
    intro i hi
    have hm := (Finset.mem_filter.mp hi).2
    cases he : u.letters i with
    | original => simp [he,gateOf] at hm
    | fresh g k x =>
      have ho : owner g = some p := by simpa [he,gateOf] using hm
      obtain ⟨e,hp,heq⟩ := hid g ho
      have hem : e ∈ atPatch a Finset.univ p := by simp [atPatch,edges,hp]
      have hfresh : i ∈ freshAtGate u (id e) := by simp [freshAtGate,he,heq,gateOf]
      exact Finset.mem_biUnion.mpr ⟨e,hem,hfresh⟩
  exact (Finset.card_le_card hsub).trans
    (sum_over_gates a p _ hgate (fun e _ => freshAtGate_le u (id e) hindex hnorepeat))

#print axioms gates_per_patch
#print axioms marks_per_patch
#print axioms fresh_per_patch

end GateCounts

end DeletionCode.Explicit.LocalBudget

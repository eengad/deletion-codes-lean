import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat

/-! Original and fresh letters, and alignment on a strong source
(manuscript `d:token-word` and `d:aligned`). -/

namespace DeletionCode.Explicit.LetterSequence

inductive Letter (ℓ : ℕ) (α : Type*) where
  | original (p : Fin ℓ)
  | fresh (entry offset : ℕ) (a : α)
  deriving DecidableEq

variable {ℓ m : ℕ} {α : Type*}

def Letter.position : Letter ℓ α → Option (Fin ℓ)
  | .original p => some p
  | .fresh .. => none

def Letter.symbol (x : Fin ℓ → α) : Letter ℓ α → α
  | .original p => x p
  | .fresh _ _ a => a

/-- A lift spells its original letters from the source and its fresh letters
from the recorded gate. Only positions of original letters must increase. -/
structure Lift (ℓ m : ℕ) (α : Type*) where
  letters : Fin m → Letter ℓ α
  increasing : ∀ {i j p q}, i < j → (letters i).position = some p →
    (letters j).position = some q → p < q

def Lift.spelling (u : Lift ℓ m α) (x : Fin ℓ → α) : Fin m → α :=
  fun i => (u.letters i).symbol x

def Lift.freshOffsets (u : Lift ℓ m α) : Finset (Fin m) :=
  Finset.univ.filter fun i => (u.letters i).position = none

private theorem Lift.position_injective (u : Lift ℓ m α) {i j : Fin m} {p : Fin ℓ}
    (hi : (u.letters i).position = some p) (hj : (u.letters j).position = some p) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (lt_irrefl p (u.increasing h hi hj)).elim
  · exact h
  · exact (lt_irrefl p (u.increasing h hj hi)).elim

private def Lift.positionsAt (u : Lift ℓ m α) (S : Finset (Fin m)) : Finset ℕ :=
  S.filterMap (fun i => (u.letters i).position.map Fin.val) (by
    intro i j p hi hj
    cases hp : (u.letters i).position with
    | none => simp [hp] at hi
    | some a =>
      cases hq : (u.letters j).position with
      | none => simp [hq] at hj
      | some b =>
        simp [hp,hq] at hi hj
        have h : a = b := Fin.ext (hi.trans hj.symm)
        exact u.position_injective hp (h ▸ hq))

def Lift.positions (u : Lift ℓ m α) : Finset ℕ := u.positionsAt Finset.univ

private theorem Lift.mem_positionsAt (u : Lift ℓ m α) (S : Finset (Fin m)) {p : ℕ} :
    p ∈ u.positionsAt S ↔
      ∃ (i : Fin m) (q : Fin ℓ), i ∈ S ∧ (u.letters i).position = some q ∧ q.val = p := by
  rw [positionsAt,Finset.mem_filterMap]
  constructor
  · rintro ⟨i,hi,h⟩
    cases he : (u.letters i).position with
    | none => simp [he] at h
    | some q => exact ⟨i,q,hi,he,by simpa [he] using h⟩
  · rintro ⟨i,q,hi,h,rfl⟩
    exact ⟨i,hi,by simp [h]⟩

theorem Lift.mem_positions (u : Lift ℓ m α) {p : ℕ} :
    p ∈ u.positions ↔ ∃ (i : Fin m) (q : Fin ℓ), (u.letters i).position = some q ∧ q.val = p := by
  simp [positions,mem_positionsAt]

/-- Positions strictly between the first and last original letters that
are missing from the lift. The set is empty when fewer than two are used. -/
def Lift.omissions (u : Lift ℓ m α) : Finset ℕ :=
  let P := u.positions
  (Finset.range ℓ).filter (fun p => p ∉ P ∧ (∃ q ∈ P, q < p) ∧ (∃ q ∈ P, p < q))

private theorem Lift.offset_le (u : Lift ℓ m α) {i j : Fin m} {p q : Fin ℓ}
    (hp : (u.letters i).position = some p) (hq : (u.letters j).position = some q)
    (hle : p ≤ q) : i ≤ j := by
  by_contra h
  exact (not_lt_of_ge hle) (u.increasing (lt_of_not_ge h) hq hp)

/-- The span of an interval of original positions is bounded by the
corresponding number of offsets plus the number of omitted positions. -/
theorem Lift.span_le (u : Lift ℓ m α) {i j : Fin m} {p q : Fin ℓ}
    (hij : i ≤ j) (hp : (u.letters i).position = some p) (hq : (u.letters j).position = some q) :
    q.val + 1 - p.val ≤ j.val + 1 - i.val + u.omissions.card := by
  classical
  let I := Finset.Icc p.val q.val
  let hit := I ∩ u.positions
  let indices := Finset.Icc i j
  have hhit : hit ⊆ u.positionsAt indices := by
    intro a ha
    obtain ⟨haI,haP⟩ := Finset.mem_inter.mp ha
    obtain ⟨k,r,hr,rfl⟩ := u.mem_positions.mp haP
    obtain ⟨hpr,hrq⟩ := Finset.mem_Icc.mp haI
    exact (u.mem_positionsAt indices).mpr ⟨k,r,Finset.mem_Icc.mpr
      ⟨u.offset_le hp hr hpr,u.offset_le hr hq hrq⟩,hr,rfl⟩
  have hval : (u.positionsAt indices).card ≤ indices.card := by
    have h (p : ↥(u.positionsAt indices)) : ∃ i : ↥indices,
        (u.letters i.val).position.map Fin.val = some p.val := by
      obtain ⟨i,q,hi,hq,e⟩ := (u.mem_positionsAt indices).mp p.property
      exact ⟨⟨i,hi⟩,by simp [hq,e]⟩
    choose f hf using h
    have hinj : Function.Injective f := by
      intro p q he
      apply Subtype.ext
      exact Option.some.inj ((hf p).symm.trans (by rw [he]; exact hf q))
    simpa using Fintype.card_le_of_injective f hinj
  have hmissing : I \ hit ⊆ u.omissions := by
    intro a ha
    obtain ⟨haI,haH⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hp₀,hq₀⟩ := Finset.mem_Icc.mp haI
    have haP : a ∉ u.positions := fun h => haH (Finset.mem_inter.mpr ⟨haI,h⟩)
    have pP : p.val ∈ u.positions := u.mem_positions.mpr ⟨i,p,hp,rfl⟩
    have qP : q.val ∈ u.positions := u.mem_positions.mpr ⟨j,q,hq,rfl⟩
    have hlt : p.val < a := lt_of_le_of_ne hp₀ (fun h => haP (h ▸ pP))
    have hgt : a < q.val := lt_of_le_of_ne hq₀ (fun h => haP (h.symm ▸ qP))
    simp only [omissions,Finset.mem_filter,Finset.mem_range]
    exact ⟨lt_of_le_of_lt hq₀ q.isLt,haP,⟨_,pP,hlt⟩,⟨_,qP,hgt⟩⟩
  have hcount := (Finset.card_le_card hhit).trans hval
  have hbound := Finset.card_le_card hmissing
  have hhit_sub : hit ⊆ I := Finset.inter_subset_left
  rw [Finset.card_sdiff_of_subset hhit_sub] at hbound
  have hsub := Finset.card_le_card (s := hit) (t := I) Finset.inter_subset_left
  have hI : I.card = q.val + 1 - p.val := Nat.card_Icc _ _
  have hJ : indices.card = j.val + 1 - i.val := Fin.card_Icc _ _
  omega

/-- Extent is inclusive of both endpoints. A pairwise statement also covers
an empty list of positions. -/
def ExtentLE {K : ℕ} (f : Fin K → Fin ℓ) (B : ℕ) : Prop :=
  ∀ i j, (f j).val + 1 ≤ (f i).val + B

/-- A strong source has no pair of increasing nearby position lists of
length `K` with the same spelling and distinct positions at every offset. -/
def Strong (x : Fin ℓ → α) (K Λ : ℕ) : Prop :=
  ∀ (f g : Fin K → Fin ℓ), StrictMono f → StrictMono g →
    ExtentLE f (K+3*Λ) → ExtentLE g (K+3*Λ) →
    (∀ i, f i ≠ g i) → (∀ i, x (f i) = x (g i)) → False

private theorem original_of_not_fresh (u : Lift ℓ m α) {i : Fin m} (h : i ∉ u.freshOffsets) :
    ∃ p, (u.letters i).position = some p := by
  cases he : (u.letters i).position with
  | none => exact False.elim (h (by simp [Lift.freshOffsets,he]))
  | some p => exact ⟨p,rfl⟩

private theorem spelled_original (u : Lift ℓ m α) (x : Fin ℓ → α) {i : Fin m} {p : Fin ℓ}
    (h : (u.letters i).position = some p) : u.spelling x i = x p := by
  cases he : u.letters i <;> simp_all [Lift.spelling, Letter.position, Letter.symbol]

/-- Equal spellings of bounded lifts on a strong source share an original
letter within the first `K+2Λ` offsets (`d:aligned`). -/
theorem aligned {x : Fin ℓ → α} {K Λ : ℕ} (hstrong : Strong x K Λ)
    (u v : Lift ℓ m α) (hlen : K+2*Λ ≤ m) (hspell : u.spelling x = v.spelling x)
    (huf : u.freshOffsets.card ≤ Λ) (hvf : v.freshOffsets.card ≤ Λ)
    (huo : u.omissions.card ≤ Λ) (hvo : v.omissions.card ≤ Λ) :
    ∃ (i : Fin m) (p : Fin ℓ), i.val < K+2*Λ ∧
      (u.letters i).position = some p ∧ (v.letters i).position = some p := by
  classical
  by_contra hno
  let B := K+2*Λ
  let initial := (Finset.univ : Finset (Fin B)).map (Fin.castLEEmb hlen)
  let bad := u.freshOffsets ∪ v.freshOffsets
  let both := initial \ bad
  have cp : initial.card = B := by simp [initial,B]
  have cb : bad.card ≤ 2*Λ := (Finset.card_union_le _ _).trans (by omega)
  have hK : K ≤ both.card := by
    have h := Finset.le_card_sdiff bad initial
    change K ≤ (initial \ bad).card
    dsimp only [B] at cp
    omega
  let off : Fin K → Fin m := fun j => both.orderEmbOfFin rfl (Fin.castLE hK j)
  have ho : StrictMono off := (both.orderEmbOfFin rfl).strictMono.comp (Fin.castLEOrderEmb hK).strictMono
  have nei (j : Fin K) : off j ∈ both := both.orderEmbOfFin_mem rfl _
  have bound (j : Fin K) : (off j).val < K+2*Λ := by
    have hm : off j ∈ initial := (Finset.mem_sdiff.mp (nei j)).1
    obtain ⟨z,_,hz⟩ := Finset.mem_map.mp hm
    rw [← hz]
    exact z.isLt
  have uorig (j : Fin K) : ∃ p, (u.letters (off j)).position = some p :=
    original_of_not_fresh u (fun h => (Finset.mem_sdiff.mp (nei j)).2 (Finset.mem_union_left _ h))
  have vorig (j : Fin K) : ∃ p, (v.letters (off j)).position = some p :=
    original_of_not_fresh v (fun h => (Finset.mem_sdiff.mp (nei j)).2 (Finset.mem_union_right _ h))
  choose f hf using uorig
  choose g hg using vorig
  have mono (w : Lift ℓ m α) (a : Fin K → Fin ℓ)
      (ha : ∀ j, (w.letters (off j)).position = some (a j)) : StrictMono a :=
    fun i j h => w.increasing (ho h) (ha i) (ha j)
  have extent (w : Lift ℓ m α) (a : Fin K → Fin ℓ)
      (ha : ∀ j, (w.letters (off j)).position = some (a j)) (hc : w.omissions.card ≤ Λ) :
      ExtentLE a (K+3*Λ) := by
    intro i j
    by_cases hij : i ≤ j
    · have hs := w.span_le (ho.monotone hij) (ha i) (ha j)
      have hj := bound j
      omega
    · have he := mono w a ha (lt_of_not_ge hij)
      have hk : 0 < K := Nat.zero_lt_of_lt i.isLt
      omega
  exact hstrong f g (mono u f hf) (mono v g hg) (extent u f hf huo) (extent v g hg hvo)
    (fun j h => hno ⟨off j,f j,bound j,hf j,h.symm ▸ hg j⟩)
    (fun j => (spelled_original u x (hf j)).symm.trans
      ((congrFun hspell (off j)).trans (spelled_original v x (hg j))))

/-- A window beginning at offset `a` has the same letters and preserves
the ordering of original positions. -/
def Lift.window (u : Lift ℓ m α) (a k : ℕ) (hk : a+k ≤ m) : Lift ℓ k α where
  letters i := u.letters ⟨a+i.val,by omega⟩
  increasing hij hp hq :=
    u.increasing (show (⟨a+_,_⟩ : Fin m) < ⟨a+_,_⟩ from Nat.add_lt_add_left hij a) hp hq

theorem Lift.window_positions_subset (u : Lift ℓ m α) {a k : ℕ} (hk : a+k ≤ m) :
    (u.window a k hk).positions ⊆ u.positions := by
  intro p hp
  obtain ⟨i,q,hi,rfl⟩ := (u.window a k hk).mem_positions.mp hp
  exact u.mem_positions.mpr ⟨⟨a+i.val,by omega⟩,q,hi,rfl⟩

theorem Lift.window_fresh_le (u : Lift ℓ m α) {a k : ℕ} (hk : a+k ≤ m) :
    (u.window a k hk).freshOffsets.card ≤ u.freshOffsets.card := by
  let f (i : Fin k) : Fin m := ⟨a+i.val,by omega⟩
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin m => z.val) h))

theorem Lift.window_omissions_subset (u : Lift ℓ m α) {a k : ℕ} (hk : a+k ≤ m) :
    (u.window a k hk).omissions ⊆ u.omissions := by
  let w := u.window a k hk
  intro p hp
  obtain ⟨hr,hn,⟨lo,hlo,hlp⟩,⟨hi,hhi,hph⟩⟩ := Finset.mem_filter.mp hp
  have hsub := u.window_positions_subset hk
  have hnot : p ∉ u.positions := by
    intro hp'
    obtain ⟨j,z,hj,rfl⟩ := u.mem_positions.mp hp'
    obtain ⟨i₀,z₀,h₀,e₀⟩ := w.mem_positions.mp hlo
    obtain ⟨i₁,z₁,h₁,e₁⟩ := w.mem_positions.mp hhi
    have hl := u.offset_le (i := ⟨a+i₀.val,by omega⟩) h₀ hj (by omega)
    have hh := u.offset_le (j := ⟨a+i₁.val,by omega⟩) hj h₁ (by omega)
    change a+i₀.val ≤ j.val at hl
    change j.val ≤ a+i₁.val at hh
    have he : (⟨a+(j.val-a),by omega⟩ : Fin m) = j := Fin.ext (Nat.add_sub_of_le (by omega : a ≤ j.val))
    apply hn
    exact w.mem_positions.mpr ⟨⟨j.val-a,by omega⟩,z,by simpa only [w,window,he] using hj,rfl⟩
  exact Finset.mem_filter.mpr ⟨hr,hnot,⟨lo,hsub hlo,hlp⟩,⟨hi,hsub hhi,hph⟩⟩

/-- Equal windows of two lifts have occurrences of the same original
letter. Hence any creation intervals enclosing the original positions
of these lifts intersect (`d:supplier-retention`, first step). -/
theorem creation_intersects {x : Fin ℓ → α} {K Λ m₁ m₂ a b k : ℕ}
    (hstrong : Strong x K Λ) (u : Lift ℓ m₁ α) (v : Lift ℓ m₂ α)
    (hu : a+k ≤ m₁) (hv : b+k ≤ m₂) (hk : K+2*Λ ≤ k)
    (hspell : (u.window a k hu).spelling x = (v.window b k hv).spelling x)
    (huf : u.freshOffsets.card ≤ Λ) (hvf : v.freshOffsets.card ≤ Λ)
    (huo : u.omissions.card ≤ Λ) (hvo : v.omissions.card ≤ Λ)
    (I J : Finset ℕ) (hI : u.positions ⊆ I) (hJ : v.positions ⊆ J) :
    (I ∩ J).Nonempty := by
  obtain ⟨i,p,_,ha,hb⟩ := aligned hstrong _ _ hk hspell
    ((u.window_fresh_le hu).trans huf) ((v.window_fresh_le hv).trans hvf)
    ((Finset.card_le_card (u.window_omissions_subset hu)).trans huo)
    ((Finset.card_le_card (v.window_omissions_subset hv)).trans hvo)
  exact ⟨p.val,Finset.mem_inter.mpr
    ⟨hI (u.window_positions_subset hu ((u.window a k hu).mem_positions.mpr ⟨i,p,ha,rfl⟩)),
      hJ (v.window_positions_subset hv ((v.window b k hv).mem_positions.mpr ⟨i,p,hb,rfl⟩))⟩⟩

#print axioms Lift.window_omissions_subset
#print axioms creation_intersects

#print axioms Lift.span_le
#print axioms aligned

end DeletionCode.Explicit.LetterSequence

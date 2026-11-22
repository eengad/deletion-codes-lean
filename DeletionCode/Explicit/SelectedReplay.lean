import DeletionCode.Explicit.LiftDictionary
import DeletionCode.Explicit.LetterGraphCuts

/-! Apply the old letter-graph budget at every splice in `d:selected-replay`. -/

namespace DeletionCode.Explicit.SelectedReplay

open LetterSequence ReplayEntry LetterGraphCuts LocalBudget

variable {ℓ m c : ℕ} {α : Type*} {E : Letter ℓ α → Letter ℓ α → Prop}

private theorem original_edges [DecidableEq α] {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) : ∀ {a b}, originalEdges a b → E a b := by
  induction H with
  | initial => exact fun h => h
  | gate prior left right removed fresh hpath hl hr hd hnew hfresh ih =>
    intro a b h
    exact Or.inl (ih h)

theorem read_follows [DecidableEq α] {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) {L current rule : ℕ} {anchor : Option (Fin ℓ)}
    {get : ℕ → Option (Completed ℓ α)} {ref : Reference} {u : Lift ℓ L α}
    (hold : ∀ j e, get j = some e → ∀ side, (e.lift side).2.Follows E)
    (h : Reads L current rule anchor get ref u) : u.Follows E := by
  cases h with
  | source root delta ha hs hb =>
    intro i j hj
    apply original_edges H
    change ((root.val : ℤ)+delta).toNat+j.val = ((root.val : ℤ)+delta).toNat+i.val+1
    omega
  | supplier j side a e hj he hr hw =>
    exact Lift.window_follows _ (hold j e he side) a L hw

/-- All vertices of lifts of at least two letters are incident to an edge. -/
def Incident (E : Letter ℓ α → Letter ℓ α → Prop) (v : Letter ℓ α) : Prop :=
  ∃ w, E v w ∨ E w v

private theorem incident_of_follows (u : Lift ℓ m α) (h : u.Follows E) (hm : 2 ≤ m)
    (i : Fin m) : Incident E (u.letters i) := by
  by_cases hi : i.val+1 < m
  · let j : Fin m := ⟨i.val+1,hi⟩
    exact ⟨u.letters j,Or.inl (h i j rfl)⟩
  · let j : Fin m := ⟨i.val-1,by omega⟩
    exact ⟨u.letters j,Or.inr (h j i (by change i.val=i.val-1+1; omega))⟩

theorem reaches_of_follows (u : Lift ℓ m α) (h : u.Follows E)
    {i j : Fin m} (hij : i < j) : Relation.TransGen E (u.letters i) (u.letters j) := by
  have reach (k : ℕ) (hk : k<m) (hi : i.val<k) :
      Relation.TransGen E (u.letters i) (u.letters ⟨k,hk⟩) := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases he : i.val = k
      · exact .single (h i ⟨k+1,hk⟩ (by change k+1 = i.val+1; omega))
      · have hp : k < m := by omega
        exact (ih hp (by omega)).tail (h ⟨k,hp⟩ ⟨k+1,hk⟩ rfl)
  exact reach j.val j.isLt hij

private theorem follows_injective (u : Lift ℓ m α) (h : u.Follows E)
    (hacyclic : ∀ v, ¬ Relation.TransGen E v v) : Function.Injective u.letters := by
  intro i j he
  rcases lt_trichotomy i j with hb | hb | hb
  · have hr := reaches_of_follows u h hb
    rw [he] at hr
    exact (hacyclic _ hr).elim
  · exact hb
  · have hr := reaches_of_follows u h hb
    rw [he] at hr
    exact (hacyclic _ hr).elim

/-- The old graph's fresh vertices belong to their owners' inventories and
have brackets inside those patches. This is independent of the path used to
visit the vertices. -/
def FreshInventory (E : Letter ℓ α → Letter ℓ α → Prop) (P : Patches ℓ c)
    (owner : ℕ → Option (Fin c)) [DecidableEq α] (stock : Fin c → Finset (Letter ℓ α)) : Prop :=
  ∀ gate offset symbol, Incident E (.fresh gate offset symbol) →
    ∃ p, owner gate = some p ∧ .fresh gate offset symbol ∈ stock p ∧
      HasBrackets E P p (.fresh gate offset symbol)

theorem old_graph_path_budget [DecidableEq α] {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    (stock : Fin c → Finset (Letter ℓ α)) {L cap : ℕ} (hL : 2 ≤ L)
    (hwidth : ∀ p, L ≤ 2*(P.positions p).card) (hcap : 4*cap ≤ L)
    (hmark : ∀ p, (P.marks p).card ≤ cap) (hstock : ∀ p, (stock p).card ≤ cap)
    (hmarked : ∀ z ∈ marked, z.val ∈ Finset.univ.biUnion P.marks)
    (hinventory : FreshInventory E P owner stock)
    (u : Lift ℓ m α) (hlo : L ≤ m) (hshort : m ≤ 3*L) (hstep : u.Follows E) :
    u.freshOffsets.card ≤ 14*cap ∧ u.omissions.card ≤ 14*cap := by
  have hv (i : Fin m) := incident_of_follows u hstep (hL.trans hlo) i
  have hf (p : Fin c) : (freshIn u owner p).card ≤ cap := by
    have hle : (freshIn u owner p).card ≤ (stock p).card := by
      apply Finset.card_le_card_of_injOn u.letters
      · intro i hi
        obtain ⟨g,a,x,he,ho⟩ := mem_freshIn_iff.mp hi
        obtain ⟨q,hq,hstock',_⟩ := hinventory g a x (he ▸ hv i)
        have hqp := Option.some.inj (hq.symm.trans ho)
        subst q
        rw [he]
        exact hstock'
      · intro i _ j _ he
        exact follows_injective u hstep H.acyclic he
    exact hle.trans (hstock p)
  have hown : ∀ gate a symbol i, u.letters i = .fresh gate a symbol → ∃ p, owner gate = some p := by
    intro gate a symbol i he
    obtain ⟨p,hp,_,_⟩ := hinventory gate a symbol (he ▸ hv i)
    exact ⟨p,hp⟩
  apply H.local_budget u P owner (by omega) hshort hwidth hcap hmark hf hown hmarked hstep
  intro i g a x p he ho
  obtain ⟨q,hq,_,hb⟩ := hinventory g a x (he ▸ hv i)
  have hqp := Option.some.inj (hq.symm.trans ho)
  subst q
  exact hb

/-- Selected windows from the old graph replay to a lift of the prescribed
negative local word. The same old-graph budget applies after the first splice. -/
theorem negativeLift_of_history [DecidableEq α] {marked : Finset (Fin ℓ)}
    (H : History ℓ α E marked) (P : Patches ℓ c) (owner : ℕ → Option (Fin c))
    (stock : Fin c → Finset (Letter ℓ α)) {K Λ L cap current : ℕ} {x : Fin ℓ → α}
    (hx : Strong x K Λ) (hL : 2 ≤ L) (hwidth : ∀ p, L ≤ 2*(P.positions p).card)
    (hcap : 4*cap ≤ L) (hΛ : 14*cap ≤ Λ)
    (hmark : ∀ p, (P.marks p).card ≤ cap) (hstock : ∀ p, (stock p).card ≤ cap)
    (hmarked : ∀ z ∈ marked, z.val ∈ Finset.univ.biUnion P.marks)
    (hinventory : FreshInventory E P owner stock)
    (e : Entry α) (word : Fin e.negativeLength → α) (anchor : Option (Fin ℓ))
    (get : ℕ → Option (Completed ℓ α))
    (hold : ∀ j e, get j = some e → ∀ side, (e.lift side).2.Follows E)
    (hlen : L ≤ e.negativeLength) (hshort : e.negativeLength ≤ 3*L)
    (hroom : (e.negativeLength-L+1)/2 + (K+2*Λ) ≤ L)
    (hreads : List.Forall₂ (fun a ref => ∃ v, Reads L current e.rule anchor get ref v ∧
      SpellsAt v x word a) (selectedStarts L e.negativeLength) e.references) :
    ∃ out, negativeLift L current e anchor get = some out ∧ SpellsAt out x word 0 ∧ out.Follows E := by
  apply negativeLift_on_graph hx E e word anchor get hlen hshort hroom
  · intro m u hm hs he
    obtain ⟨hf,ho⟩ := old_graph_path_budget H P owner stock hL hwidth hcap hmark hstock
      hmarked hinventory u hm hs he
    exact ⟨hf.trans hΛ,ho.trans hΛ⟩
  · generalize selectedStarts L e.negativeLength = starts at hreads ⊢
    generalize e.references = refs at hreads ⊢
    induction hreads with
    | nil => exact .nil
    | cons hfirst _ ih =>
      obtain ⟨v,hd,hs⟩ := hfirst
      exact .cons ⟨v,read_of_reads hd,hs,read_follows H hold hd⟩ ih

#print axioms negativeLift_of_history

/-- Convert the ordered dictionary results into the hypotheses for
`negativeLift_of_history`. Only the source offsets change when the anchor
is chosen. The referenced lifts and their spellings stay the same. -/
theorem dictionary_reads (pad : α) (x : Fin ℓ → α) {n L current rule : ℕ}
    (word : Fin n → α) (root : Fin ℓ) (get : ℕ → Option (Completed ℓ α))
    {starts : List ℕ} {os : List (LiftDictionary.Occurrence ℓ L α)}
    (hstarts : ∀ a ∈ starts, a+L ≤ n)
    (hmatch : List.Forall₂ (fun a (o : LiftDictionary.Occurrence ℓ L α) =>
      o.lift.spelling x = Qary.SignedSupport.gram (LiftDictionary.paddedLetters pad word) L a ∧
      Reads L current rule (some root) get (o.location.reference root) o.lift) starts os) :
    List.Forall₂ (fun a ref => ∃ v, Reads L current rule (some root) get ref v ∧ SpellsAt v x word a)
      starts (os.map (fun o => o.location.reference root)) := by
  induction hmatch with
  | nil => exact .nil
  | @cons a o as os hfirst hrest ih =>
    refine .cons ⟨o.lift,hfirst.2,hstarts a (List.mem_cons_self ..),?_⟩
      (ih (fun j hj => hstarts j (List.mem_cons_of_mem _ hj)))
    intro i j he
    have hs := congrFun hfirst.1 i
    change o.lift.spelling x i = LiftDictionary.paddedLetters pad word (a+i.val) at hs
    rw [he] at hs
    simpa [LiftDictionary.paddedLetters,j.isLt] using hs

#print axioms dictionary_reads

end DeletionCode.Explicit.SelectedReplay

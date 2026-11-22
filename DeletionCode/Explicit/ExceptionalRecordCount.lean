import DeletionCode.Explicit.EditBallCount
import DeletionCode.Explicit.WeightedAddress
import DeletionCode.Explicit.ExceptionalWeight
import DeletionCode.CloseAnchorCount
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.List.Nodup

/-! Bounded chronological record enumeration and the counting constant
in `d:exception-constant`. -/
namespace DeletionCode.Explicit.ExceptionalWeight

open Burst
open scoped BigOperators

/-- Cartesian powers of a list, including its single empty tuple. -/
def tuples (xs : List α) : ℕ → List (List α)
  | 0 => [[]]
  | r+1 => xs.flatMap fun x => (tuples xs r).map (x :: ·)

@[simp] theorem mem_tuples {xs : List α} {r : ℕ} {ys : List α} :
    ys ∈ tuples xs r ↔ ys.length = r ∧ ∀ y ∈ ys, y ∈ xs := by
  induction r generalizing ys with
  | zero => cases ys <;> simp [tuples]
  | succ r ih =>
    cases ys <;> simp [tuples, List.mem_flatMap, List.mem_map, ih, and_comm, and_left_comm]

@[simp] theorem length_tuples (xs : List α) (r : ℕ) :
    (tuples xs r).length = xs.length^r := by
  induction r with
  | zero => simp [tuples]
  | succ r ih =>
    rw [tuples, List.length_flatMap]
    simp only [List.length_map, ih, List.map_const', List.sum_replicate, nsmul_eq_mul, pow_succ]
    exact Nat.mul_comm _ _

theorem tuples_nodup {xs : List α} (hx : xs.Nodup) (r : ℕ) :
    (tuples xs r).Nodup := by
  induction r with
  | zero => simp [tuples]
  | succ r ih =>
    rw [tuples, List.nodup_flatMap]
    refine ⟨fun a _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    apply hx.imp
    intro a b hn w ha hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, h⟩ := List.mem_map.mp hb
    exact hn (List.cons.inj h).1.symm

def inserts (q b : ℕ) : List (List (Fin q)) :=
  (List.range (b+1)).flatMap (wordsOfLength q)

@[simp] theorem mem_inserts {q b : ℕ} {w : List (Fin q)} :
    w ∈ inserts q b ↔ w.length ≤ b := by
  simp [inserts, List.mem_flatMap, List.mem_range, Nat.lt_succ_iff]

theorem inserts_nodup (q b : ℕ) : (inserts q b).Nodup := by
  rw [inserts, List.nodup_flatMap]
  refine ⟨fun a _ => WeightedAddress.words_nodup q a, ?_⟩
  apply List.nodup_range.imp
  intro a c h w ha hc
  exact h ((mem_wordsOfLength.mp ha).symm.trans (mem_wordsOfLength.mp hc))

private theorem length_inserts_le (q b : ℕ) (hq : 2 ≤ q) : (inserts q b).length ≤ 2*q^b := by
  have hs (k : ℕ) : ((List.range (k+1)).map (fun i => q^i)).sum + 1 ≤ 2*q^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      have hp : 2*q^k ≤ q^(k+1) := by
        rw [pow_succ, Nat.mul_comm 2]
        exact Nat.mul_le_mul_left _ hq
      omega
  rw [inserts, List.length_flatMap]
  simpa only [Function.comp_def, length_wordsOfLength] using
    (show ((List.range (b+1)).map (fun i => q^i)).sum ≤ 2*q^b by have := hs b; omega)

abbrev OpPayload (q : ℕ) := ℕ × List (Fin q)

def payloads (q b : ℕ) : List (OpPayload q) :=
  (List.range (b+1)).flatMap fun d => (inserts q b).map (d, ·)

@[simp] theorem mem_payloads {q b : ℕ} {d : OpPayload q} :
    d ∈ payloads q b ↔ d.1 ≤ b ∧ d.2.length ≤ b := by
  obtain ⟨r,v⟩ := d
  simp [payloads, List.mem_flatMap, List.mem_range, List.mem_map, Nat.lt_succ_iff]

theorem payloads_nodup (q b : ℕ) : (payloads q b).Nodup := by
  simp only [payloads, List.nodup_flatMap]
  refine ⟨fun a _ => (inserts_nodup q b).map (fun _ _ h => congrArg Prod.snd h), ?_⟩
  apply List.nodup_range.imp
  intro a c h x ha hc
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨w, _, he⟩ := List.mem_map.mp hc
  exact h (congrArg Prod.fst he).symm

theorem payloads_length (q b : ℕ) (hq : 2 ≤ q) : (payloads q b).length ≤ 2*(b+1)*q^b := by
  simp only [payloads, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
    List.length_range]
  exact (Nat.mul_le_mul_left _ (length_inserts_le q b hq)).trans_eq (by ring)

def op (j : ℕ) (p : OpPayload q) : Edit (Fin q) := ⟨j,p.1,p.2⟩

def choices (q b T : ℕ) : List (Edit (Fin q)) :=
  (List.range T).flatMap fun j => (payloads q b).map (op j)

@[simp] theorem mem_choices {q b T : ℕ} {e : Edit (Fin q)} :
    e ∈ choices q b T ↔ e.pos < T ∧ e.Bounded b := by
  obtain ⟨i,d,a⟩ := e
  simp [choices, op, List.mem_flatMap, List.mem_range, List.mem_map, Edit.Bounded, and_assoc]

theorem choices_nodup (q b T : ℕ) : (choices q b T).Nodup := by
  rw [choices, List.nodup_flatMap]
  refine ⟨fun a _ => (payloads_nodup q b).map (fun x y h => by
    cases x; cases y; simpa [op] using h), ?_⟩
  apply List.nodup_range.imp
  intro a c h e ha hc
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨w, _, he⟩ := List.mem_map.mp hc
  exact h (congrArg Edit.pos he).symm

theorem length_choices (q b T : ℕ) : (choices q b T).length = T * (payloads q b).length := by
  simp [choices, List.length_flatMap, List.map_const']

def separation (ℓ D : ℕ) (es : List (Edit (Fin q))) : Bool :=
  decide ((∀ i : Fin es.length, D ≤ (es[i]).pos ∧ (es[i]).pos+D ≤ ℓ) ∧
    ∀ i j : Fin es.length, i ≠ j → D ≤ Nat.dist (es[i]).pos (es[j]).pos)

theorem separation_eq_true {q ℓ D : ℕ} (es : List (Edit (Fin q))) :
    separation ℓ D es = true ↔ Separated ℓ D es := by
  simp [separation, Separated, PositionsSeparated]

def chronological (q b t L ℓ : ℕ) : List (List (Edit (Fin q))) :=
  let s := 2*t
  let choices := choices q b (ℓ+s*b+1)
  ((List.range s).flatMap fun r => tuples choices (r+1)).filter
    (fun es => es.length < s || !separation ℓ (8*(L+t*b)) es)

theorem chronological_nodup (q b t L ℓ : ℕ) : (chronological q b t L ℓ).Nodup := by
  unfold chronological
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => tuples_nodup (choices_nodup ..) (r+1), ?_⟩
  apply List.nodup_range.imp
  intro a c h e ha hc
  exact h (by have := (mem_tuples.mp ha).1; have := (mem_tuples.mp hc).1; omega)

theorem mem_chronological {q b t L ℓ : ℕ} {es : List (Edit (Fin q))} :
    es ∈ chronological q b t L ℓ ↔
      0 < es.length ∧ es.length ≤ 2*t ∧
      (es.length < 2*t ∨ ¬ Separated ℓ (8*(L+t*b)) es) ∧
      ∀ e ∈ es, e.pos < ℓ+2*t*b+1 ∧ e.Bounded b := by
  simp only [chronological, List.mem_filter, List.mem_flatMap, List.mem_range,
    mem_tuples, mem_choices, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.eq_false_iff]
  have hsep := not_congr (separation_eq_true (ℓ := ℓ) (D := 8*(L+t*b)) es)
  constructor
  · rintro ⟨⟨r, hr, hlen, hchoice⟩, h⟩
    exact ⟨by omega, by omega, (or_congr Iff.rfl hsep).mp h, hchoice⟩
  · rintro ⟨hpos, hlen, hbad, hchoice⟩
    exact ⟨⟨es.length-1, by omega, by omega, hchoice⟩, (or_congr Iff.rfl hsep).mpr hbad⟩

private def LeftBad {s T : ℕ} (D : ℕ) (i : Fin s) (a : Fin s → Fin T) : Prop :=
  (a i).val < D

private def RightBad {s T : ℕ} (ℓ D : ℕ) (i : Fin s) (a : Fin s → Fin T) : Prop :=
  ℓ < (a i).val+D

private def PairBad {s T : ℕ} (D : ℕ) (i j : Fin s) (a : Fin s → Fin T) : Prop :=
  (a j).val ≤ (a i).val ∧ (a i).val < (a j).val+D

attribute [local instance] Classical.propDecidable

private theorem card_left_values (T D : ℕ) :
    ((Finset.univ : Finset (Fin T)).filter (fun x => x.val < D)).card ≤ D := by
  have h := Finset.card_le_card_of_injOn
    (s := ((Finset.univ : Finset (Fin T)).filter (fun x => x.val < D)))
    (t := Finset.range D) Fin.val
    (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
    (fun _ _ _ _ h => Fin.ext h)
  simpa using h

private theorem card_right_values (ℓ d D : ℕ) :
    ((Finset.univ : Finset (Fin (ℓ+d+1))).filter (fun x => ℓ < x.val+D)).card ≤ D+d+1 := by
  let f (x : Fin (ℓ+d+1)) := x.val + D - (ℓ+1)
  have h := Finset.card_le_card_of_injOn
    (s := ((Finset.univ : Finset (Fin (ℓ+d+1))).filter (fun x => ℓ < x.val+D)))
    (t := Finset.range (D+d+1)) f
    (fun x _ => Finset.mem_range.mpr (by have := x.isLt; unfold f; omega))
    (fun x hx y hy he => by
      have hh := (Finset.mem_filter.mp hx).2
      have hh' := (Finset.mem_filter.mp hy).2
      apply Fin.ext
      unfold f at he
      omega)
  simpa using h

private theorem card_pair_values (T c D : ℕ) :
    ((Finset.univ : Finset (Fin T)).filter (fun x => c ≤ x.val ∧ x.val < c+D)).card ≤ D := by
  let f (x : Fin T) := x.val-c
  have h := Finset.card_le_card_of_injOn
    (s := ((Finset.univ : Finset (Fin T)).filter (fun x => c ≤ x.val ∧ x.val < c+D)))
    (t := Finset.range D) f
    (fun x hx => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hx).2; unfold f; omega))
    (fun x hx y hy he => by
      have hh := (Finset.mem_filter.mp hx).2
      have hh' := (Finset.mem_filter.mp hy).2
      apply Fin.ext
      unfold f at he
      omega)
  simpa using h

private theorem classical_filter_card {α : Type*} [Fintype α] {p : α → Prop}
    {dp : DecidablePred p} {m : ℕ} (h : (@Finset.filter α p dp Finset.univ).card ≤ m) :
    (@Finset.filter α p (fun a => Classical.propDecidable (p a)) Finset.univ).card ≤ m := by
  have he : dp = fun a => Classical.propDecidable (p a) := Subsingleton.elim _ _
  exact he ▸ h

private theorem bad_anchors_card (s ℓ d D : ℕ) :
    Nat.card {a : Fin s → Fin (ℓ+d+1) // ¬ PositionsSeparated ℓ D (fun i => (a i).val)} ≤
      (s*(s+1)*D+s*(d+1))*(ℓ+d+1)^(s-1) := by
  classical
  cases s with
  | zero => simp [PositionsSeparated]
  | succ r =>
    let s := r+1
    let T := ℓ+d+1
    let left (i : Fin s) := Finset.univ.filter (LeftBad (T := T) D i)
    let right (i : Fin s) := Finset.univ.filter (RightBad (T := T) ℓ D i)
    let pair (i j : Fin s) := Finset.univ.filter (PairBad (T := T) D i j)
    let badPair (i : Fin s) := (Finset.univ.erase i).biUnion (pair i)
    let bad := (Finset.univ : Finset (Fin s)).biUnion (fun i => left i ∪ right i ∪ badPair i)
    have hcap :
        (Finset.univ.filter (fun a : Fin s → Fin T => ¬ PositionsSeparated ℓ D (fun i => (a i).val))) ⊆ bad := by
      intro a h
      have hn := (Finset.mem_filter.mp h).2
      have hh : ¬ (∀ i : Fin s, D ≤ (a i).val ∧ (a i).val+D ≤ ℓ) ∨
          ¬ (∀ i j : Fin s, i ≠ j → D ≤ Nat.dist (a i).val (a j).val) := not_and_or.mp hn
      push Not at hh
      rcases hh with ⟨i, hend⟩ | ⟨i,j,hij,hnear⟩
      · by_cases hi : D ≤ (a i).val
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
            Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hend hi⟩))⟩
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, Nat.lt_of_not_ge hi⟩))⟩
      · have put (i j : Fin s) (hn : j ≠ i) (hij : PairBad D i j a) : a ∈ bad := by
          apply Finset.mem_biUnion.mpr
          refine ⟨i, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
        unfold Nat.dist at hnear
        rcases le_total (a i).val (a j).val with h₁ | h₂
        · exact put j i hij ⟨h₁, by omega⟩
        · exact put i j hij.symm ⟨h₂, by omega⟩
    have hl (i : Fin s) : (left i).card ≤ D*T^r :=
      CloseAnchorCount.coordinate_constraint_card_le i (fun _ x => x.val < D) D
        (fun _ => classical_filter_card (card_left_values T D))
    have hr (i : Fin s) : (right i).card ≤ (D+d+1)*T^r :=
      CloseAnchorCount.coordinate_constraint_card_le i (fun _ x => ℓ < x.val+D) (D+d+1)
        (fun _ => classical_filter_card (card_right_values ℓ d D))
    have hp (i j : Fin s) (hij : j ≠ i) : (pair i j).card ≤ D*T^r := by
      obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hij
      have h := CloseAnchorCount.coordinate_constraint_card_le i
        (fun y x => (y k).val ≤ x.val ∧ x.val < (y k).val+D) D
        (fun y => classical_filter_card (card_pair_values T (y k).val D))
      refine le_of_eq_of_le ?_ h
      apply congrArg Finset.card
      ext a
      simp only [pair, Finset.mem_filter, Finset.mem_univ, true_and]
      change ((a j).val ≤ (a i).val ∧ (a i).val < (a j).val+D) ↔
        ((a (i.succAbove k)).val ≤ (a i).val ∧ (a i).val < (a (i.succAbove k)).val+D)
      rw [hk]
    have hbp (i : Fin s) : (badPair i).card ≤ r*(D*T^r) := by
      have h := Finset.card_biUnion_le_card_mul (Finset.univ.erase i) (pair i) (D*T^r)
        (fun j hj => hp i j (Finset.mem_erase.mp hj).1)
      simpa [badPair, s, Finset.card_erase_of_mem (Finset.mem_univ i)] using h
    have hper (i : Fin s) : (left i ∪ right i ∪ badPair i).card ≤ ((s+1)*D+(d+1))*T^r := by
      calc
        _ ≤ (left i).card + (right i).card + (badPair i).card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
        _ ≤ D*T^r+(D+d+1)*T^r+r*(D*T^r) :=
          Nat.add_le_add (Nat.add_le_add (hl i) (hr i)) (hbp i)
        _ = _ := by dsimp [s]; ring
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact (Finset.card_le_card hcap).trans
      ((Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => hper i)).trans_eq (by
        simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]; dsimp [s,T]; ring))

private theorem long_records_card {q : ℕ} (rs : Finset (List (Edit (Fin q)))) (b ℓ s D : ℕ)
    (h : ∀ es ∈ rs, es.length = s ∧ ¬Separated ℓ D es ∧
      ∀ e ∈ es, e.pos < ℓ+s*b+1 ∧ e.Bounded b) :
    rs.card ≤ (s*(s+1)*D+s*(s*b+1))*(ℓ+s*b+1)^(s-1)*(payloads q b).length^s := by
  let T := ℓ+s*b+1
  let A := {a : Fin s → Fin T // ¬PositionsSeparated ℓ D (fun i => (a i).val)}
  let P := (payloads q b).toFinset
  let opAt (es : rs) (i : Fin s) : Edit (Fin q) := es.1[Fin.cast (h es.1 es.2).1.symm i]
  have spec (es : rs) (i : Fin s) := (h es.1 es.2).2.2 _ (List.getElem_mem
    (Fin.cast (h es.1 es.2).1.symm i).isLt)
  let anchor (es : rs) (i : Fin s) : Fin T := ⟨(opAt es i).pos, (spec es i).1⟩
  let f (es : rs) : A × (Fin s → P) :=
    ⟨⟨anchor es, by
      intro hsep
      apply (h es.1 es.2).2.1
      unfold Separated
      generalize_proofs at opAt
      have hl := (h es.1 es.2).1
      constructor
      · intro i
        exact hsep.1 (Fin.cast hl i)
      · intro i j hn
        exact hsep.2 (Fin.cast hl i) (Fin.cast hl j) (fun he => hn (Fin.ext (congrArg (fun x : Fin s => x.val) he)))⟩,
      fun i => ⟨((opAt es i).removed, (opAt es i).replacement),
        List.mem_toFinset.mpr (mem_payloads.mpr (spec es i).2)⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have hx := (h x.1 x.2).1
    have hy := (h y.1 y.2).1
    apply List.ext_getElem (hx.trans hy.symm)
    intro j hj hj'
    let i : Fin s := ⟨j, by omega⟩
    have hpos : (opAt x i).pos = (opAt y i).pos :=
      congrArg (fun z : A × (Fin s → P) => (z.1.val i).val) he
    have hpay : ((opAt x i).removed, (opAt x i).replacement) =
        ((opAt y i).removed, (opAt y i).replacement) :=
      congrArg (fun z : A × (Fin s → P) => (z.2 i).val) he
    change opAt x i = opAt y i
    cases hx : opAt x i <;> cases hy : opAt y i
    simp only [hx, hy, Edit.mk.injEq, Prod.mk.injEq] at hpos hpay ⊢
    exact ⟨hpos, hpay⟩
  let : Fintype A := Fintype.ofFinite _
  have hA : Fintype.card A ≤ (s*(s+1)*D+s*(s*b+1))*T^(s-1) := by
    rw [← Nat.card_eq_fintype_card]
    exact bad_anchors_card s ℓ (s*b) D
  have hP : P.card = (payloads q b).length := List.toFinset_card_of_nodup (payloads_nodup q b)
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, hP] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hA)

/-- Exact polynomial bound for the number of candidate records. A bad pair of
positions is counted in its increasing orientation, with at most `D` choices
for the larger position once the other positions are fixed. -/
theorem chronological_length_le {q b t L ℓ : ℕ} (hq : 2 ≤ q) (hL : 1 ≤ L)
    (hℓ : 2*t*b+1 ≤ ℓ) :
    (chronological q b t L ℓ).length ≤
      recordConstant b (2*t) t * q^(b*(2*t)) * L * ℓ^(2*t-1) := by
  classical
  let s := 2*t
  let T := ℓ+s*b+1
  let D := 8*(L+t*b)
  let ζ := (payloads q b).length
  let C := (chronological q b t L ℓ).toFinset
  let S := C.filter (fun es => es.length < s)
  let N := C.filter (fun es => ¬ es.length < s)
  let R j := (tuples (choices q b T) (j+1)).toFinset
  have hs : S.card ≤ (s-1)*T^(s-1)*ζ^s := by
    have hS : S ⊆ (Finset.range (s-1)).biUnion R := by
      intro es he
      obtain ⟨hC, hlen⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, _, _, he⟩ := mem_chronological.mp (List.mem_toFinset.mp hC)
      exact Finset.mem_biUnion.mpr ⟨es.length-1, Finset.mem_range.mpr (by omega),
        List.mem_toFinset.mpr (mem_tuples.mpr ⟨by omega, fun e he' => mem_choices.mpr (he e he')⟩)⟩
    refine (Finset.card_le_card hS).trans ?_
    rw [Nat.mul_assoc]
    have hf := Finset.card_biUnion_le_card_mul (Finset.range (s-1)) R (T^(s-1)*ζ^s)
    have hbound : ∀ j ∈ Finset.range (s-1), (R j).card ≤ T^(s-1)*ζ^s := by
      intro j hj
      have hn : 1 ≤ ζ := by
        have hm : ((0,[]) : OpPayload q) ∈ payloads q b := mem_payloads.mpr (by simp)
        have := List.length_pos_of_mem hm
        omega
      have hj' := Finset.mem_range.mp hj
      refine (List.toFinset_card_le _).trans ?_
      rw [length_tuples, length_choices, mul_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by unfold T; omega) (by omega))
        (Nat.pow_le_pow_right hn (by omega))
    simpa only [Finset.card_range] using hf hbound
  have hl : N.card ≤ (s*(s+1)*D+s*(s*b+1))*T^(s-1)*ζ^s := by
    apply long_records_card
    intro es he
    obtain ⟨hC, hlen⟩ := Finset.mem_filter.mp he
    obtain ⟨_, hh, hz, hspec⟩ := mem_chronological.mp (List.mem_toFinset.mp hC)
    exact ⟨by omega, hz.resolve_left hlen, hspec⟩
  have hsplit : C.card = S.card + N.card := (Finset.card_filter_add_card_filter_not _).symm
  have hb := (Nat.add_le_add hs hl)
  rw [← hsplit] at hb
  have hD : D ≤ 8*(1+t*b)*L := by
    have h := Nat.mul_le_mul_left (t*b) hL
    dsimp [D]; nlinarith only [h]
  let B := (s-1)+8*s*(s+1)*(1+t*b)+s*(s*b+1)
  have hcoeff : (s-1)+s*(s+1)*D+s*(s*b+1) ≤ B*L := by
    have hx := Nat.mul_le_mul_left (s*(s+1)) hD
    have hy := Nat.mul_le_mul_left ((s-1)+s*(s*b+1)) hL
    unfold B
    nlinarith only [hx, hy]
  have hT : T ≤ 2*ℓ := by
    change ℓ+(2*t)*b+1 ≤ 2*ℓ
    omega
  rw [← List.toFinset_card_of_nodup (chronological_nodup ..)]
  calc
    C.card ≤ ((s-1)+s*(s+1)*D+s*(s*b+1))*T^(s-1)*ζ^s := by
      convert hb using 1
      ring
    _ ≤ B*L*(2*ℓ)^(s-1)*(2*(b+1)*q^b)^s :=
      Nat.mul_le_mul (Nat.mul_le_mul hcoeff (Nat.pow_le_pow_left hT _))
        (Nat.pow_le_pow_left (payloads_length q b hq) _)
    _ = _ := by
      change _ = recordConstant b s t * q^(b*s) * L * ℓ^(s-1)
      simp only [recordConstant, B, mul_pow, ← pow_mul]
      ring

#print axioms chronological_length_le

#print axioms mem_chronological
#print axioms chronological_nodup

end DeletionCode.Explicit.ExceptionalWeight

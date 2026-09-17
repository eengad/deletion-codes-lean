import DeletionCode.UniqueRuns
import DeletionCode.SingleEditScripts

/-!
Maximal constant runs extracted from actual finite binary words. A valid index
determines a nonempty run containing that index; existing boundary letters
are opposite to the run bit. Deleting any selected position in a displayed
run gives the same shortened word. The length bound comes from k-uniqueness.
-/

namespace DeletionCode.MaximalRuns

open Windows CatalogueWords UniqueRuns

private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

/-- The first bit begins a nonempty run ending at the first opposite bit or
at the word's end. The run and its boundary are derived by list induction. -/
theorem exists_head_run (bit : Bool) (tail : List Bool) :
    ∃ (rho : ℕ) (suffix : List Bool), 0 < rho ∧
      bit :: tail = List.replicate rho bit ++ suffix ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  induction tail with
  | nil => exact ⟨1, [], by omega, rfl, Or.inl rfl⟩
  | cons b rest ih =>
    by_cases hb : b = bit
    · subst b
      obtain ⟨rho, suffix, hrho, heq, hright⟩ := ih
      refine ⟨rho + 1, suffix, by omega, ?_, hright⟩
      simpa only [List.replicate_succ, List.cons_append]
        using congrArg (List.cons bit) heq
    · refine ⟨1, b :: rest, by omega, rfl, Or.inr ?_⟩
      simpa only [List.head?_cons, Option.some.injEq] using bool_eq_not_of_ne hb

/-- A valid index lies in a concrete maximal run. Empty exterior words
represent runs reaching a boundary; otherwise the adjacent bit is opposite. -/
theorem exists_maximal_run (word : List Bool) (pos : ℕ) (hpos : pos < word.length) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  induction word generalizing pos with
  | nil => simp at hpos
  | cons head tail ih =>
    cases pos with
    | zero =>
      obtain ⟨rho, suffix, hrho, heq, hright⟩ := exists_head_run head tail
      exact ⟨[], suffix, rho, head, hrho, by simpa using heq,
        by simp, by simpa using hrho, Or.inl rfl, hright⟩
    | succ pos =>
      have htail : pos < tail.length := by
        simp only [List.length_cons] at hpos
        omega
      obtain ⟨pre, suffix, rho, bit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
        ih pos htail
      cases pre with
      | nil =>
        simp only [List.nil_append, List.length_nil, Nat.zero_add] at heq hstart hstop
        by_cases hhead : head = bit
        · subst head
          refine ⟨[], suffix, rho + 1, bit, by omega, ?_, by simp,
            by simpa using Nat.succ_lt_succ hstop, Or.inl rfl, hright⟩
          simpa only [List.nil_append, List.replicate_succ, List.cons_append]
            using congrArg (List.cons bit) heq
        · refine ⟨[head], suffix, rho, bit, hrho, ?_, by simp,
            by simp only [List.length_cons, List.length_nil]; omega, Or.inr ?_, hright⟩
          · simpa only [List.cons_append, List.nil_append]
              using congrArg (List.cons head) heq
          · change some head = some (!bit)
            exact congrArg some (bool_eq_not_of_ne hhead)
      | cons first rest =>
        refine ⟨head :: first :: rest, suffix, rho, bit, hrho, ?_, ?_, ?_, ?_, hright⟩
        · simpa only [List.cons_append] using congrArg (List.cons head) heq
        · simp only [List.length_cons] at hstart ⊢
          omega
        · simp only [List.length_cons] at hstop ⊢
          omega
        · rcases hleft with hnil | hlast
          · simp at hnil
          · exact Or.inr (by simpa only [List.getLast?_cons_cons] using hlast)

/-- Every index in a displayed constant block reads its actual bit. -/
theorem constantOn_block (pre suffix : List Bool) (rho : ℕ) (bit : Bool) :
    ConstantOn (listLetters (pre ++ List.replicate rho bit ++ suffix)) pre.length rho bit := by
  intro i hi
  simp only [List.append_assoc]
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  have hindex : pre.length + i - pre.length = i := by omega
  rw [hindex]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi)]
  rw [List.getElem?_replicate_of_lt hi]
  rfl

theorem bit_at_run_index (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    listLetters (pre ++ List.replicate rho bit ++ suffix) pos = bit := by
  have h := constantOn_block pre suffix rho bit (pos - pre.length) (by omega)
  have hindex : pre.length + (pos - pre.length) = pos := by omega
  simpa only [hindex] using h

/-- Deleting anywhere in a constant run yields the same shortened list.
Maximality is not needed for this local edit identity. -/
theorem eraseIdx_in_run (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx pos =
      pre ++ List.replicate (rho - 1) bit ++ suffix := by
  simp only [List.append_assoc]
  have hrun : pos - pre.length < rho := by omega
  rw [List.eraseIdx_append_of_length_le hstart]
  rw [List.eraseIdx_append_of_lt_length
    (by simpa only [List.length_replicate] using hrun)]
  rw [List.eraseIdx_replicate, ite_eq_left hrun]

theorem eraseIdx_same_in_run (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (p q : ℕ)
    (hp : pre.length ≤ p) (hp' : p < pre.length + rho)
    (hq : pre.length ≤ q) (hq' : q < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx p =
      (pre ++ List.replicate rho bit ++ suffix).eraseIdx q := by
  rw [eraseIdx_in_run pre suffix rho bit p hp hp', eraseIdx_in_run pre suffix rho bit q hq hq']

/-- The source uniqueness bound applies to every displayed run decomposition. -/
theorem run_length_le_of_unique (word : List Bool) (k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (pre suffix : List Bool) (rho : ℕ) (bit : Bool)
    (hword : word = pre ++ List.replicate rho bit ++ suffix) : rho ≤ k := by
  subst word
  apply constant_length_le k _ _ hx pre.length rho bit
  · simp only [List.length_append, List.length_replicate]
    omega
  · exact constantOn_block pre suffix rho bit

/-- Extracting a maximal source run also derives its length bound. -/
theorem exists_maximal_run_unique (word : List Bool) (pos k : ℕ)
    (hpos : pos < word.length) (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ rho ≤ k ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, bit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
    exists_maximal_run word pos hpos
  exact ⟨pre, suffix, rho, bit, hrho,
    run_length_le_of_unique word k hx pre suffix rho bit heq,
    heq, hstart, hstop, hleft, hright⟩

/-- Inserting a bit into an actual list split yields a maximal run containing
that inserted bit. Shortening the extracted run recovers the exact source. -/
theorem exists_insertion_run (left right : List Bool) (bit : Bool) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, runBit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
    exists_maximal_run (left ++ bit :: right) left.length
      (by simp only [List.length_append, List.length_cons]; omega)
  have hbit := bit_at_run_index pre suffix rho runBit left.length hstart hstop
  rw [← heq, SingleEditScripts.listLetters_at_split] at hbit
  subst runBit
  have hshort := eraseIdx_in_run pre suffix rho bit left.length hstart hstop
  rw [← heq, SingleEditScripts.eraseIdx_at_split] at hshort
  exact ⟨pre, suffix, rho, hrho, heq, hshort, hstart, hstop, hleft, hright⟩

/-- For a k-unique source, the longer run produced by insertion has length
between one and k+1. Its shorter run may be empty, as when rho=1. -/
theorem exists_insertion_run_unique (left right : List Bool) (bit : Bool) (k : ℕ)
    (hx : KUnique (listLetters (left ++ right)) (left ++ right).length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, hrho, heq, hshort, hstart, hstop, hleft, hright⟩ :=
    exists_insertion_run left right bit
  have hconstant : ConstantOn
      (insertAt (listLetters (left ++ right)) left.length bit) pre.length rho bit := by
    rw [SingleEditScripts.insert_split, heq]
    exact constantOn_block pre suffix rho bit
  have hbound : pre.length + rho ≤ (left ++ right).length + 1 := by
    have hlength := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_replicate] at hlength ⊢
    omega
  have hrhoBound := insert_constant_length_le k (left ++ right).length
    (listLetters (left ++ right)) hx left.length bit
    (by simp only [List.length_append]; omega) pre.length rho bit hbound hconstant
  exact ⟨pre, suffix, rho, hrho, hrhoBound, heq, hshort, hstart, hstop, hleft, hright⟩

/-- Valid insertion gaps, including either boundary, have the same concrete
maximal-run decomposition and length bound without a supplied list split. -/
theorem exists_insertion_run_at_gap_unique (word : List Bool) (pos : ℕ) (bit : Bool)
    (k : ℕ) (hpos : pos ≤ word.length)
    (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      word.take pos ++ bit :: word.drop pos = pre ++ List.replicate rho bit ++ suffix ∧
      word = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  have htake : (word.take pos).length = pos := by
    simp only [List.length_take, Nat.min_eq_left hpos]
  have hx' : KUnique (listLetters (word.take pos ++ word.drop pos))
      (word.take pos ++ word.drop pos).length k := by
    simpa only [List.take_append_drop] using hx
  simpa only [List.take_append_drop, htake] using
    exists_insertion_run_unique (word.take pos) (word.drop pos) bit k hx'

#print axioms exists_maximal_run
#print axioms eraseIdx_in_run
#print axioms exists_maximal_run_unique
#print axioms exists_insertion_run_unique
#print axioms exists_insertion_run_at_gap_unique

end DeletionCode.MaximalRuns

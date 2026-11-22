import DeletionCode.Explicit.Machine.SourceCoreCatalogue
import DeletionCode.Explicit.Machine.SourceExceptionalTable
import DeletionCode.Explicit.SourceSetup
import Batteries.Tactic.OpenPrivate

/-! Certify the concrete rare-word address and its padded inverse. -/
namespace DeletionCode.Explicit.Machine.SourceRareBranch

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Ternary CataloguePrefix
open _root_.DeletionCode.Explicit.UniformParameters
open private wordMasses from DeletionCode.Explicit.SourceSetup

variable {q l : ℕ}

abbrev HashInput := ℕ × Rows
abbrev hashInputEncoding := encPair encUnary rowsEncoding
abbrev massEncoding (q : ℕ) := Machine.RareAddress.massEncoding hashInputEncoding q

def prefixMass (pad : Fin q) (b t : ℕ) (p : ℕ × (Rows × QWord q)) : ℕ :=
  MatchingPrefixes.mass pad b t (p.1,p.2.2) + SourceExceptionalTable.evaluatePrefix pad b t p +
    SourceCoreCatalogue.evaluatePrefix pad b t p

theorem prefixMass_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (prefixMass pad b t) (SourceCoreCatalogue.prefixEncoding q) encNat := by
  let e := SourceCoreCatalogue.prefixEncoding q
  let w := wordEncoding q
  have hn := fst encUnary (encPair rowsEncoding w)
  have hw := (snd encUnary (encPair rowsEncoding w)).snd'
  have hm := (MatchingPrefixes.mass_polyTime pad hq hb ht).comp (encIn := e) (hn.prod hw)
  exact binary_add' (binary_add' hm (SourceExceptionalTable.prefix_polyTime pad b t hq))
    (SourceCoreCatalogue.prefix_polyTime pad b t hq)

private theorem prefixMass_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (H : ConcreteSource.Hash q b t l) (p : QWord q) :
    prefixMass pad b t (l,matrixRows H,p) = SourceSetup.prefixMass pad H p := by
  have hex := SourceExceptionalTable.prefix_eq pad H p.get
  have hcore := SourceCoreCatalogue.prefix_eq pad hq hb ht hl H p.get
  rw [List.ofFn_get] at hex hcore
  unfold prefixMass SourceSetup.prefixMass
  simp only [hex,hcore]

def mass (pad : Fin q) (b t : ℕ) (p : (HashInput × ℕ) × QWord q) : ℕ :=
  if p.1.2 = p.1.1.1 then prefixMass pad b t (p.1.2,p.1.1.2,p.2) else 0

private theorem mass_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (H : ConcreteSource.Hash q b t l) :
    (fun n p => mass pad b t (((l, matrixRows H), n), p)) = wordMasses pad H := by
  funext n p
  by_cases h : n = l
  · subst n
    simp only [mass, wordMasses, ↓reduceIte]
    exact prefixMass_eq pad b t hq hb ht hl H p
  · simp [mass, wordMasses, h]

theorem mass_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (mass pad b t) (massEncoding q) encNat := by
  let e := massEncoding q
  let w := wordEncoding q
  let a := encPair hashInputEncoding encUnary
  have hp := fst a w
  have hw := snd a w
  have h := (prefixMass_polyTime pad b t hq hb ht).comp (encIn := e)
    (hp.snd'.prod (hp.fst'.snd'.prod hw))
  exact ((hp.snd'.decide_eq' hp.fst'.fst').ite' h (const 0)).of_enc_eq (fun p => by
    simp [mass])

def encode (pad : Fin q) (b t : ℕ) (data : HashInput) (x : QWord q) : Option (QWord q) :=
  _root_.DeletionCode.Explicit.RareAddress.encodePayload pad (minLength q b t)
    (fun n p => mass pad b t ((data,n),p)) x

def decode (pad : Fin q) (b t : ℕ) (data : HashInput) (n : ℕ) (x : QWord q) : Option (QWord q) :=
  _root_.DeletionCode.Explicit.RareAddress.decodePayload (minLength q b t)
    (fun n p => mass pad b t ((data,n),p)) n x

theorem encode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (H : ConcreteSource.Hash q b t l) (x : QWord q) :
    encode pad b t (l, matrixRows H) x = (SourceSetup.rareBranch pad H).encode x := by
  unfold encode SourceSetup.rareBranch _root_.DeletionCode.Explicit.RareAddress.branch
  rw [mass_eq pad b t hq hb ht hl H]

theorem decode_eq (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (hl : minLength q b t ≤ l) (H : ConcreteSource.Hash q b t l) (n : ℕ) (x : QWord q) :
    decode pad b t (l, matrixRows H) n x = (SourceSetup.rareBranch pad H).decode n x := by
  unfold decode SourceSetup.rareBranch _root_.DeletionCode.Explicit.RareAddress.branch
  rw [mass_eq pad b t hq hb ht hl H]

theorem encode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun p : HashInput × QWord q => encode pad b t p.1 p.2)
      (encPair hashInputEncoding (wordEncoding q)) (encOption (wordEncoding q)) :=
  Machine.RareAddress.encodePayload_polyTime pad hq (minLength q b t) (mass_polyTime pad b t hq hb ht)

theorem decode_polyTime (pad : Fin q) (b t : ℕ) (hq : 2 ≤ q) (hb : 1 ≤ b) (ht : 2 ≤ t) :
    ComputableInPolyTime (fun p : (HashInput × ℕ) × QWord q => decode pad b t p.1.1 p.1.2 p.2)
      (massEncoding q) (encOption (wordEncoding q)) :=
  Machine.RareAddress.decodePayload_polyTime hq (minLength q b t) (mass_polyTime pad b t hq hb ht)

#print axioms encode_eq
#print axioms encode_polyTime
#print axioms decode_eq
#print axioms decode_polyTime

end DeletionCode.Explicit.Machine.SourceRareBranch

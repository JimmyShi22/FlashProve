-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReplyAtDriver.lean: THE FRAME FACT ON THE REPLY (`EachRep`,
Johnson/Desc/Sound/LeadsQ.lean: the end theorems' field `reply_leaves`) AT THE DRIVER'S OWN FIRST
CHAIN, AT THE TABLE'S OWN READER OF THE REPLY (`repHeard getS`, FinReply.lean). A JOINING: two rules
of other files (`eachOnce_firstChain`, Johnson/Desc/Sound/RepAtDriver.lean; `eachRep_of_once`,
RepOfOnce.lean), the driver's `flat_places` (Johnson/Desc/First/Driver/PlacesLaw.lean) and
evaluations of the table at the two closed lists.
  `heardV getS`: the reader at the record alone; `repHeard getS t` IS `heardV getS t.2`.
  `lays_small`, `lays_full`: ON THE TABLE, BY THE KERNEL: at every place of the written list "the
    row lays the token" is "the kind is K7".
  **`eachRep_at_driver`**: `EachRep tokOf links (flatPlacesOf links several) (fun a => (a.1, getS
    a.2)) f (fun b => repHeard getS b.1) on 0 l`, AT ANY PROMISE `on`: nothing is asked of the
    promise.
  `eachRep_of_desc`: the same at a description's first row: hl by `OfDesc`'s clause.
  `htok_nat`: a payer of htok: the token a number, tokOf := what the record heard (else 0), f :=
    that number as a token of the model (else 0).
LEFT, BY NAME: hc (the chain is the driver's) · hs (THE SEAT'S: what its guard `same` lets pass
leaves the reading) · hK (K7's FILES': the block at K7's place hears once: nothing heard in front,
something behind) · hl (the pieces hold these blocks: `OfDesc`'s clause b₁ with `held_map`) · hlays
(paid at the two closed lists) · htok (ON THE FILLINGS: the table's extractor's token is the reply
heard). Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RepAtDriver
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.Sound.AtDriver
import Johnson.P5J.FinReply

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Inst.Model
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart laysTok flatPlacesOf hearsReply)

/-- The reader of the reply that was heard, at the record alone. -/
def heardV {S₁ : Type} (getS : S₁ → First.S) (s : S₁) : Option (Fin ppref.V) :=
  (getS s).heardTok?.bind fun n => if h : n < ppref.V then some ⟨n, h⟩ else none

theorem repHeard_is {P S₁ : Type} (getS : S₁ → First.S) (t : P × S₁) :
    repHeard getS t = heardV getS t.2 := rfl

set_option maxRecDepth 1000000 in
theorem lays_small : ∀ p ∈ flatPlacesOf linksSmall true, laysTok linksSmall p = hearsReply p := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem lays_full : ∀ p ∈ flatPlacesOf linksFull true, laysTok linksFull p = hearsReply p := by
  decide +kernel

/-- **THE FRAME FACT ON THE REPLY AT THE DRIVER's OWN FIRST CHAIN.** -/
theorem eachRep_at_driver {P S₁ Cells Tok Cl : Type} {Fr : Frame} {C : CK} (getS : S₁ → First.S)
    (tokOf : P × First.S → Tok) (f : Tok → Fin ppref.V) (links : List ModelPart) (several : Bool)
    (on : ℕ → (P × S₁) × Fr.E.Str → Prop) {H : First.Blocks S₁ Cl} {c : Chain S₁ Cl}
    (hc : First.firstChain H links several = some c)
    (hs : ∀ t s, H.same t s = true → heardV getS s = heardV getS t)
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce (heardV getS))
    (l : List (Piece C Fr (P × S₁) Cl (Wit Cells Tok MsgT)))
    (hl : l.map (·.b) = c.blocksInOrder.map (held (P := P)))
    (hlays : ∀ p ∈ flatPlacesOf links several, laysTok links p = hearsReply p)
    (htok : ∀ (t : P × S₁) x, repHeard getS t = some x → f (tokOf (t.1, getS t.2)) = x) :
    EachRep tokOf links (flatPlacesOf links several) (fun a : P × S₁ => (a.1, getS a.2)) f
      (fun b => repHeard getS b.1) on 0 l := by
  have hp := First.flat_places H links several c hc
  refine eachRep_of_once tokOf links (flatPlacesOf links several) (fun a : P × S₁ => (a.1, getS
    a.2)) f (fun t : P × S₁ => heardV getS t.2) on htok l 0
    (eachOnce_firstChain links (flatPlacesOf links several) (heardV getS) hc hs hK l 0 hl ?_ ?_)
  · intro i b hb
    rw [Nat.zero_add, ← hp, List.getElem?_map, hb]
    rfl
  · intro b hb
    exact hlays b.place (by rw [← hp]; exact List.mem_map_of_mem hb)

/-- **THE SAME AT A DESCRIPTION's FIRST ROW**: hl is `OfDesc`'s own clause. hc: the
description's first chain is the driver's. -/
theorem eachRep_of_desc {Xi Cells Tok X₁ X₂ : Type} {C : CK} {D : WholeD} {all : List LeftT}
    (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ (Wit Cells Tok MsgT)) (hO : OfDesc F T)
    (getS : F.S₁ → First.S) (tokOf : F.XiPub × First.S → Tok) (f : Tok → Fin ppref.V)
    (links : List ModelPart) (several : Bool)
    (on : ℕ → (F.XiPub × F.S₁) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    {H : First.Blocks F.S₁ F.Cl} (hc : First.firstChain H links several = some F.first)
    (hs : ∀ t s, H.same t s = true → heardV getS s = heardV getS t)
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce (heardV getS))
    (hlays : ∀ p ∈ flatPlacesOf links several, laysTok links p = hearsReply p)
    (htok : ∀ (t : F.XiPub × F.S₁) x, repHeard getS t = some x → f (tokOf (t.1, getS t.2)) = x) :
    EachRep tokOf links (flatPlacesOf links several) (fun a : F.XiPub × F.S₁ => (a.1, getS a.2)) f
      (fun b => repHeard getS b.1) on 0 (T.p₁ :: T.l₁) :=
  eachRep_at_driver getS tokOf f links several on hc hs hK (T.p₁ :: T.l₁)
    (hO.b₁.trans (held_map _).symm) hlays htok

/-- **A payer of htok.** -/
theorem htok_nat {P S₁ : Type} (getS : S₁ → First.S) (t : P × S₁) (x : Fin ppref.V)
    (h : repHeard getS t = some x) :
    (fun n : ℕ => if h : n < ppref.V then (⟨n, h⟩ : Fin ppref.V) else ⟨0, OnBytes.Flat.ppref_V_pos⟩)
      ((fun a : P × First.S => a.2.heardTok?.getD 0) (t.1, getS t.2)) = x := by
  have h' : ((getS t.2).heardTok?.bind fun n =>
      if h : n < ppref.V then some (⟨n, h⟩ : Fin ppref.V) else none) = some x := h
  obtain ⟨n, hn, hx⟩ := Option.bind_eq_some_iff.1 h'
  show (if h : (getS t.2).heardTok?.getD 0 < ppref.V then
    (⟨(getS t.2).heardTok?.getD 0, h⟩ : Fin ppref.V) else ⟨0, OnBytes.Flat.ppref_V_pos⟩) = x
  rw [hn]
  show (if h : n < ppref.V then (⟨n, h⟩ : Fin ppref.V) else ⟨0, OnBytes.Flat.ppref_V_pos⟩) = x
  by_cases hv : n < ppref.V
  · rw [dif_pos hv] at hx ⊢
    exact Option.some.inj hx
  · rw [dif_neg hv] at hx
    cases hx

end P5J

#print axioms P5J.lays_small
#print axioms P5J.lays_full
#print axioms P5J.eachRep_at_driver
#print axioms P5J.eachRep_of_desc
#print axioms P5J.htok_nat

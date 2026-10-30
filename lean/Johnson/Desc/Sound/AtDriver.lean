-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/AtDriver.lean: THE OBJECT OF A BLOCK'S TIES TO THE TABLE OF JOINTS: A BLOCK OF
THE DRIVER'S OWN FIRST CHAIN, AND THE PIECE THAT A DESCRIPTION'S ROW HOLDS THERE. One structure, two
lists, two theorems, four evaluations. (In a file apart from
Johnson/Desc/Sound/Border62.lean, so that other kinds' files can stand on it.)

What is said.
  `AtDriver H links k a b B q`: B is block number k of the flat list of `firstChain H links true`
    (Johnson/Desc/First/Driver/Chain.lean); a is entry number k of the driver's own
    `flatPlacesOf links true`; b is the seat's block at a (`H.block a`); the piece q holds `below
    B`, lifted over the public part, as a description's pieces do.
  `AtDriver.narrows`: B narrows b, at a place of a kind other than K9 and "frame": by the driver's
    own law on the places (`flat_places`, Johnson/Desc/First/Driver/PlacesLaw.lean) and
    `flat_seated` (Johnson/Desc/Sound/FlatSeated.lean).
  `OfDesc.pieceAt`: entry number k of a description's first row of pieces holds entry number k of
    its first flat list, under the strict reading, lifted.
  `linksSmall`, `linksFull`; `place61_small` ... `place342_full` (by evaluation).

Limits. The seat H is a letter. That a description's first chain is `firstChain`'s value is not said
here. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FlatSeated
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart)

/-- **THE OBJECT: block number k of the driver's own first chain at a seat's blocks, and the piece
that a description's row holds there.** -/
structure AtDriver {Cl P W : Type} {C : CK} {Fr : Frame} (H : First.Blocks First.S Cl)
    (links : List ModelPart) (k : ℕ) (a : Place) (b B : Block First.S Cl)
    (q : Piece C Fr (P × First.S) Cl W) : Prop where
  /-- B is block number k of the chain's flat list -/
  chain : ∃ c, First.firstChain H links true = some c ∧ c.blocksInOrder[k]? = some B
  /-- a is entry number k of the driver's list of places -/
  place : (First.flatPlacesOf links true)[k]? = some a
  /-- b is what the seat lays at a -/
  seat : H.block a = some b
  /-- the piece holds B under the strict reading, lifted over the public part -/
  piece : q.b = (below B).lift Prod.snd fun t s => (t.1, s)

/-- **At the driver's chain the flat list's entry narrows what the seat lays at its place**: by the
driver's own law on the places (`flat_places`) and `flat_seated`. -/
theorem AtDriver.narrows {Cl P W : Type} {C : CK} {Fr : Frame} {H : First.Blocks First.S Cl}
    {links : List ModelPart} {k : ℕ} {a : Place} {b B : Block First.S Cl}
    {q : Piece C Fr (P × First.S) Cl W} (h : AtDriver H links k a b B q) (hf : a.kind ≠ .frame)
    (h9 : a.kind ≠ .K9) : B.Narrows b := by
  obtain ⟨c, hc, hk⟩ := h.chain
  have hpl : B.place = a := by
    have e := First.flat_places H links true c hc
    have e2 : (c.blocksInOrder.map (·.place))[k]? = some B.place := by
      rw [List.getElem?_map, hk]
      rfl
    rw [e, h.place] at e2
    exact (Option.some.inj e2).symm
  obtain ⟨b₀, e₀, n⟩ := First.flat_seated hc B (List.mem_of_getElem? hk) (by rw [hpl]; exact hf)
    (by rw [hpl]; exact h9)
  rw [hpl, h.seat] at e₀
  cases e₀
  exact n

/-- **The piece as a description's row holds it**: entry number k of the first row's pieces holds
entry number k of the description's first flat list, under the strict reading, lifted. -/
theorem OfDesc.pieceAt {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    {F : FileDescription Xi} {T : ThreeAt C D all F X₁ X₂ W} (h : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W} {B : Block F.S₁ F.Cl}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) (hB : F.first.blocksInOrder[k]? = some B) :
    q.b = (below B).lift Prod.snd fun t s => (t.1, s) := by
  have e := congrArg (·[k]?) h.b₁
  simp only [List.getElem?_map, hq, hB, Option.map_some] at e
  exact Option.some.inj e

/-- The segments' sorts of the small stored proof. -/
def linksSmall : List ModelPart := [.layers, .attention, .layers, .attention, .head]

/-- The segments' sorts at the full size. -/
def linksFull : List ModelPart :=
  (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

set_option maxRecDepth 100000 in
theorem place61_small : (First.flatPlacesOf linksSmall true)[61]? =
    some { chain := 1, link := some 4, piece := 4, kind := .K6 } := by decide

set_option maxRecDepth 100000 in
theorem place62_small : (First.flatPlacesOf linksSmall true)[62]? =
    some { chain := 1, link := some 4, piece := 5, kind := .K1 } := by decide

set_option maxRecDepth 100000 in
theorem place341_full : (First.flatPlacesOf linksFull true)[341]? =
    some { chain := 1, link := some 24, piece := 4, kind := .K6 } := by decide

set_option maxRecDepth 100000 in
theorem place342_full : (First.flatPlacesOf linksFull true)[342]? =
    some { chain := 1, link := some 24, piece := 5, kind := .K1 } := by decide

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.AtDriver.narrows
#print axioms VerifiableInference.Desc.Sound.OfDesc.pieceAt
#print axioms VerifiableInference.Desc.Sound.place61_small
#print axioms VerifiableInference.Desc.Sound.place342_full

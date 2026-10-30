-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RepAtDriver.lean: `EachOnce` (Johnson/Desc/Sound/RepOfOnce.lean) AT THE DRIVER's
OWN FIRST CHAIN: at a row of pieces that hold the blocks of `firstChain H lk several`'s flat list,
by the guard's laws at the driver's text (`firstChain_flat_leaves`, `firstChain_flat_hears`,
Johnson/Desc/Sound/GuardAtDriver.lean).

Why. The frame fact on the reply wants: the block at the row that lays the token hears once; every
other block leaves the reading. The driver's first chain stands behind a guard, whose laws give both
of EVERY block of its flat list, whatever the kinds' texts are, from one fact on the seat's test
`same` and one on what the seat hands at K7's places. A piece of a description holds `held b`
(Johnson/Desc/Sound/PaidAtDesc.lean): the block under the test on the words, lifted over the public
part. Here the laws are carried through `held` and called.
  `Block.HearsOnce.below`, `Block.HearsOnce.held`, `Block.Leaves.held`: through the piece's form of
  a block.
  `Block.HearsOnce.bind`: to a reading MADE OF the reading: where the block hears once at r, and
  what it holds behind meets ok (`Block.Hears r ok`, RepOfLeaves.lean), and g is defined wherever ok
  holds: it hears once at `fun s => (r s).bind g`. (The table's reader of the reply gives a value
  only at a token's number below the vocabulary's size: so "something is held" is not enough for
  it.)
  `eachOnce_of_flat`: a row of pieces that hold `bs.map held`, the list's places being bs's: from
  the two laws on bs.
  `eachOnce_firstChain`: bs := the flat list of the driver's first chain.
Limits. RULES, GENERAL IN THE SEAT H: nothing is shown of any seat. OWED: hs (the seat's test `same`
holds the reading fixed) · hK (what the seat hands at a place of the kind K7 hears once AT THE
READING r). THE ROAD TO hK, all of it in Johnson/Desc/Sound/HearsOnce.lean and SeatGuardLaws.lean,
none of it called here: K7's own kind hears once at the raw reply (`Kinds.Reply.kind_hearsOnce`); a
block that only refuses more hears once too (`hearsOnce_of_under`); and where a seat JOINS another
block behind K7's (by reading, the seat of today does: K7's place is the first of the head's link,
behind which a frame's block is joined), `hearsOnce_andThen` wants that the joined block leaves r,
which a block under the guard at no place told apart does (`guarded_or`, with hs). At a reading made
of the raw reply: `Block.HearsOnce.bind` · hlays (at each place of the flat list the table's "lays
the token" is "the kind is K7": a fact on the table: its row at K7's place lays; links, the table's,
and lk, the driver's, are two letters here, and hlays is what ties them) · that the row's pieces
hold these blocks and that the list of places is theirs. That a description's first chain IS such a
chain, AT A SEAT THAT IS NAMED (hs and hK speak of H: "there is a seat" does not serve), is not said
here. No soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RepOfOnce
import Johnson.Desc.Sound.GuardAtDriver
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

theorem Block.HearsOnce.below {S Cl β : Type} {r : S → Option β} {b : Block S Cl}
    (hl : b.HearsOnce r) : (Sound.below b).HearsOnce r := by
  intro s rs gs s' e
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  split at e'
  · exact hl s rs gs s' e'
  · cases e'

/-- Through the piece's form of a block. -/
theorem Block.HearsOnce.held {P S Cl β : Type} {r : S → Option β} {b : Block S Cl}
    (hl : b.HearsOnce r) : (Sound.held (P := P) b).HearsOnce fun t => r t.2 := by
  intro t rs gs t' e
  have e' : ((Sound.below b).decide t.2 rs gs).map (fun s => ((t.1, s) : P × S)) = .ok t' := e
  cases hd : (Sound.below b).decide t.2 rs gs with
  | error m => rw [hd] at e'; cases e'
  | ok s' =>
    rw [hd] at e'
    have et : ((t.1, s') : P × S) = t' := Except.ok.inj e'
    subst et
    exact hl.below _ _ _ _ hd

theorem Block.Leaves.held {P S Cl α : Type} {h : S → α} {b : Block S Cl} (hl : b.Leaves h) :
    (Sound.held (P := P) b).Leaves fun t => h t.2 := by
  intro t rs gs t' e
  have e' : ((Sound.below b).decide t.2 rs gs).map (fun s => ((t.1, s) : P × S)) = .ok t' := e
  cases hd : (Sound.below b).decide t.2 rs gs with
  | error m => rw [hd] at e'; cases e'
  | ok s' =>
    rw [hd] at e'
    have et : ((t.1, s') : P × S) = t' := Except.ok.inj e'
    subst et
    exact hl.below _ _ _ _ hd

/-- **To a reading made of the reading.** -/
theorem Block.HearsOnce.bind {S Cl β γ : Type} {r : S → Option β} {ok : β → Prop} {b : Block S Cl}
    (h1 : b.HearsOnce r) (h2 : b.Hears r ok) (g : β → Option γ)
    (hg : ∀ x, ok x → (g x).isSome = true) : b.HearsOnce fun s => (r s).bind g := by
  intro s rs gs s' e
  obtain ⟨h0, -⟩ := h1 s rs gs s' e
  obtain ⟨x, hx, hok⟩ := h2 s rs gs s' e
  refine ⟨?_, ?_⟩
  · show (r s).bind g = none
    rw [h0]; rfl
  · show ((r s').bind g).isSome = true
    rw [hx]; exact hg x hok

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart laysTok)

section
variable {P S₁ Cells Tok Tok' Cl : Type} {Fr : Frame} {C : CK} (links : List ModelPart) (ps : List Place)
  (r : S₁ → Option Tok')

/-- **A row of pieces that hold a list of blocks, from the two laws on the list.** -/
theorem eachOnce_of_flat (but : Place → Bool) (bs : List (Block S₁ Cl))
    (l : List (Piece C Fr (P × S₁) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (hl : l.map (·.b) = bs.map (held (P := P)))
    (hps : ∀ i b, bs[i]? = some b → ps[k + i]? = some b.place)
    (hlays : ∀ b ∈ bs, laysTok links b.place = but b.place)
    (hor : ∀ b ∈ bs, but b.place = true ∨ b.Leaves r)
    (hh : ∀ b ∈ bs, but b.place = true → b.HearsOnce r) :
    EachOnce (Cells := Cells) (Tok := Tok) links ps (fun t : P × S₁ => r t.2) k l := by
  refine eachOnce_of_rows links ps _ but l k fun i q hq => ?_
  have e : (l.map (·.b))[i]? = some q.b := by rw [List.getElem?_map, hq]; rfl
  rw [hl, List.getElem?_map] at e
  obtain ⟨b, hb, hbq⟩ := Option.map_eq_some_iff.1 e
  have hm : b ∈ bs := List.mem_of_getElem? hb
  rw [← hbq]
  exact ⟨hps i b hb, hlays b hm, (hor b hm).imp id fun h => h.held, fun h => (hh b hm h).held⟩

/-- **At the driver's own first chain.** -/
theorem eachOnce_firstChain {H : First.Blocks S₁ Cl} {lk : List ModelPart} {several : Bool}
    {c : Chain S₁ Cl} (hc : First.firstChain H lk several = some c)
    (hs : ∀ t s, H.same t s = true → r s = r t)
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce r)
    (l : List (Piece C Fr (P × S₁) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (hl : l.map (·.b) = c.blocksInOrder.map (held (P := P)))
    (hps : ∀ i b, c.blocksInOrder[i]? = some b → ps[k + i]? = some b.place)
    (hlays : ∀ b ∈ c.blocksInOrder, laysTok links b.place = First.hearsReply b.place) :
    EachOnce (Cells := Cells) (Tok := Tok) links ps (fun t : P × S₁ => r t.2) k l :=
  eachOnce_of_flat links ps r First.hearsReply c.blocksInOrder l k hl hps hlays
    (fun b hb => (First.firstChain_flat_leaves hs hc b hb).imp
      (fun e => by unfold First.hearsReply; rw [e]; exact beq_self_eq_true _) id)
    (First.firstChain_flat_hears hK hc)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Block.HearsOnce.held
#print axioms VerifiableInference.Desc.Block.Leaves.held
#print axioms VerifiableInference.Desc.Block.HearsOnce.bind
#print axioms VerifiableInference.Desc.Sound.eachOnce_of_flat
#print axioms VerifiableInference.Desc.Sound.eachOnce_firstChain

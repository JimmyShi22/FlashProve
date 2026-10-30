-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Seated.lean.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on (some files of
this folder call it "the record"). WORDS BELOW: "block": a sub-protocol ·
"a yes": that it accepts · "a description": the IOP as written in Lean.
ITS FORM: (1) IN THE SECOND FORM OF THE CHAIN OF PROMISES (Desc/Sound/TiedR.lean): a
letter Rch stands beside the table's promise at the border in front (meant: "this state is reached
from the first by the sub-protocols in front"): THE FIELDS pub, pubP, shown, frames, order, held MAY
SPEND IT; dec may not ("decodes" must ride without it). k7_tied_seat ends in TiedAtR, by
Desc/Sound/TiedLaysR.lean: tiedAtR_of_seatE. (2) THE BILL IS CUT IN THREE: dec, order, held,
shown, pub, pubP AND frames STAND APART AS K7State: whoever has them as theorems at a meaning is
asked K7Rest's SIX alone. (3) piece_yes and piece_ext: k7_yes from the field "yes" alone, and the
bill's field "ext" from two facts on the table, for whoever pays K7State before the whole bill is in
hand.
WHAT IT DOES NOT SHOW. No soundness. A RULE OVER LETTERS: NO MEMBER: no piece of any description is
shown to meet its premises. THE SMALLER BILL K7Left IS PAID BY NOBODY HERE: its fields, and whose:
  constr, decIs   the meaning's two fields that the proofs open: constr is
                  constrQAt at this filling of headPart (at the composed meaning mgAll: MgAll.lean's
                  mgAll_constr, by definition); decodes says that the reading's decoder answers
                  (at that meaning: NOT HELD).
  yes     a yes of the block B that the piece holds is a yes of the seated constant (the entry of
            the head's link, then the next token's block) FROM THE SAME STATE TO THE SAME STATE: at
            a description: the law in the seats' files at the place "H:1" (the head's frame's
            "opened", joined behind, hands the verifier's state on as it is).
  front   a yes of the constant's first half is a yes of the entry's own function.
  place, next, head   the table's list of places has the next token's place at k and the head's
                      second piece behind it; the segment is a head's.
  noRows  NO CLASS OF ROWS IS OPEN AT THE BORDER k: so the fresh group that the entry of the head's
            link lays can be no open segment's (Law/K7Rides.lean's premise hFresh holds emptily).
  book, told          as in Law/K7Rides.lean.
  req     the reading of the request reads the verifier's state through its request's words alone.
  dec     the decoded table is the same at the two statements.
  tok     the token that the reading of the witness finds in a witness whose token is tokOf b is
            tokH b.
  order, pub, pubP, held, shown   the promise's other clauses ride ACROSS A YES OF THE PIECE
                                  (Law/K7Rides.lean: hIn … hSN).
  frames  what rides past the block rides (Law/K7Tied.lean's head says what is held of it).
LETTERS. No "there is" in the tops. z: the public part: under "for all". Bst: what the seat lays:
read by SeatOf alone.
OBJECT. The piece over the verifier's state that holds "below B" and bears the table's own extractor
read at that state (Desc/Sound/TiedLays.lean: atPub), and the description's piece q that holds B
beneath the lift over the public part.
USER. The next token's kind's share of the chain of promises, second form (Desc/Sound/TiedR.lean:
KindTiedR).
WHAT IT IS. OF THE ELEVEN FIELDS OF THE BILL K7Due (Law/K7Tied.lean) SIX ARE PAID HERE AT THAT
PIECE: ext (the table's extractor at the place turns the token alone: Law/K7Calls.lean: ext_k7) ·
ins, outs, ctx (the table's row at the place, by evaluation of its text) · mark (the entry says yes
at no marked state) · req (the request's words stay); "rides" IS CUT TO ITS SIX OPEN CLAUSES
(Law/K7Rides.lean); "decodes" follows from "dec". SO THE TIE AT THE DESCRIPTION's OWN PIECE FOLLOWS
FROM K7Left.
  K7Table, K7Rest   the smaller bill's two parts: six facts on the meaning and the table (constr,
                    decIs, place, next, head, noRows), which read no block and no piece; and the
                    rest.
  K7State           dec, order, held, shown, pub, pubP and frames.
  K7Left            the smaller bill: the three together.
  k7_yes            a yes of that piece is the seated constant's yes between the two states.
  k7_due            K7Left gives K7Due at that piece, for every z.
  k7_tied_seat      the tie at q.withMap (the table's extractor), by tiedAtR_of_seatE.
THE MEANING IS A LETTER, with the two
fields constr and decIs. THE BILL IS CUT IN TWO PARTS, so that whoever has the five facts on
the meaning and the table as theorems is asked the other part alone.

THE FIELD "noRows" IS a fact on
the table alone: the promise pins the numbers of trees and of messages, not of groups; and at the
full chain's table no class of rows is open at this border.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K7Tied
import Johnson.Desc.Kinds.Law.K7Rides
import Johnson.Desc.Sound.TiedLaysR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (HTailF2)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Place Block FileDescription Oracle KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart Item Meaning start rowSegs openSets pubSets
  pubRowM pubStep stepOpen rowOf pubHeld sampledIn bookFit)
open VerifiableInference.Desc.First.K2 (headFrontQ)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open OnBytes.Maker (uLT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)
  {Cl P Xi : Type} {C : CK} {Fr : Frame} (hd : Nat) (tab : Nat → Nat)
  (put : P5J.TReq → Fin ppref.V → P5J.TReq)
  (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
  (tokH : P × S → Fin ppref.V) (tokOf : P × S → Tok)
  (digitsPart : Nat → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart) (ps : List Place)
  (k : Nat) (G : FileDescription Xi)
  (smp : P × S → (x : Sending) → (i : Fin x.l.length) →
    Option ((Johnson.Pack.sigOf cs x.l).om i).Smp)
  (ms : List Mem)
  (decT : (Nat → Option (Nat × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (c₀ : Fin rows → Fin cols → GE) (B : Block S Cl)
  (q : Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
  (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
  (tl : HTailF2) (k2 : KindName) (told : List (List Oracle))
  (Rch : Nat → (P × S) × Fr.E.Str → Prop)

/-- The piece over the verifier's state at which the kind's tie is asked. -/
abbrev pieceK7 (z : P) : Piece C Fr S Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT) :=
  (⟨Sound.below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece C Fr S Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT)).withMap
    (atPub (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) k) z)

local notation "PC7" => pieceK7 cs arr N tokOf links ps k G smp ms decT c₀ B q

/-- **THE BILL's PART ON THE MEANING AND THE TABLE**: six facts that read no block and no piece. -/
structure K7Table : Prop where
  constr : Mg.constr =
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart
  decIs : ∀ a y, Mg.decodes a y ↔ (H.dec a y).isSome = true
  place : ps[k]? = some ⟨1, some hd, 1, .K7⟩
  next : ps[k + 1]? = some ⟨1, some hd, 2, k2⟩
  head : links[hd]? = some .head
  noRows : rowSegs (openQ links ps k) = []

/-- **THE BILL's OTHER PART.** Every field that speaks of two states speaks of A YES OF THE
PIECE. -/
structure K7Rest : Prop where
  yes : ∀ x rs gs t, B.decide x rs gs = .ok t →
    ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide x rs' gs' = .ok t
  front : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1
  book : bookFit N ps told = true
  told : told[k]? = some []
  req : ∀ (z : P) (x t : S), t.req = x.req → H.req (z, t) = H.req (z, x)
  tok : ∀ (b : P × S) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT),
    (H.hid ⟨w.cells, tokOf b, w.msg, w.pad⟩).tok = tokH b

/-- **THE BILL's THIRD PART**: seven fields that say of a sentence of the meaning that it is handed
on where the piece accepts, and that can be had from WHAT THE PLACE LEAVES OF THE VERIFIER's STATE
once the meaning's terms are known. -/
structure K7State : Prop where
  dec : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b →
    H.dec (z, b.1) (strsOf Fr b.2) = H.dec (z, a.1) (strsOf Fr a.2)
  order : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b → Rch k ((z, a.1), a.2) →
    Mg.inOrder (z, a.1) = true → Mg.inOrder (z, b.1) = true
  held : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b → Rch k ((z, a.1), a.2) →
    ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.held x.1 x.2 (z, a.1) = true → Mg.held x.1 x.2 (z, b.1) = true
  shown : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b → Rch k ((z, a.1), a.2) →
    ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (z, a.1) (strsOf Fr a.2) →
      Mg.shown x.1 x.2 (strsOf Fr b.2) ∧ Mg.noColl x.1 x.2 (z, b.1) (strsOf Fr b.2)
  pub : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b → Rch k ((z, a.1), a.2) →
    pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (z, a.1) = true →
    pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD [])
        (rowOf links ⟨1, some hd, 1, .K7⟩))
      (pubStep ((pubSets Mg.more links ps)[k]?.getD [])
        (pubRowM Mg.more links ⟨1, some hd, 1, .K7⟩)) (z, b.1) = true
  pubP : ∀ (z : P) a τ b, (PC7 z).ior.red.out a τ = some b → Rch k ((z, a.1), a.2) →
    (∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP x (z, a.1)) →
    ∀ x ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD [])
        (pubRowM Mg.more links ⟨1, some hd, 1, .K7⟩), Mg.pubP x (z, b.1)
  frames : ∀ z : P, (PC7 z).Frames
    (onR N Mg links ps (fun x => (z, x)) (fun k a => Rch k ((z, a.1), a.2)) k)
    (onQ N Mg links ps (fun x => (z, x)) (k + 1)) (meansQ N Mg fun x => (z, x))
    (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k)

/-- **THE SMALLER BILL**: the three parts. -/
structure K7Left : Prop extends
  K7Table cs arr msR N s seat Wp pl hd tab put H tokH digitsPart Mg links ps k k2,
  K7Rest N Wp H tokH tokOf ps k B W l name front tl told,
  K7State cs arr N Wp hd H tokOf Mg links ps k G smp ms decT c₀ B q Rch

local notation "LEFT7" => K7Left cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg
  links ps k G smp ms decT c₀ B q W l name front tl k2 told Rch

variable {cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps k G smp ms decT
  c₀ B q W l name front tl k2 told Rch}

namespace Came

/-- **Where that piece accepts, the seated constant accepts between the two states**: from the
bill's field "yes" alone. -/
theorem piece_yes
    (hyes : ∀ x rs gs t, B.decide x rs gs = .ok t →
      ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide x rs' gs' = .ok t)
    (z : P) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C (PC7 z).ds))
    (b : S × Fr.E.Str) (hb : (PC7 z).ior.red.out a τ = some b) :
    ∃ rs gs, (front.andThen name (Reply.blockOf W l)).decide a.1 rs gs = .ok b.1 := by
  obtain ⟨rs, gs, hd'⟩ := out_yes (PC7 z) a b τ hb
  exact hyes _ _ _ _ ((below_narrows B).2 _ _ _ _ hd')

/-- **What that piece's extractor does**: it lays the token of the state behind into the witness,
and nothing else: from two facts on the table. -/
theorem piece_ext (hplace : ps[k]? = some ⟨1, some hd, 1, .K7⟩) (hhead : links[hd]? = some .head)
    (z : P) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C (PC7 z).ds)) (b : S × Fr.E.Str)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hb : (PC7 z).ior.red.out a τ = some b) :
    (PC7 z).ext a τ w = ⟨w.cells, tokOf (z, b.1), w.msg, w.pad⟩ := by
  have hseg : rowOf links ⟨1, some hd, 1, .K7⟩ = First.segRow .head hd 1 := by
    unfold First.rowOf
    simp only [hhead]
  refine (withMap_ext (⟨Sound.below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece C Fr S Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (atPub (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) k) z) a τ b w
    hb).trans ?_
  show extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) k ((z, a.1), a.2)
    ((z, b.1), b.2) w = _
  unfold extQAt
  rw [hplace]
  exact ext_k7 cs G arr smp ms decT c₀ tokOf N links _ rfl (by rw [hseg]; rfl) _ _ _ w

/-- The same from the whole bill. -/
theorem k7_yes (L : LEFT7) (z : P) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C (PC7 z).ds))
    (b : S × Fr.E.Str) (hb : (PC7 z).ior.red.out a τ = some b) :
    ∃ rs gs, (front.andThen name (Reply.blockOf W l)).decide a.1 rs gs = .ok b.1 :=
  piece_yes L.yes z a τ b hb

/-- **THE BILL OF Law/K7Tied.lean, AT THAT PIECE.** -/
theorem k7_due (L : LEFT7) (z : P) :
    K7Due cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps
      (fun x => (z, x)) (fun k a => Rch k ((z, a.1), a.2)) k (PC7 z) := by
  have hrow : rowQ links ps k = rowOf links ⟨1, some hd, 1, .K7⟩ := by
    unfold rowQ
    rw [L.place]
    rfl
  have hseg : rowOf links ⟨1, some hd, 1, .K7⟩ = First.segRow .head hd 1 := by
    unfold First.rowOf
    simp only [L.head]
  have hmark : ∀ a τ b, (PC7 z).ior.red.out a τ = some b → a.1.failed = none := by
    intro a τ b hb
    obtain ⟨rs, gs, hy⟩ := k7_yes L z a τ b hb
    exact (place_facts W l name front tl L.front _ _ _ _ hy).1
  refine ⟨L.constr, ?_, ?_, ?_, ?_, ?_, ?_, L.dec z, L.tok, L.frames z, ?_, ?_⟩
  · intro a τ b ha hr hb
    obtain ⟨rs, gs, hy⟩ := k7_yes L z a τ b hb
    obtain ⟨f0, f1, f2, f3⟩ := place_facts W l name front tl L.front _ _ _ _ hy
    exact k7_rides N Mg links ps (fun x => (z, x)) k hd .K7 k2 L.head L.place L.next a b ha _ _ f0
      f1 f2 f3 (fun y hy => by rw [L.noRows] at hy; cases hy) told L.book L.told
      (fun h => (L.decIs _ _).2 (by
        rw [L.dec z a τ b hb]
        exact (L.decIs _ _).1 h))
      (fun _ _ => L.order z a τ b hb hr) (fun _ _ => L.pub z a τ b hb hr)
      (fun _ _ => L.pubP z a τ b hb hr) (fun _ _ => L.held z a τ b hb hr)
      (fun _ _ => L.shown z a τ b hb hr)
  · intro a τ b w hb
    exact piece_ext L.place L.head z a τ b w hb
  · rw [hrow, hseg]
    rfl
  · rw [hrow, hseg]
    rfl
  · rw [hrow, hseg]
    rfl
  · intro a τ b hb
    obtain ⟨rs, gs, hy⟩ := k7_yes L z a τ b hb
    exact L.req z _ _ (place_whole W l name front tl L.front _ _ _ _ hy).2.2.2.2.2.2
  · intro a τ b hb h
    exact absurd (hmark a τ b hb) h
  · intro a τ b hb h
    refine (L.decIs _ _).2 ?_
    rw [L.dec z a τ b hb]
    exact (L.decIs _ _).1 h

/-- **THE TIE AT THE DESCRIPTION's OWN PIECE.** -/
theorem k7_tied_seat (L : LEFT7) (Bst : Block S Cl) (hS : SeatOf Bst B)
    (hq : q.b = (Sound.below B).lift Prod.snd fun t x => (t.1, x)) :
    TiedAtR N Mg links ps (fun a => a) Rch k
      (q.withMap (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) k)) :=
  tiedAtR_of_seatE links ps k Bst B q hS hq N Mg Rch _ _ _ _ _ fun _ z => k7_tiedBy (k7_due L z)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

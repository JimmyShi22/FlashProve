-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Border62.lean: THE CHAIN OF PROMISES AT ONE INNER BORDER OF THE DRIVER'S OWN
FIRST CHAIN: BETWEEN THE OUTPUT HEAD'S BLOCK (K6; piece 4 of the head's segment) AND THE SENDING
BEHIND IT (K1; piece 5): `TiedAt` (Johnson/Desc/Sound/ChainOfPromises.lean) AT BOTH BLOCKS, WITH
EACH KIND'S OWN WORDS WRITTEN OUT. STATEMENTS. PROVED HERE: THE PLACES' NUMBERS, AND THE STEP FROM
THE OBJECT TO WHAT THE CARRIAGE OF K6'S LAW ASKS OF THE SEAT, AND A RULE: WHAT IS LEFT OF K6'S SIDE.

A LATER CHANGE: `tied61_of_object` takes `PubBehind` in its second form (K6Second.lean); `Tied62`'s
docstring says what the letter `sealed` makes of it. No statement turns. THE CLOSED INSTANCES AT THE
TWO REAL LISTS: Johnson/Desc/Sound/Border62At.lean.
`AtDriver`, `AtDriver.narrows`, `OfDesc.pieceAt`, the two lists and the four
evaluations stand in Johnson/Desc/Sound/AtDriver.lean.


What is said.
  (`TiedBy k q o o' R R'`, Johnson/Desc/Sound/TiedBy.lean: `TiedAt k q` with the kind's four words
    named, in the place of "there are".)
  `AtDriver H links k a b B q`: THE OBJECT: B is block number k of the flat list of
    `firstChain H links true` (Johnson/Desc/First/Driver/Chain.lean); a is entry number k of the
    driver's own `flatPlacesOf links true`; b is the seat's block at a (`H.block a`); the piece q
    holds `below B`, lifted over the public part, as a description's pieces do.
  `linksSmall`, `linksFull`; `place61_small` ... `place342_full` (by evaluation): at the two real
    lists of segments the two blocks have the numbers 61 | 62 and 341 | 342.
  `AtDriver.narrows`: at the driver's chain the flat list's entry narrows the seat's block at its
    place. `seated_of_object`: so `Object61` gives `Seated` (K6Tied.lean), all five fields.
  `Object61`, `Tied61`: K6's block: the seat's block is the seated constant `seatedClaims Wp m bef`
    under the seat's guard on the mark and a name; the kind's words are those of the head's files:
    K6On, K6After, and its three items (closed, opened, pins).
  `tied61_of_object`: what is left of `Tied61` at the object, by name (its docstring).
  `Object62`, `Tied62`: the sending: the kind's law has letters for its conditions and relations
    (`send_goodIn_entry`, Johnson/Desc/K1/Law/GoodSend4.lean): they are laid AT THE TABLE'S OWN
    TERMS; the one clause that is the kind's own, "each sampled message that is sent is sealed", IS
    A LETTER HERE (`sealed`): its text stands in a file that does not compile over this base.
  `Border62`: both.

WHAT HAS NO TERM, SO THAT THE INSTANCE IS A FUNCTION OF IT: the section's variables: read the list
at `Tied61`.

Limits. Statements: that they can be met is not said. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6Second
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.First (Pub pubFit sampledIn pubOfItems)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ relQ insQ outsQ
  extQAt openAfter strsOf openQ pubQ TiedBy AtDriver Fenced ErrBears kitK kitFs BlindOrder)

section
/- THE LETTERS. WITH A TERM ELSEWHERE, NOT JOINED: cs G arr smp decT msT (the oracles' reading:
the fillings of the end theorems) · N (a root beside the tiles) · Wp bef (the public record; the
lot's list) · H (the pure seat's blocks) · rd6 ms (the head's files' newer laws fill them by
the table's readers). WITHOUT A TERM: Mg's FIELDS pub · inOrder · worth · row · pile, AND constr AT
THE HEAD (a letter of the map to the model) · c₀ tokOf (any). GIVEN BY THE OBJECT: k a B q. -/
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms msT : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (tokOf : P × S → Tok) (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
  (H : First.Blocks S Claim) (links : List ModelPart) (k m : ℕ)

/-- **K6's block at the driver's chain.** n: the seat's name for it. -/
def Object61 (bef : List (ℕ × ℕ)) (n : String) (bS B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  seatedClaims Wp m bef = some bS ∧
    AtDriver H links k { chain := 1, link := some m, piece := 4, kind := .K6 }
      { markGuard bS with name := n } B q ∧ q.back = []

/-- **FROM THE OBJECT TO WHAT THE CARRIAGE OF THE LAW ASKS OF THE SEAT**: all five fields of
`Seated` (Johnson/Desc/Sound/K6Tied.lean), with no premise more. -/
theorem seated_of_object (bef : List (ℕ × ℕ)) (n : String) (bS B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (h : Object61 Wp fld Fr H links k m bef n bS B q) : Seated Wp fld Fr q m bef B bS := by
  obtain ⟨h1, h2, h3⟩ := h
  have hn : B.Narrows { markGuard bS with name := n } :=
    h2.narrows (fun e => by cases e) (fun e => by cases e)
  exact ⟨h1, hn.trans ((Block.Same.narrows (⟨rfl, rfl⟩ : ({ markGuard bS with name := n } :
      Block S Claim).Same (markGuard bS))).trans (markGuard_narrows bS)),
    fun s rs gs t e => markGuard_unmarked bS s rs gs t (hn.2 s rs gs t e), h2.piece, h3⟩

/-- **K6's BLOCK IS TIED, IN ITS KIND's OWN WORDS.** -/
def Tied61 (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  TiedBy N Mg links (First.flatPlacesOf links true) (fun a => a) k
    (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links (First.flatPlacesOf links true)
      (fun a => a) k))
    (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
    (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s))
      ms rd6 Wp Fr i (a.1.2, a.2) w) InK6)
    (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s))
      ms rd6 Wp Fr i (a.1.2, a.2) w) OutK6)

set_option quotPrecheck false in
/-- The driver's list of places. -/
local notation "PS" => First.flatPlacesOf links true

/-- **WHAT IS LEFT OF `Tied61` AT THE OBJECT, BY NAME.** ON THE TABLE (tests at the list of segments
and at the door's filling): hfit hs hp' · ON THE PLAN AND ITS NUMBERS: hplan hF hlog hNum · ON THE
FILLINGS: hBl hloc hPub hOr · THE BITS: hErr · WHAT RIDES: hDec hSh hNc · THE PUBLIC ITEMS BEHIND,
AS Bools AND AS SENTENCES: hPB hPP · THE TIES: t3 t4 t5. PAID OUTRIGHT, FROM THE OBJECT: all that
the carriage asks of the seat; "a mark stays"; of the second tie the stand, the groups, the book's
places. ONLY CARRIED, UNDER THE PREMISES NAMED: the law (hBl hloc hF hlog hErr) · the first tie
(hfit hs hplan hPub) · of the second: "in order" and the samples held (hOr: A PREMISE ON THE
FILLING: these two letters do not read the open segment's own part), the book's numbers (hNum). -/
theorem tied61_of_object (bef : List (ℕ × ℕ)) (n : String) (bS B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (hO : Object61 Wp fld Fr H links k m bef n bS B q)
    (hfit : pubFit Mg.more links PS = true)
    (hs : links[m]? = some .head)
    (hp' : PS[k + 1]? = some { chain := 1, link := some m, piece := 5, kind := .K1 })
    (hNum : N.treesAt PS[k + 1]? = N.treesAt PS[k]? ∧ N.msgsAt PS[k + 1]? = N.msgsAt PS[k]?)
    (hplan : planB Wp = true) (hF : Fenced q.base ms)
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64) (hBl : Blind cs smp decT)
    (hloc : ReadsPinned cs ms rd6) (hPub : PubSays Wp Mg m) (hOr : BlindOrder Mg)
    (hPB : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ x ∈ pubQ Mg.more links PS (k + 1) ++ pubOfItems (openQ links PS (k + 1)),
        Mg.pub x b.1 = true)
    (hPP : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ x ∈ pubQ Mg.more links PS (k + 1), Mg.pubP x b.1)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2))
    (hSh : ∀ a τ b, q.ior.red.out a τ = some b → ∀ x ∈ sampledIn N (openQ links PS k),
      Mg.shown x.1 x.2 (strsOf Fr a.2) → Mg.shown x.1 x.2 (strsOf Fr b.2))
    (hNc : ∀ a τ b, q.ior.red.out a τ = some b → ∀ x ∈ sampledIn N (openQ links PS k),
      Mg.noColl x.1 x.2 a.1 (strsOf Fr a.2) → Mg.noColl x.1 x.2 b.1 (strsOf Fr b.2))
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links PS k) b w →
      relAt (meansK6 cs G arr (fun s => smp (b.1.1, s)) (fun c s => decT c (b.1.1, s)) ms rd6 Wp
        Fr) OutK6 (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links PS k) b w →
      relAt (meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms rd6 Wp
        Fr) InK6 (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links PS k) a w)
    (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b →
      relQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b w →
      openAfter (insQ links PS) (outsQ links PS) (· ∈ First.start links) k i → ¬ insQ links PS k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w) :
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg links k q := by
  have Hs := seated_of_object Wp fld Fr H links k m bef n bS B q hO
  unfold Tied61
  exact k6_tiedBy cs G arr smp decT c₀ ms rd6 Wp fld Fr q m bef B bS msT tokOf N Mg links PS k _ m
    hfit hO.2.1.place rfl rfl hs rfl Hs hplan hF hlog hBl hloc hPub hErr
    (fun a τ b ha hm hb hA => k6_t2_quiet Hs N Mg links PS k _ _ m hO.2.1.place hp' rfl rfl hs rfl
      rfl hOr hDec hSh hNc hPB hPP hNum a τ b ha hm hb hA)
    t3 t4 t5 hDec

/-- **The sending behind it, at the driver's chain.** b1: what the seat lays at piece 5. -/
def Object62 (b1 B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  AtDriver H links (k + 1) { chain := 1, link := some m, piece := 5, kind := .K1 } b1 B q

/-- **THE SENDING IS TIED.** The kind's law takes any conditions and relations: they are laid at the
table's own terms at the block's two borders; `sealed`: the kind's own clause behind its yes: A
LETTER: SO THIS IS A FAMILY OF STATEMENTS: at a `sealed` that never holds the law says that the
block always refuses; at one that always holds the second tie must find "no collision" at the new
tenants in nothing. MEANT: "each sampled message that is sent is sealed" (`Sealed`,
Johnson/Desc/K1/Law/GoodSend3.lean), when that file compiles over this base. -/
def Tied62 (sealed : (P × S) × Fr.E.Str → Prop)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  TiedBy N Mg links (First.flatPlacesOf links true) (fun a => a) (k + 1)
    (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links (First.flatPlacesOf links true)
      (fun a => a) (k + 1)))
    (fun a => onQ (Fr := Fr) N Mg links (First.flatPlacesOf links true) (fun a => a) (k + 1) a ∧
      a.1.2.failed = none)
    (fun b => b.1.2.failed = none ∧ sealed b)
    (relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links (First.flatPlacesOf links true) (k + 1)))
    (relAt (meansQ (Fr := Fr) N Mg fun a => a)
      (outsQ links (First.flatPlacesOf links true) (k + 1)))

/-- **THE BORDER**: both blocks at the driver's chain, each tied. -/
def Border62 (bef : List (ℕ × ℕ)) (n : String) (bS B₆ b1 B₁ : Block S Claim)
    (sealed : (P × S) × Fr.E.Str → Prop)
    (q₆ q₁ : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  Object61 Wp fld Fr H links k m bef n bS B₆ q₆ → Object62 fld Fr H links k m b1 B₁ q₁ →
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg links k q₆ ∧
      Tied62 cs G arr smp decT c₀ msT fld Fr tokOf N Mg links k sealed q₁

end

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#check @VerifiableInference.Desc.Kinds.Head.Law.AtTable.Border62
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seated_of_object
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tied61_of_object

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadRestR.lean: the kind "lookup" (K3), the lookup argument on the calls
at the output head's link: `HeadAtTableR` (Johnson/Desc/First/Look/K3HeadAtTableR.lean) CUT IN TWO:
the 23 fields that have a payer at the composed meaning
(`HeadGotR`) and the 3 that have none (`HeadLeftR`): so that what is owed there is a Lean
structure, not a list in a text outside the library.

Main names:
  `HeadGotR`: ins, outs, ctx, askIn, seats, pubIn, qIn, tokIn, freeIn, worthP, worthK, worthR,
    cf, pinIn, pinBack, tabIn, pinWIn, pinWOut, ownIn, free, pinWBack, behind, decodes.
  `HeadLeftR`: objects, model, smallBack.
  `headAtTableR_of`: the two give `HeadAtTableR`. `headAtTableR_iff`: and it gives the two.

PAYERS: tokIn, freeIn, ownIn (the facts on every reached state) and behind (the `BehindPartsR`,
Johnson/Desc/First/Look/K3CallsBehindR.lean) have payers. `BehindParts`' first form can be met
by nothing at the small door.



THE FIELDS' TEXTS ARE `HeadAtTableR`'s OWN, LAID HERE BY A PROGRAM (one local notation of that file
is written out in worthR; some docstrings' words are levelled to the table of terms); Lean holds
each against its original in both theorems.

Limits: definitions and two re-packings. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3HeadAtTableR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

/-- **The fields that have a payer at the composed meaning.** -/
structure HeadGotR {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
    (adr : HeadAdr)
    (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (set : Params.Setting)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (Rc : Desc.First.S × Fr.E.Str → Prop)
    (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop) : Prop where
  ins : (rowQ links ps k).ins = [.constr m .lookCallsHeard, .constr m .rider]
  outs : (rowQ links ps k).outs =
    [.formsT m 3 "objects", .worth m 3 "planes", .worth m 3 "keys", .worth m 3 "rider"]
  ctx : (rowQ links ps k).ctx = [.pin m 0, .constr m .small, .pinW]
  askIn : Pub.lookIn m 3 ∈ (pubSets Mg.more links ps)[k]?.getD []
  seats : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])
  pubIn : ∀ s, Mg.pub (.lookIn m 3) (pi, s) = true →
    k3LookIn (Desc.First.Look.P.ofPlace set false x) (D.arrayOf.getD x.link #[]) s = true
  /-- what is known of the ledger in front -/
  qIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → ∀ F, (Desc.K3.seatCalls claim).fork a.1 = some F → Q F
  /-- a reply has been heard -/
  tokIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → a.1.replyTok?.isSome = true
  /-- the ledger is free above its next slot -/
  freeIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → FreeAt (Desc.K3.seatCalls claim).fork a.1
  worthP : ∀ s y w, Mg.worth m 3 "planes" (pi, s) y w → gd w →
    K3WorthPlanes (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm
      x.F.next (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) s w
  /-- the keys, AT THE REPLY THAT THE VERIFIER's STATE HAS HEARD (written out: `K3WorthKeys` takes
  keys that read the witness alone) -/
  worthK : ∀ (s : Desc.First.S) y w, Mg.worth m 3 "keys" (pi, s) y w → gd w → ∀ g F',
    (Desc.K3.seatCalls claim).fork s = some F' → (Desc.K3.seatCalls claim).heard s = some g →
    K3OutKeys x.fs x.lm x.F.next (headNu adr x tl D rad oW wOf nr nc seatT arr msgW w)
      (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns tl nr nc) (s.replyTok?.getD 0)
        (zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w))) Reading.gl g F'
  /-- the rider, at that reply -/
  worthR : ∀ (s : Desc.First.S) y w, Mg.worth m 3 "rider" (pi, s) y w → gd w → ∀ g F',
    (Desc.K3.seatCalls claim).fork s = some F' → (Desc.K3.seatCalls claim).heard s = some g →
    K3OutRider (headRider adr x tl D rad oW wOf nr nc extNone Unit) x.lm x.F.next
      (s.replyTok?.getD 0) (layMs x D rad oW seatT arr msgW w) g F'
  cf : ∀ i s y, Mg.held (seatT i).1 (seatT i).2 (pi, s) = true →
    Mg.shown (seatT i).1 (seatT i).2 y → Mg.noColl (seatT i).1 (seatT i).2 (pi, s) y →
    CfAt G D.codes (sigListCalls D rad x.link) seatT smp i s y
  pinIn : ∀ s y w, (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, s) y w) →
    PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) s y w
  pinBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    (∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, b.1) (strsOf Fr b.2) w) →
    ∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (pi, a.1) (strsOf Fr a.2) w
  tabIn : ∀ a : Desc.First.S × Fr.E.Str, Mg.decodes (pi, a.1) (strsOf Fr a.2) →
    ∃ σW, smpW a.1 = some σW ∧ ¬ oW.Clash (strW a.2) σW.1
  pinWIn : ∀ (a : Desc.First.S × Fr.E.Str) w, Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    ∃ σW, smpW a.1 = some σW ∧ oW.dec (strW a.2) σW = some (msgW w)
  pinWOut : ∀ (a : Desc.First.S × Fr.E.Str) w,
    (∃ σW, smpW a.1 = some σW ∧ oW.dec (strW a.2) σW = some (msgW w)) →
    Mg.pinW (pi, a.1) (strsOf Fr a.2) w
  /-- the state's own numbers are the plan's at this link: the codes, the open link's number and
  list of arrays, the live copy's shape and layout: ONE SENTENCE, a fact along the fold -/
  ownIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → OwnIs D x.link a.1
  /-- where the guard fails, the two items in front hold of themselves (they bear a guard of their
  own, which the committed table's pin turns into this one) -/
  free : ∀ (a : Desc.First.S × Fr.E.Str) w, ¬ gd w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    Mg.constr m .lookCallsHeard (pi, a.1) (strsOf Fr a.2) w ∧
      Mg.constr m .rider (pi, a.1) (strsOf Fr a.2) w
  /-- the committed table's pin goes back past the accepting -/
  pinWBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.pinW (pi, b.1) (strsOf Fr b.2) w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w
  behind : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    Mg.decodes (pi, b.1) (strsOf Fr b.2) →
    K3LeftAt (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next Q
      b.1 →
    FreeAt (Desc.K3.seatCalls claim).fork b.1 → onQ N Mg links ps (fun s => (pi, s)) (k + 1) b
  decodes : ∀ a b : Desc.First.S × Fr.E.Str, Yes a b → SameBut a.1 b.1 →
    Mg.decodes (pi, a.1) (strsOf Fr a.2) → Mg.decodes (pi, b.1) (strsOf Fr b.2)


/-- **The fields that have none yet.** -/
structure HeadLeftR {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
    (adr : HeadAdr)
    (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (set : Params.Setting)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (Rc : Desc.First.S × Fr.E.Str → Prop)
    (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop) : Prop where
  /-- asked behind an accepting of the piece at a statement inside the promise and without a mark,
  with what that accepting leaves, the lookup's test behind and the promise behind in hand (the
  lookups' authors' form of the field) -/
  objects : ∀ (a b : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
    Mg.formsT m 3 "objects" (pi, b.1) (strsOf Fr b.2) w →
    K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) b.1 w
  /-- the head's sentence at the heard reply gives the two items in front: asked where the promise
  in front holds and no mark stands (so a reply is heard, and it is a token), with the committed
  table's pin in hand (the row's ctx has it) -/
  model : ∀ (a : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none →
    HeadSays adr x tl D rad oW wOf nr nc (a.1.replyTok?.getD 0)
      (layMs x D rad oW seatT arr msgW w) →
    Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w → Mg.pinW (pi, a.1) (strsOf Fr a.2) w →
    Mg.constr m .lookCallsHeard (pi, a.1) (strsOf Fr a.2) w ∧
      Mg.constr m .rider (pi, a.1) (strsOf Fr a.2) w
  smallBack : ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.constr m .small (pi, b.1) (strsOf Fr b.2) w → Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w

/-- **The two give the whole.** -/
theorem headAtTableR_of {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
    (adr : HeadAdr)
    (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (set : Params.Setting)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (Rc : Desc.First.S × Fr.E.Str → Prop)
    (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
    (A : HeadGotR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes)
    (B : HeadLeftR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes) :
    HeadAtTableR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes where
  ins := A.ins
  outs := A.outs
  ctx := A.ctx
  askIn := A.askIn
  seats := A.seats
  pubIn := A.pubIn
  qIn := A.qIn
  tokIn := A.tokIn
  freeIn := A.freeIn
  objects := B.objects
  worthP := A.worthP
  worthK := A.worthK
  worthR := A.worthR
  cf := A.cf
  pinIn := A.pinIn
  pinBack := A.pinBack
  tabIn := A.tabIn
  pinWIn := A.pinWIn
  pinWOut := A.pinWOut
  ownIn := A.ownIn
  model := B.model
  free := A.free
  pinWBack := A.pinWBack
  smallBack := B.smallBack
  behind := A.behind
  decodes := A.decodes

/-- And the whole gives the two. -/
theorem headAtTableR_iff {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
    (adr : HeadAdr)
    (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (set : Params.Setting)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (Rc : Desc.First.S × Fr.E.Str → Prop)
    (claim : Aff → Cl) (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop) :
    HeadAtTableR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes ↔
      HeadGotR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes ∧
      HeadLeftR (Fr := Fr) G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q
      gd Rc claim N Mg links ps pi k m Yes :=
  ⟨fun T => ⟨⟨T.ins, T.outs, T.ctx, T.askIn, T.seats, T.pubIn, T.qIn, T.tokIn, T.freeIn, T.worthP,
      T.worthK, T.worthR, T.cf, T.pinIn, T.pinBack, T.tabIn, T.pinWIn, T.pinWOut, T.ownIn,
      T.free, T.pinWBack, T.behind, T.decodes⟩,
    ⟨T.objects, T.model, T.smallBack⟩⟩,
    fun h => headAtTableR_of G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q gd Rc
      claim N Mg links ps pi k m Yes h.1 h.2⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headAtTableR_of
#print axioms VerifiableInference.OnPublicFiles.headAtTableR_iff

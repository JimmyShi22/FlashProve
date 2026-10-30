-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
calls_objects_att_facts, calls_objects_lay_facts: no list of rounds, no
meaning and no state are shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsObjectsAt.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS:
THE FIELD "objects" OF AttAtTableR AND LayAtTableR WITH ITS PREMISE ON THE VERIFIER's STATE PAID:
calls_objects_att | calls_objects_lay (K3CallsObjects.lean) at maskOkCalls_of_facts
(K3CallsMaskOkAt.lean), own := N.sent m 0. Two theorems: joinings. No error term. NO SOUNDNESS IS
CLAIMED.

Why. So that Lean, and no reader's eye, holds the one theorem's conclusion against the other's
premise.

OBJECT, LETTERS: the two files'.
USER: Johnson/Desc/Sound/MgAt/K3CallsObjFacts.lean.

Compiled with the whole library.


WHAT IS LEFT. formsT_objects_bare's six · hMg · hB · hBare · and maskOkCalls_of_facts' own: four
facts along the fold at Rc · two public tests open at the border behind, with the meaning's lemmas
at them · the tests on the list of rounds and on the list of members.

Limits. At Cl := Desc.Claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsObjects
import Johnson.Desc.First.Look.K3CallsMaskOkAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Wit Link Strs)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First (ModelPart Pub Meaning Numbers pubSets moreItem)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB sentName)
open VerifiableInference.Desc.First.Att.P (maskMsg)

section
variable {P Cells Tok : Type} {Fr : Frame} (x : Desc.First.Look.Place) (D : Sent)
  (rad : OracleShape → ℕ) (set : Params.Setting)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (claim : Aff → Desc.Claim) (N : Numbers) (Mg Mg₀ : Meaning P (Wit Cells Tok MsgT))
  (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
  (Rc : Desc.First.S × Fr.E.Str → Prop)
  (ms : List Mem) (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → Desc.First.S → Except String Desc.First.S)
  (wt : ℕ → P × Desc.First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → Desc.First.S → Bool)
  (ah : ℕ → String → Bool) (pr : ℕ) (H : LinkHoles) (l : Link Desc.First.S Desc.Claim)
  (pass : Desc.First.S → Desc.First.S → Prop)
  (hB : maskCallsB D (sigListCalls D rad x.link) x.link x.ns = true)
include hB

/-- **THE FIELD objects OF AttAtTableR, ITS PREMISE ON THE STATE PAID.** -/
theorem calls_objects_att_facts (A : Attention.Shape) (tl : HTailF2)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 2 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 2 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 2 "objects" (pi, s) y
        w)
    (hBare : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b →
      ∀ g, (Desc.K3.seatCalls claim).heard b.1 = some g → ∀ f ∈ g.rows.toList, Bare f)
    {dS : SentData} {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (seatN : ℕ → ℕ × ℕ)
    (hT : ∀ i, seatT i = seatN i.val)
    (hLive : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.shape = D.shape)
    (hGroups : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hSeats : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstShapes M a.1 = true)
    (askSent : moreItem (sentName m) ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubSent : ∀ s, Mg.pub (moreItem (sentName m)) (pi, s) = true → sentIsB dS x.link s = true)
    (askFree : Pub.freeAbove m ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubFree : ∀ s, Mg.pub (.freeAbove m) (pi, s) = true →
      H2K5.Door.freeAboveB x.ns s = true)
    (hTests : maskTestsB (maskMsg D x.link) (keptAt D x.link).length (dS.own x.link) N ps[k + 1]?
      Ld M (N.sent m 0) seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨sigListCalls D rad x.link, seatT⟩, i⟩)
    (h6 : oneShapeB ms = true) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
      Rc a → a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
      attObjects x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard b.1 w :=
  calls_objects_att x D rad set seatT arr claim N Mg Mg₀ links ps pi k m Yes Rc ms Rd runs St after
    wt rw ah pr H l pass hB A tl hA hrun hlink hpass hfind hSt hMg
    (maskOkCalls_of_facts x D rad seatT ms (N.sent m 0) m Yes Rc seatN hT hLive hGroups hSeats
      hShapes askSent pubSent askFree pubFree hTests hsome h6)
    hBare

/-- **THE FIELD objects OF LayAtTableR, ITS PREMISE ON THE STATE PAID.** -/
theorem calls_objects_lay_facts (q : LayPub) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 2 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 2 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 2 "objects" (pi, s) y
        w)
    (hBare : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b →
      ∀ g, (Desc.K3.seatCalls claim).heard b.1 = some g → ∀ f ∈ g.rows.toList, Bare f)
    {dS : SentData} {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (seatN : ℕ → ℕ × ℕ)
    (hT : ∀ i, seatT i = seatN i.val)
    (hLive : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.shape = D.shape)
    (hGroups : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hSeats : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstShapes M a.1 = true)
    (askSent : moreItem (sentName m) ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubSent : ∀ s, Mg.pub (moreItem (sentName m)) (pi, s) = true → sentIsB dS x.link s = true)
    (askFree : Pub.freeAbove m ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubFree : ∀ s, Mg.pub (.freeAbove m) (pi, s) = true →
      H2K5.Door.freeAboveB x.ns s = true)
    (hTests : maskTestsB (maskMsg D x.link) (keptAt D x.link).length (dS.own x.link) N ps[k + 1]?
      Ld M (N.sent m 0) seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨sigListCalls D rad x.link, seatT⟩, i⟩)
    (h6 : oneShapeB ms = true) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
      Rc a → a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
      layObjects x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard b.1 w :=
  calls_objects_lay x D rad set seatT arr claim N Mg Mg₀ links ps pi k m Yes Rc ms Rd runs St after
    wt rw ah pr H l pass hB q tl oW wOf nr nc msgW hA hrun hlink hpass hfind hSt hMg
    (maskOkCalls_of_facts x D rad seatT ms (N.sent m 0) m Yes Rc seatN hT hLive hGroups hSeats
      hShapes askSent pubSent askFree pubFree hTests hsome h6)
    hBare

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_objects_att_facts
#print axioms VerifiableInference.OnPublicFiles.calls_objects_lay_facts

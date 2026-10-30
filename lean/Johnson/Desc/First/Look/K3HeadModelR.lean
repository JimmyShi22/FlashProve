-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadModelR.lean: the lookup on the output head's calls: `HeadLeftR`
(Johnson/Desc/First/Look/K3HeadRestR.lean: objects, model, smallBack) CUT IN THREE, so that each of
its fields can be paid apart: `HeadModelR`: the field model alone, at the same letters;
`headLeft_of`: objects, `HeadModelR` and smallBack give `HeadLeftR`.

THE TEXTS ARE `HeadLeftR`'s OWN, LAID HERE BY A PROGRAM; Lean holds each against its original.

Limits: a definition and a re-packing. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3HeadRestR

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

/-- **The field model, alone.** -/
structure HeadModelR {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
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

/-- **The three give the structure.** -/
theorem headLeft_of {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
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
    (objects :
      ∀ (a b : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
    a.1.failed = none → Yes a b → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
    onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
    Mg.formsT m 3 "objects" (pi, b.1) (strsOf Fr b.2) w →
    K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) b.1 w)
    (M : HeadModelR G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q gd Rc claim N
      Mg links ps pi k m Yes)
    (smallBack :
      ∀ (a b : Desc.First.S × Fr.E.Str) w, Yes a b → SameBut a.1 b.1 →
    Mg.constr m .small (pi, b.1) (strsOf Fr b.2) w →
    Mg.constr m .small (pi, a.1) (strsOf Fr a.2) w) :
    HeadLeftR G adr x tl D rad oW wOf nr nc set seatT arr smp smpW strW msgW Q gd Rc claim N Mg
      links ps pi k m Yes :=
  ⟨objects, M.model, smallBack⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headLeft_of

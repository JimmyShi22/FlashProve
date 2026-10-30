-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Skeleton/Start.lean: the records from which the steps start, in the second form of the check
of a proof file's first hash chain by the Lean verifier program `verify-on-bytes` (OnBytes/); see
Johnson/Skeleton/Steps.lean: definitions with code; no theorem is about them.

`Files`: the seven files of a call, as bytes. `startG`, `startA`, `startF`, `startM`: the record of
local values before a link of the kind "layers", before a link of the kind "attention", before the
steps of `ChainCheck.finish` and before those of `memberFirstVerify` (Johnson/Skeleton/SpyLay.lean,
SpyAtt.lean, SpyTail.lean). Each holds the two values that the program passes from link to link (a
`ChainCheck` and a `Proof.LinksResult`), and placeholders in all other fields. `endedB`: what
`Blk.runOn` asks of the context at the end of a run.

Limits: definitions only; nothing is evaluated in this file and nothing is proved about it. That no
step reads a placeholder before a step has filled the field is our reading of the steps, not a
theorem; no step fills one field (`FinishLoc.D`: see SpyTail.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Skeleton.SpyLay
import Johnson.Skeleton.SpyAtt
import Johnson.Skeleton.SpyTail
import Johnson.RunOne.Letters
import OnBytes.Cut.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Three records of the library get a default value, for fields that no step has filled yet. -/
deriving instance Inhabited for OnBytes.Attention.Divide
deriving instance Inhabited for OnBytes.Attention.Attain
deriving instance Inhabited for OnBytes.Attention.Tables

namespace KObj.Course.SpyK1
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- The seven files of a call. -/
structure Files where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  ent : ByteArray
  request : ByteArray
  y : ByteArray
  proof : ByteArray

/-- A value of what the own rounds of a link of the kind "layers" return, for the record before the
link: a placeholder. By our reading of SpyLay.lean no step reads it before `gOwn`, the step that
fills it. -/
def blankOwn : Layer.Own :=
  { v := { y := { h := default }, sc := default, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] },
    H := { fo := default, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := default, sPv := 0,
           omV := #[], tV := default },
    K := { rs := #[], sA0 := 0, sH1 := 0, sB0 := 0, sV := 0, fin := {}, rowS := {} },
    hd := default, hd2 := none, sVE := 0, wo := default, funs := #[] }

/-- The record before a link of the kind "attention": the two values that pass from link to link;
all other fields are placeholders. -/
def startA (check : ChainCheck) (out : Proof.LinksResult) : AttLoc :=
  { check := check, out := out, L := { check := check }, F := {}, tl := {}, g := default,
    planes := #[], scores := #[], d := default, x := default, t := default, slotA := 0 }

/-- The record before a link of the kind "layers": likewise. -/
def startG (check : ChainCheck) (out : Proof.LinksResult) : LayLoc :=
  { check := check, out := out, L := { check := check }, F := {}, fo := default, own := blankOwn,
    tl := {}, slotA := 0 }

/-- A value of the record of a code switch's run, for the field that no step fills. c: any context.
-/
def blankTaken (c : Ctx) : Tie.Pv.Switch.LocTaken :=
  { lay := default, ids := #[], shapes := [], dS := ⟨[], [], [], none⟩, seeds := [],
    code := default, dL := ⟨[], [], [], none⟩, eL := { name := "" }, y := #[], c0 := c, c1 := c,
    cA := c, cB := c, cC := c, cD := c }

/-- The record before the steps of `ChainCheck.finish`. c: the context there. -/
def startF (check : ChainCheck) (out : Proof.LinksResult) (c : Ctx) : FinishLoc :=
  { check := check, out := out, G := default, fr := check.frame, sw := default, D := blankTaken c,
    answers := 0, cur := default, later := [], row := default, L := default, mask := none,
    st := default }

/-- The record before the steps of `memberFirstVerify`. -/
def startM (check : ChainCheck) (out : Proof.LinksResult) : MemberLoc :=
  { check := check, out := out, rows := [], msg := #[], ids := #[], lin := default }

/-- What `Blk.runOn` asks of the context at the end of a run: no named test has failed, and nothing
is left over. -/
def endedB (c : Ctx) : Bool :=
  c.failed.isNone && c.ch.entries.isEmpty && c.ch.settled && c.ch.cur.isNone &&
    c.ch.opened.isEmpty && c.ch.left.isEmpty

end KObj.Course.SpyK1

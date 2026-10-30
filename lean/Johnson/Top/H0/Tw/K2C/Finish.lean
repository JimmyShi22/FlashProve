-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2C/Finish.lean: the kind «the code switch» at the finish: THE WHOLE PLACE «F:1»:
"F.0.front" · "F.0.call" · "F.0.quiet". The record enters the finish by S.enterFin?, the form that
refuses at once: so a record that comes in marked is refused here, under its mark. Each refusal
under its guard's name. definitions with code; no theorem.
  finishFrontQ   [B0] the record stands between the links · [W8] the finish is due (the walk's
  finishDue; Model/ReqChain.lean:146) · [F10] a first message is due and the frame stands behind the
  last link (Iop/Req.lean:373) · [F3] the groups' list has the
                 last test's (:374) · [F4-F6] a new group (the plain ground's newGroupP; :375 over
                 :307-309) · the record enters the finish and holds the group's record and the frame
                 behind the new group
  finishBehindQ  [F11] the switch returned the fresh mask's number (Iop/Req.lean:377): it is kept
  for the last test
No soundness.
-/
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open Johnson.Desc.First.Walk (finishDue)

def finishFrontQ (s : S) : Except String S :=
  if !s.atBetween then .error "B0: the record does not stand between the links"
  else if !finishDue s.check then .error "W8: the finish is not due (lot L20's finishDue)"
  else
      match s.check.frame.groups[s.check.frame.link]?,
          _root_.Tw.K2.finishFront s.st s.check.frame with
    | some G, .ok x =>
      s.enterFin?.bind fun s₁ =>
        match s₁.here with
        | .fin a => .ok { s₁ with st := x.st, here := .fin { a with G := some G, fr := x.f } }
        | _ => .error "B3: the record has not entered the finish"
    | _, .error e => .error e
    | none, _ => .error "F3: there is no group for the last test"

def finishBehindQ (s : S) : Except String S :=
  match s.here with
  | .fin a => (_root_.Tw.K2.finishBehind a.sw).map fun m =>
      { s with here := .fin { a with mask := some m } }
  | _ => .error "B2: the record stands at another sort of place than the block"

/-- **The place «F:1».** p: the switch's numbers there (p.stands = .finish). -/
def finishPlace {Cl : Type} (p : P2) : Block S Cl :=
  { ((roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece
      finishFrontQ).andThen p.name (codeSwitchKind p)).andThen p.name
      (roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece finishBehindQ)
          with place := p.place }

end VerifiableInference.Desc.First.K2

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Walk/Quiet.lean: the quiet lines of the walk over the first chain's links, as
plain functions on data: what the routine of the program `verify-on-bytes` that walks the links
(runLinkH, OnBytes/Model/StagesLinks.lean:558-581) does itself, in front of a sub-proof's check and
behind it, and the own lines of the four calls of ChainCheck (OnBytes/Model/ReqChain.lean:111-147).
"Quiet": no round is closed and no item or column is taken.

  LinkPub      a link's record (LinkH, StagesLinks.lean:79-107) without its routine: public data
               alone
  firstDue | firstKept     ChainCheck.first's own guard, and what it writes behind the frame's call
  front        behind a link's first call, in front of the sub-proof: "plan-head"; the walk stands
               at link l; the link's context laid; the walk's result handed on as it is
  samePlan     the sub-proof has worked on the plan that the record holds (that verifier's text, at
               LinkPub)
  back         behind the sub-proof: handed and done; samePlan; where the record says that a row is
               left, something is returned
  pendingKept  the row is laid at the end of the list (the row itself is made elsewhere:
               Johnson/Desc/First/Pend/Row.lean)
  laterDue | laterKept, closeDue | closeKept, finishDue     the own lines of ChainCheck.later |
               close | finish
  SW, frontStep, backStep     the same at the one Step type, on the part of the carried record that
               these lines read and write

Not here: the frame's calls (ReqFrame.first, "REPLY", later, close, finish); indexMasksH at link 0
(:561-565: LinkZero.lean); the sub-proof's check (:572); pendingRowH (:579); the row of the link's
equation (ReqChain.lean:131-132). Blk.inPlace (:572) turns a refusal's place alone, no verdict: it
has no counterpart.

Every guard here is on public numbers or on marks of the order of steps: on a real file none says
no; a control can only be a made-up state or a turned record.

Written anew after that verifier's text, down to the records' fields: its small readers
ChainCheck.link | links | plain (ReqChain.lean:75-85) are written out (frame.link,
frame.shape.link.length, frame.plain). One pure routine of it is called by name:
ChainCheck.momentsDue (:96, over reqMoments), in laterDue | closeDue alone.

Limits. No Blk, no Ctx, no SubM, no LinkM in any type of this file. But the records that it reads
(ChainCheck, LinkCtx, Fork, Tail2, LinksResult, WsForkOut) are that verifier's, carried whole, and
their homes (Model/ReqChain, Trees, Hide, Merge, Proof/File) hold running code too: until the
records move out of these modules this file stands on modules that have the monad in a type.
No soundness: definitions with code.

-/
import OnBytes.Model.Trees
import OnBytes.Model.Merge
import OnBytes.Proof.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model

abbrev Col : Type := Nat × Nat × List UInt64

/-- The one Step type: the state · this stretch's rounds · the opened columns not yet taken ↦
the state and how many columns the step took | a refusal. -/
abbrev Step (S : Type) : Type := S → List Fmt.RoundView → List Col → Option (S × Nat)

/-- A link's record without its routine. The fields and their order are LinkH's
  (StagesLinks.lean:79-105); g, gid, tl and ns, which
these lines do not read, are left out. -/
structure LinkPub where
  /-- the link's name: G0, A0, .., H -/
  name : String := ""
  /-- 0 layers, 1 attention, 2 the head -/
  kind : Nat := 0
  /-- the planned state of the sub-proof's check: its arrays have their sizes -/
  Fp : Fork := {}
  /-- the sub-proof's list of arrays -/
  Tp : Tail2 := {}
  /-- the sub-proof leaves a row on the weight table -/
  fv : Bool := false
  /-- the number of the sub-proof's claims on the weights by its plan -/
  NCL : Nat := 0
  /-- for each array of the list: the link that commits to it, and its name there -/
  arrayOf : Array (Nat × String) := #[]

/-! ## ChainCheck's own lines -/

/-- **A link's first call is due.**
 [W0] not in a link, and a link is left                     ReqChain.lean:112 -/
def firstDue (c : ChainCheck) : Bool := !c.inLink && decide (c.frame.link <
    c.frame.shape.link.length)

/-- What ChainCheck.first writes behind the frame's call. f, sent: what that call returned.
  ReqChain.lean:114 -/
def firstKept (c : ChainCheck) (f : ReqFrame) (sent : Array Nat) : ChainCheck :=
  { c with frame := f, sent := sent, inLink := true, moments := 1 }

/-- **A further moment is due.**
 [W6] in a link, and the shape gives it a moment more       ReqChain.lean:118 -/
def laterDue (c : ChainCheck) : Bool := c.inLink && decide (c.moments < c.momentsDue)

/-- What ChainCheck.later writes behind the frame's call.
  ReqChain.lean:120 -/
def laterKept (c : ChainCheck) (f : ReqFrame) (sent : Array Nat) : ChainCheck :=
  { c with frame := f, sent := sent, moments := c.moments + 1 }

/-- **The link's closing is due.**
 [W7] in a link, and all its moments have been received     ReqChain.lean:130 -/
def closeDue (c : ChainCheck) : Bool := c.inLink && c.moments == c.momentsDue

/-- What ChainCheck.close writes behind the frame's call.
  ReqChain.lean:134 -/
def closeKept (c : ChainCheck) (f : ReqFrame) : ChainCheck := { c with frame := f, inLink := false }

/-- **The finish is due.**
 [W8] not in a link, and every link is behind               ReqChain.lean:146 -/
def finishDue (c : ChainCheck) : Bool := !c.inLink && c.frame.link == c.frame.shape.link.length

/-! ## In front of the sub-proof -/

/-- **Behind a link's first call, in front of its sub-proof.** check: as ChainCheck.first has
  returned it. out: at link 0 with the
index-mask message's number laid in (LinkZero.lean).
 [W1] «plan-head»: one plain scalar was received at the head's link, none elsewhere
   StagesLinks.lean:566
 (e1) NOT DONE HERE: that verifier lays the reply at this point (StagesLinks.lean:567). In this
   description the reply has one writer, the block that hears it: out is handed on as it is
 [W2] the walk stands at the link for which the record was made
   StagesLinks.lean:569
 (e2) the link's context: the check · l · the record's arrayOf and list; one moment has passed;
   neither handed nor done
                                                     StagesLinks.lean:570 with Trees.lean:169-185 -/
def front (X : LinkPub) (l : Nat) (check : ChainCheck) (out : Proof.LinksResult) :
    Except String (LinkCtx × Proof.LinksResult) :=
  if !(check.frame.plain.length == (if X.kind == 2 then 1 else 0)) then .error
      "W1: plan-head: the number of plain scalars"
  else if !(check.frame.link == l) then .error "W2: the walk is not at the record's link"
  else .ok ({ check := check, link := l, arrayOf := X.arrayOf, list := X.Tp }, out)

/-! ## Behind the sub-proof -/

/-- True if the check of a sub-proof has worked on the plan that X holds: the same list of arrays,
  and for each array of the list the
same rows and columns. The text of `verify-on-bytes` (StagesLinks.lean:548-553), at the record
  without the routine. -/
def samePlan (X : LinkPub) (F : Fork) (list : Tail2) : Bool :=
  list.nt == X.Tp.nt &&
    (List.range X.Tp.nt.size).all fun t =>
      match F.trees[t]?, X.Fp.trees[t]? with
      | some a, some b => a.R == b.R && a.K == b.K
      | _, _ => false

/-- **Behind a link's sub-proof.** o, C, F: what the sub-proof's check returned, and the link's
  context and the fork with which it ended.
Returns the chain's check, and what is to become a row on the weight table, if the record says that
  one is left.
 [W3] «plan-link»: the last challenge has been drawn, and the link is closed
   StagesLinks.lean:574
 [W4] «plan-link»: the check has worked on the record's plan
   StagesLinks.lean:575
 [W5] «plan-link»: where the record says that a row is left, the check has returned what is
   needed      StagesLinks.lean:576-578
 (e3) the chain's check is the context's
   StagesLinks.lean:580, :581 -/
def back (X : LinkPub) (o : Option WsForkOut) (C : LinkCtx) (F : Fork) : Except String (ChainCheck ×
    Option WsForkOut) :=
  if !(C.handed && C.done) then .error
      "W3: plan-link: the sub-proof has not drawn its last challenge or not closed its link"
  else if !samePlan X F C.list then .error "W4: plan-link: the sub-proof has worked on another plan"
  else if X.fv then
    match o with
    | some o => .ok (C.check, some o)
    | none => .error "W5: plan-link: the sub-proof has returned nothing for its row"
  else .ok (C.check, none)

/-- (e4) The row is laid at the end of the list.
  StagesLinks.lean:580 -/
def pendingKept (out : Proof.LinksResult) (row : TensorRow) : Proof.LinksResult :=
  { out with pending := out.pending ++ [row] }

/-! ## At the one Step type -/

/-- What these lines read and write of the carried record. run: none between two links; within a
  link the link's context, the fork and
what the sub-proof's check has returned so far. WITHIN A LINK THE CHAIN's CHECK IS THE CONTEXT's
  (run's first part): check is then stale,
as `verify-on-bytes`'s variable is (StagesLinks.lean:570-581). -/
structure SW where
  check : ChainCheck
  out : Proof.LinksResult
  run : Option (LinkCtx × Fork × Option WsForkOut) := none
  /-- the statement's messages: read and written by the pending row's function alone -/
  oracles : Array Oracle := #[]

/-- The words of frontStep's refusal.
 [S1] the stretch has no round                              (the table's «take»)
 [S2] no link is running                                    (`verify-on-bytes`'s order of
   lines) -/
def frontE (X : LinkPub) (l : Nat) (s : SW) (rounds : List Fmt.RoundView) : Except String SW :=
  if !rounds.isEmpty then .error "S1: a quiet step is handed a round"
  else if s.run.isSome then .error "S2: a link is running"
  else (front X l s.check s.out).map fun y => { s with out := y.2, run := some (y.1, X.Fp, none) }

/-- **‹g|a›FirstQuiet's and sSwitchQuiet's share of the walk.** The sub-proof starts from the
  record's planned fork (:572). -/
def frontStep (X : LinkPub) (l : Nat) : Step SW := fun s r _ => (frontE X l s r).toOption.map (·, 0)

/-- The pending row as a plain function: an argument of the step (its text:
  Johnson/Desc/First/Pend/Row.lean). It is handed the statement's
messages (the index-mask message's ledger lies among them), takes the ledger's next free entry there
  (StagesLinks.lean:527: Blk.takeMask) and gives them back: so
no ledger can be closed over. -/
abbrev RowFn : Type :=
  (indexMasks : Nat) → WsForkOut → (claims : Nat) → Array Oracle → Except String (TensorRow × Array
      Oracle)

/-- The words of backStep's refusal.
 [S1] the stretch has no round
 [S3] a link is running -/
def backE (X : LinkPub) (row : RowFn) (s : SW) (rounds : List Fmt.RoundView) : Except String SW :=
  if !rounds.isEmpty then .error "S1: a quiet step is handed a round"
  else match s.run with
    | none => .error "S3: no link is running"
    | some (C, F, o) => do
      let y ← back X o C F
      match y.2 with
      | none => pure { s with check := y.1, run := none }
      | some w =>
        let r ← row s.out.indexMasks w X.NCL s.oracles
        pure { check := y.1, out := pendingKept s.out r.1, run := none, oracles := r.2 }

/-- **‹g|a|s›DoorQuiet's share of the walk.** -/
def backStep (X : LinkPub) (row : RowFn) : Step SW := fun s r _ => (backE X row s r).toOption.map
    (·, 0)

end Johnson.Desc.First.Walk

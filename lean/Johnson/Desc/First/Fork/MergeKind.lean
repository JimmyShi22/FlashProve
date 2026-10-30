-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Fork/MergeKind.lean: the merge of the claims on the committed weights at the
head's link, as a block of a file's description (Johnson/Desc/Block.lean). Definitions with code.
Every refusal bears the name of the test that refused.

ROUNDS, at a matrix with 2^lk columns and n claims (`mergeEntries`: lk + 4 entries of the plan, as a
function of three numbers). 1: nothing is sent; one element is drawn; the entry counts n rows. 2:
one scalar; one element. 3 to lk + 2: two scalars; one element. lk + 3: one scalar; one element,
drawn other than 0. lk + 4: one scalar; nothing is drawn. A scalar has 24 bytes. Each round that
draws has the setting's bits of work for an error of the field's kind
(OnBytes/Params/Planner.lean:213, with PlanListsSub.lean:181-183 and PlanListsSum.lean:41-60); the
last has none (PlanningLaws.lean:71). FIXED BEFORE THE DRAW: every oracle message that the first
chain has sent so far. The block opens no tree: so `before` names every tree that it opens.

READS. No oracle is read.

DECIDES (`headMergeDecide`). At the head's part of the carried record
(Johnson/Desc/First/State.lean): the claim, the slot of its value, the ledger; what is owed by the
round in front is asked by the record's own `noneWaits` (no rows, or 0 rows, are owed). `mergeHear`
is the program `verify-on-bytes`'s wsForkEnd with
wsForkMerge (OnBytes/Model/Merge.lean:65-112), line for line, over the library's flat functions
(OnBytes/K/Kc/Flat.lean, QuietLink.lean), each call under a name; the test on a claim's sizes is
this
file's own text (`claimFits`, `facFits`). No equation between sent values is tested. It writes what
the merge leaves, the ledger behind and in front of it, the next free slot,
and that nothing is owed behind it. What `Block.step` asks already (each message's items by the
entry's cut; the three numbers of draws) is asked once more by the tape's maker: kept, because the
step does not ask an entry's rows or what is owed.

CLAIMS (`headMergeClaim`). One run, "the merge": the claim that the merge's sumcheck leaves
(`Fl.pscRow`): a form that must be 0. The run lays, in the ledger, the pairs (0, -1) under the slots
of the hiding polynomial's coefficients. It reads neither the number that it is handed nor the
ledger's counter. In the protocol's order it is the last of the head's link.

THE TESTS ON THE PLAN ALONE: the plan counts one claim on the weights (Head.lean:319).

SENDS: Johnson/Desc/ProofFile/Honest/K11/Part.lean; for its parameter `claims` see ClaimsN.lean.

Limits: no theorem. The head's link alone: one claim; `mergeHear` is general in the number of
claims. A name that begins "the masked sumcheck" or "the reading" stands for all tests of the
function that is called there. It calls `verify-on-bytes`'s pure functions and
plain records by name: among them, through the flat functions, the ledger's tests (Fork.hideRun,
Fork.publicPart, Fork.shown) and the tests on a sumcheck's weights. Nothing on soundness or on
hiding.
The namespace is Johnson.Desc.First.ForkMerge.
-/
import Johnson.Desc.Block
import Johnson.Desc.Claim
import Johnson.Desc.First.State
import Johnson.Desc.First.Look.LookStep
import Johnson.Desc.First.Door.Door
import OnBytes.K.Kc.Laws
import OnBytes.K.Kc.QuietLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge

open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff WsLay WsClaim WsForkOut RoundName WsFac WsGrp)
open OnBytes.Model (wsForkStart wsRowPart wsEpsT)
open VerifiableInference.Desc (Block Kind Claim named need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (tapeS)
open VerifiableInference.Desc.First.Door (batchEntryB batchRoundB)

/-- The numbers of the merge's place at the head's link. -/
structure HeadMergeP where
  /-- the link's number on the first chain, and the block's number inside the link -/
  link : Nat
  piece : Nat
  /-- the layout of the committed matrix of weights -/
  lay : WsLay
  /-- the setting's bits of work for a round whose error is of the field's kind -/
  work : Nat
  /-- the oracle messages that the first chain has sent in front of this place -/
  sent : Nat
  /-- the plan's numbers of claims on the weights, of slots and of claims of the sub-proof -/
  ncl : Nat
  nMsg : Nat
  nLin : Nat

/-- **ROUNDS**: the merge's entries of the plan. -/
def mergeEntries (lk n work : Nat) : List Fmt.Entry :=
  { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } ::
  { name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } ::
  (List.replicate lk { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } ++
    [{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
     { name := RoundName.pscValues.name, msg := 24 }])

/-- The stretch as a tape, each of its three conditions named. -/
def mergeTapeE : List Fmt.RoundView → List Fmt.Entry → Except String Tape
  | r :: rs, e :: es => do
    need "the merge: the batching round's entry" (batchEntryB e)
    need "the merge: the batching round as it is shown" (batchRoundB e r)
    let t ← named "the reading: a round of the merge's sumcheck" (tapeS rs es)
    pure (flatOf r (some e) :: t)
  | _, _ => .error "the merge: no round or no entry"

/-- A factor has the sizes that its index group asks for. At a group of the class 'E': one element
for
each value of the index's high part, one coordinate for each bit of its low part, and no table. At
any other group: one element for each index, and nothing else. -/
def facFits (x : WsFac) (g : WsGrp) : Bool :=
  if g.cls == 'E' then x.HV.size == g.o && x.pt.size == g.z && x.AV.size == 0
  else x.AV.size == g.R && x.HV.size == 0 && x.pt.size == 0

/-- A claim's factors fit its unit in the layout: the layout has the unit; the claim has one factor
for each of the unit's index groups; each factor has its group's sizes. `wsEpsT`
(OnBytes/Model/Weights.lean) is defined without this test too: by its own docstring it gives 0 where
the layout has no such unit, and reads 0 beyond the end of an array. This test rules both out. -/
def claimFits (lay : WsLay) (c : WsClaim) : Bool :=
  match lay.U[c.ui]? with
  | none => false
  | some u => c.f.length == u.g.length && (c.f.zip u.g).all fun y => facFits y.1 y.2

/-- What is heard: `verify-on-bytes`'s wsForkEnd with wsForkMerge, each call under a name. -/
def mergeHear (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (F : Fork) (t : Tape) :
    Except String (WsForkOut × Fork × Tape) := do
  need "the merge: the numbers of claims and of slots"
    (!cl.isEmpty && cl.size ≤ 4096 && sv.size == cl.size)
  need "the merge: a claim's unit is not in the layout" (cl.all fun c => c.ui < lay.U.size)
  need "the merge: a claim's factors do not fit its unit"
    (cl.all fun c => claimFits lay c)
  let (rho, F, t) ← named "the reading: the batching round's close" (Fl.batch sv.size F t)
  let C := wsForkStart sv rho
  let (v, F, t) ← named "the ledger: a claim's value was not sent" (Fl.publicPart C F t)
  let (p, F, t) ← named "the masked sumcheck: the beginning" (Fl.pscBeginAt v F t)
  let p := { p with start := C, started := true }
  let ((rm, p), F, t) ← named "the masked sumcheck: a round"
    (Fl.wsForkRounds lay.lk (Array.emptyWithCapacity lay.lk) p F t)
  let ((sFv, p), F, t) ← named "the masked sumcheck: the closing round and the end value"
    (Fl.pscEnds p 1 1 F t)
  let (fvp, F, t) ← named "the ledger: the end value's slot" (Fl.shown sFv F t)
  pure ({ fvp := fvp, beta := p.r.back?.getD zeroE, rm := rm, p := p, sFv := sFv
          recs := (cl.zip rho).toList.map fun y =>
            wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm)) }, F, t)

/-- **DECIDES.** -/
def headMergeDecide (P : HeadMergeP) (s : S) (rs : List Fmt.RoundView) : Except String S :=
  match s.here with
  | .head a => do
    need "the merge: the head's ledger is not laid" a.opened
    need "the merge: rows are owed by the round in front" s.noneWaits
    let t ← mergeTapeE rs (mergeEntries P.lay.lk 1 P.work)
    let claim ← named "the merge: the claim on the weights is not laid" a.claim
    let x ← named "the merge: what the head heard is not laid" a.x
    let (wo, F, t) ← mergeHear P.lay #[claim] #[x.sV] a.F t
    need "the merge: the stretch is not used up" t.isEmpty
    need "the merge: the next free slot is not the plan's number of slots" (F.next == P.nMsg)
    pure { s with rowsOwed := none
                  here := .head { a with wo := some wo, F := { F with planClaimsF := P.nLin },
                                         Fm := a.F, slot := some F.next } }
  | _ => .error "the merge: not inside the head's link"

/-- **CLAIMS**: the claim that the merge's sumcheck leaves. -/
def headMergeClaim (_ : Nat) (s : S) : Except String (List Claim × S) :=
  match s.here with
  | .head a => do
    let wo ← named "the merge: it has not run" a.wo
    let x ← named "the masked sumcheck: the claim that the sumcheck leaves"
      (Fl.pscRow wo.p wo.fvp {} a.F [])
    pure ([{ form := x.1.1 }], { s with here := .head { a with F := x.2.1 } })
  | _ => .error "the merge: not inside the head's link"

/-- **The kind.** -/
def headClaimMergeKind : Kind HeadMergeP S Claim := fun P =>
  { name := "the merge of the claims on the weights"
    place := ⟨1, some P.link, P.piece, .K11⟩
    planOk := P.ncl == 1
    rounds := (mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }
    oracles := List.replicate (P.lay.lk + 4) []
    before := (List.range P.sent).map fun n => (1, n)
    decide := fun s rs _ => headMergeDecide P s rs
    claims := [("the merge", headMergeClaim)]
    after := [] }

end Johnson.Desc.First.ForkMerge

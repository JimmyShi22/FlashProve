-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Text.lean (kind K9: THE BATCHING DRAW AND THE ONE EQUATION): DEFINITIONS
WITH CODE; NO THEOREM.
Plain functions on data. EACH TEST REFUSES UNDER A NAME OF ITS OWN.

WHAT THE KIND IS FOR. When all messages of a link have been heard, the link's other blocks leave n
linear claims: affine forms that must be 0, in the scalars that were sent under a mask (by their
slots) and in entries of committed arrays. K9 makes ONE claim of them, with random weights, and lays
it as one row on the link's group of oracle messages. It tests no equation of the protocol itself.

ROUNDS. One round, "BAT-sigma". The prover sends nothing. The verifier draws one element chi of the
extension field (0 is allowed). The plan's entry counts the rows that chi combines.
READS. Nothing.
DECIDES. draw: the round is as said; the link is ready for it; chi is laid into the sub-proof's
record; the entry's rows are handed on as owed. (Between the two the other kinds add their claims,
claim number c under chi^c.) equation: the sum of the claims, collected as weights L on the columns
of each virtual row, a coefficient on each slot and a constant, is written as
   sum over the virtual rows v of < w_v (x) L_v , array(v) >  +  < m , the mask row >  +  c  =  0 :
the scalar under slot j is shown_j - factor_j * (entry j of the mask row), so m_j = - coefficient_j
* factor_j and c = constant + sum_j coefficient_j * shown_j. door: the count of rows that is owed is
compared; the equation is made a row; the link's mask entries 0 .. ns - 1 are taken; the row is
laid.

Typed after `verify-on-bytes`'s t2Batch, doorH, doorTerms, rowWeights (OnBytes/Model/Trees.lean),
Fork.settle (OnBytes/Model/Hide.lean), closeAs (OnBytes/Model/Rounds.lean), Blk.close and
Blk.requireRows (OnBytes/Iop/Ground.lean), ChainCheck.close (OnBytes/Model/ReqChain.lean) and
ReqRows.row (OnBytes/Iop/ReqRows.lean). A test that the program makes on a view alone is made
always. The program's records (LinkCtx, Fork, HTree, HRow, ReqTerm, Row) are used as plain data. Its
PURE functions that are called by name CANNOT REFUSE: E.ofTriple, t2FillL, ChainCheck.momentsOf and
momentsDue, rowProduct, productWritten, pickIndex, clog2, Row.addRun (and, in `draw` alone, which no
block calls, Params.kindOf). What could refuse is said in own words in
Johnson/Desc/First/Batch/Lay.lean. The two effects on the statement are the plain functions
takeMaskP and addRowP (Johnson/Desc/First/Base/Ground.lean), by name.

What is not claimed. That a function here is the program's routine: no theorem says so. Nothing on
soundness, on an honest prover or on hiding.



-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.First.Batch.Lay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The rows that a closed round's entry counts and that nobody has compared yet: their number; or
nothing. -/
abbrev RowsOwed : Type := Option Nat

/-! ## The draw -/

/-- What the draw hands on: the rows that are owed a count; the link's record; the sub-proof's. -/
structure Drawn where
  owed : RowsOwed
  L : LinkCtx
  F : Fork

/-- **The batching draw.** e: the plan's entry of the round. r: the round as the view shows it.
owed: the rows that are still owed a count. used: the number of slots that the messages have taken.
-/
def draw (e : Fmt.Entry) (r : Fmt.RoundView) (owed : RowsOwed) (used : Nat) (L : LinkCtx) (F : Fork) :
    Ans Drawn := do
  need "K9.nothing-owed" owed.isNone
  need "K9.entry-name" (e.name == RoundName.batSigma.name)
  need "K9.entry-kind" (Params.kindOf e.name == some .elems)
  need "K9.entry-not-zero" (e.drawNZ == 0)
  need "K9.entry-draws" (e.drawE == 1 && e.trits == 0 && e.poss == 0)
  need "K9.round-items" r.vals.isEmpty
  need "K9.round-draws" (r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits)
  let chi ← there "K9.one-element"
    (match r.drawn.elems with
     | [x] => some (E.ofTriple x)
     | _ => none)
  need "K9.slots-used" (L.list.planned && used == F.ns)
  need "K9.link-ready" (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link)
  need "K9.drawn-once" !F.thetaDrawnF
  need "K9.claims-planned" (F.planClaimsF != 0)
  pure
    { owed := some e.rows
      L := { L with list := { L.list with used := used }, handed := true }
      F := { t2FillL F L.list with
        theta := chi, thetaDrawnF := true, kapMapF := Array.replicate F.planClaimsF false } }

/-! ## The one equation -/

/-- The one equation, before it goes to the chain. -/
structure Equation where
  /-- the weights on the committed arrays -/
  terms : Array ReqTerm
  /-- the coefficients on the first entries of the link's mask row -/
  onMasks : Array E
  /-- the constant; the chain is given its negative as the target -/
  constant : E

/-- A virtual row's weights on the rows of X, as a product over the bits of a row's number. The
written-out weights must be the same function on the array's rows. -/
def rowWeights (X : HTree) (r : HRow) : Ans IndexWeights := do
  need "K9.row-form" (rowFormFits X r)
  let w := rowProduct X r
  let all := productWritten w
  need "K9.row-form-values" (everyBelow X.R fun i => all.getD i zeroE == r.coef.getD i zeroE)
  pure w

/-- The terms of one virtual row, behind those in acc. A row with a product form gives one term; any
other one for each row of the array, its weight there as the scale. -/
def rowTerms (born : Nat) (array : String) (X : HTree) (acc : Array ReqTerm) (r : HRow) :
    Ans (Array ReqTerm) := do
  need "K9.weights-sizes" (r.coef.size == X.R && r.L.size == X.K && r.L0 == 0)
  let onColumns : IndexWeights := { values := some r.L }
  if r.rowForm then
    let onRows ← rowWeights X r
    pure (acc.push { born := born, array := array, onRows := onRows, onColumns := onColumns })
  else
    pure ((List.range X.R).foldl (fun t i => t.push
      { born := born, array := array, scale := r.coef.getD i zeroE,
        onRows := pickIndex (clog2 X.R) i, onColumns := onColumns }) acc)

/-- The terms on the listed arrays, in the list's order. -/
def allTerms (L : LinkCtx) (F : Fork) : Ans (Array ReqTerm) :=
  (List.range L.list.nt.size).foldlM (fun (terms : Array ReqTerm) ti => do
    let (born, array) := L.arrayOf.getD ti (0, "")
    let X := F.trees.getD ti {}
    need "K9.array-laid" (arrayLaid L.check.rows.layout born array X.R X.K)
    X.rows.foldlM (rowTerms born array X) terms) #[]

/-- The slots put in: slot j with the coefficient l gives - l * factor_j on the mask row's entry j,
and adds l * shown_j to the constant. A slot with a coefficient must be filled. -/
def slotsIn (F : Fork) : Ans (Array E × E) := do
  let x ← F.LS.foldlM (fun (x : Nat × Array E × E) l => do
    if isZeroE l then pure (x.1 + 1, x.2.1, x.2.2)
    else
      need "K9.slot-with-coefficient-filled" (F.gotF.getD x.1 false)
      pure (x.1 + 1, x.2.1.set! x.1 (subE zeroE (mulE l (F.mf.getD x.1 zeroE))),
        addE x.2.2 (mulE l (F.vp.getD x.1 zeroE))))
    ((0, Array.replicate F.ns zeroE, F.c0) : Nat × Array E × E)
  pure x.2

/-- **The one equation.** Returns it with the sub-proof's record, in which no claim can be added any
more. -/
def equation (L : LinkCtx) (F₀ : Fork) : Ans (Equation × Fork) := do
  need "K9.door-once" (L.list.link && !L.list.walked && !L.done)
  let F := { F₀ with doorShutF := true }
  need "K9.draw-has-run" L.handed
  need "K9.claims-all-added" (F.planClaimsF != 0 && F.nClaim == F.planClaimsF)
  need "K9.weights-all-taken" (F.kapMapF.size == F.planClaimsF && F.kapMapF.all id)
  need "K9.no-weight-outside" ((F.trees.extract L.list.nt.size F.trees.size).all fun X =>
    X.rows.all fun r => r.L.all isZeroE)
  need "K9.arrays-named" (L.arrayOf.size == L.list.nt.size)
  need "K9.arrays-there" (decide (L.list.nt.size ≤ F.trees.size))
  let terms ← allTerms L F
  need "K9.slots-sizes" (decide (L.list.used ≤ F.ns) && F.gotF.size == F.ns && F.LS.size == F.ns &&
    F.vp.size == F.ns && F.mf.size == F.ns)
  need "K9.owed-claims-added" (F.owed.all (·.added))
  need "K9.slots-filled" (F.gotF.all id 0 L.list.used)
  let mc ← slotsIn F
  pure ({ terms := terms, onMasks := mc.1, constant := mc.2 }, F)

/-! ## The door: the equation as a row on the link's group -/

/-- The plain carried record. -/
abbrev St (X : Type) : Type := _root_.Desc.Plain.DState X

/-- The next n free mask entries of the message o, in the order of taking. -/
def takeN {X : Type} (o : Nat) : Nat → St X → List Nat → Ans (List Nat × St X)
  | 0, d, acc => .ok (acc.reverse, d)
  | n + 1, d, acc => do
    let x ← there "K9.mask-entry-free" (Ground.takeMaskP d o)
    takeN o n x.2 (x.1 :: acc)

/-- The equation as a row; the link's mask entries are taken here. -/
def asRow {X : Type} (R : ReqRows) (f : ReqFrame) (q : Equation) (d : St X) : Ans (Row × St X) := do
  let row ← termsRow R.layout f d.st q.terms.toList {}
  let target := subE zeroE q.constant
  if q.onMasks.isEmpty then pure ({ row with target := target }, d)
  else
    let messages := (f.shape.link[f.link]?.map (·.messages)).getD []
    let m ← there "K9.mask-row-there" (messages.findIdx? fun x => x.shape.maskRows != 0)
    need "K9.one-mask-row" ((messages[m]?.map (·.shape.maskRows)) == some 1)
    let o ← there "K9.mask-message-here" (messageNow f f.link m)
    let x ← takeN o q.onMasks.size d []
    need "K9.mask-from-0" (x.1.head? == some 0 && x.1.getLast? == some (x.1.length - 1))
    pure ({ row.addRun o .mask 0 1 (.own q.onMasks) with target := target }, x.2)

/-- What the door hands on. -/
structure Out (X : Type) where
  owed : RowsOwed
  L : LinkCtx
  F : Fork
  d : St X

/-- **The door, up to the row laid.** owed: the rows that are owed a count. laid: the number of
indices that the smallness test's equations take; nothing before its claims have been made. -/
def door {X : Type} (owed : RowsOwed) (laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X) :
    Ans (Out X) := do
  let laid ← there "K9.equations-laid" laid
  let x ← equation L F
  need "K9.rows-counted" (owed == some (x.2.nClaim + laid))
  need "K9.link-is-the-walks" (L.link == L.check.link)
  need "K9.moments-passed" (L.check.inLink && L.check.moments == L.check.momentsDue)
  let y ← asRow L.check.rows L.check.frame x.1 d
  let d' ← there "K9.row-fits" (Ground.addRowP y.2 L.check.group y.1)
  pure { owed := none, L := L, F := x.2, d := d' }

/-- The link's record behind the closing: the closing's frame; no link is under way; the door has
been walked. -/
def closed (L : LinkCtx) (f : ReqFrame) : LinkCtx :=
  { L with check := { L.check with frame := f, inLink := false },
           list := { L.list with walked := true }, done := true }

end VerifiableInference.Desc.K9

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFold.lean: THE FORM's HALF AT A FOLD: the letters for saying that the
description's fold (foldD, Johnson/Desc/First/Close/Closing.lean), the proximity test's plain part
over it (foldE, Johnson/Desc/K12/Parts.lean) and its part in the kind's block (foldJ,
Johnson/Desc/K12/Join.lean; guardedProximityTestParts.fold, JoinGuarded.lean) RETURN ok: from facts on the plan, on the
view's format and on the carried record. ONE OF THEM READS ELEMENTS: FoldFront.rowFits
(Own.foldRowFits calls formFits: each written-out variable of a vector of product form has the pair
(1, 1): an equality of elements on the row's coefficients, which come from drawn values); no other
reads a value that is sent or drawn.

What is proved of them: Johnson/Prover/Link/FormFoldLaws.lean.

Main names.
  elemEntry name items e   a test on an entry of the plan: it is the entry of a round in which
    "items" elements are sent, no root, and one element is drawn; it counts no rows.
  foldCut k cut    a test on the declared rounds that the frame deals to a fold: "FOLD epsilon" (one
    element), then k times "FOLD round" (two); none opens a tree or a stored table.
  foldCuts cur rest l   foldCut at the frame's cut for each stage's fold.
  spent S id       the statement with the message number id marked as spent as a mask:
    spendAsMaskP's own effect (Johnson/Desc/First/Base/Ground.lean).
  FoldFront p j cur t   THE CARRIED RECORD IN FRONT OF A FOLD (the first form of the invariant's
    part on form): what passes is one claim; the stage and the next stage's codes are the plan's;
    the three tests in front of a fold (Johnson/Desc/Own/Fold.lean) say yes; the mask has come and
    can be spent; the new group's codes are there.
  sentOf, drawnOf, claimStep, claimOf   what the fold reads off its rounds: the elements that a
    round shows as sent; the one drawn; the running claim.
  foldOutAt, foldOut, foldT   the single rows that the fold returns, and THE RECORD BEHIND IT, as
    functions of the record in front and the rounds.

Limits. Letters and tests: nothing says here that a record or a plan meets them. The arm in which
the fold's own first message brings the mask is not served: the mask has come (FoldFront.mask).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The entry of a round of elements: "items" are sent, one is drawn; no root; no rows counted. -/
def elemEntry (name : String) (items : Nat) (e : Fmt.Entry) : Bool :=
  e.name == name && e.drawNZ == 0 && e.count == 1 && e.msg == 24 * items && e.roots == 0 &&
    e.answers == 0 && e.poss == 0 && e.trits == 0 && e.drawE == 1 && e.rows == 0

/-- The declared rounds of a fold with k row variables. -/
def foldCut (k : Nat) : List Fmt.DeclaredRound → Bool
  | dE :: dR => elemEntry "FOLD epsilon" 1 dE.entry && dR.length == k &&
      dR.all (fun d => elemEntry "FOLD round" 2 d.entry) &&
      (dE :: dR).all fun d => d.stored.isEmpty && d.opens.isEmpty
  | [] => false

/-- The frame's cut for the fold of every stage but the last passes foldCut. l: the declared rounds
still to be dealt in front of the stage cur (the recursion of stagesFrom,
Johnson/Desc/K12/Frame.lean). -/
def foldCuts : Fmt.M1.Stage → List Fmt.M1.Stage → List Fmt.DeclaredRound → Bool
  | _, [], _ => true
  | cur, next :: rest, l =>
    foldCut cur.k (l.take (1 + cur.k)) && foldCuts next rest (l.drop (cur.k + 3))

/-- The message number id is marked as spent as a mask. WHERE THE STATEMENT HAS NO MESSAGE OF THAT
NUMBER: the statement as it was (`Array.modify`). -/
def spent (S : Statement) (id : Nat) : Statement :=
  { S with oracles := S.oracles.modify id fun x => { x with spentAsMask := true } }

/-- **The carried record in front of a fold.** -/
structure FoldFront (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (n : Nat × Nat) (id : Nat) : Prop where
  pass : t.pass = .claim row L
  stage : stageAt p j cur = some c
  next : p.idx[j + 1]? = some n
  shape : Own.foldShapeFits t.st (ioppFoldShape c L) = true
  mask : t.mask = some id
  maskFits : Own.foldMaskFits t.st (ioppFoldShape c L) id = true
  spend : Ground.ok (Ground.spendAsMaskL t.st id) = true
  rowFits : Own.foldRowFits t.st (ioppFoldShape c L) row = true
  group : Ground.ok (Ground.newGroupL t.st n.1 n.2) = true

/-- The elements that a round shows as sent: of its shown items (`vals`) those of the sort `.e`, in
their order; an item of another sort is passed over. The library has another function of this name,
`OnBytes.Slice.sentOf` (OnBytes/Slice/BlkCsRun.lean): the oracle messages of the prover's message of
a switch without kept members. FormStepPlan.lean and FormSwitch.lean read that one. -/
def sentOf (r : Fmt.RoundView) : List E :=
  r.vals.filterMap fun v =>
    match v with
    | .e x => some (E.ofTriple x)
    | _ => none

/-- The element that a round drew first. AT AN EMPTY LIST: (0, 0, 0): the value that a round which
drew the element 0 gives. Nothing here tests that the list is not empty. -/
def drawnOf (r : Fmt.RoundView) : E := E.ofTriple (r.drawn.elems.headD (0, 0, 0))

/-- The running claim behind one round "FOLD round". WHERE THE ROUND SHOWS FEWER THAN TWO ELEMENTS:
`zeroE` stands for each that is missing. Nothing here tests their number. -/
def claimStep (claim : E) (r : Fmt.RoundView) : E :=
  foldClaimRound claim ((sentOf r).getD 0 zeroE) ((sentOf r).getD 1 zeroE) (drawnOf r)

/-- The running claim behind the rounds "FOLD round". -/
def claimOf (rs : List Fmt.RoundView) (claim : E) : E := rs.foldl claimStep claim

/-- **The single rows that the fold returns**, at its rounds "FOLD epsilon" and "FOLD round". WHERE
"FOLD epsilon" SHOWS NO ELEMENT: `zeroE` stands for it. AT THE EMPTY LIST OF ROUNDS: the default
(`{}`). -/
def foldOutAt (S : Statement) (F : FoldShape) (row : GroupRow) (id : Nat) : List Fmt.RoundView → SingleRows
  | rE :: rR => foldOutput (spent S id) F row id (drawnOf rE) (rR.map drawnOf)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
  | [] => {}

/-- The same at the record inside a proximity test. -/
def foldOut (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (id : Nat)
    (rs : List Fmt.RoundView) : SingleRows :=
  foldOutAt t.st (ioppFoldShape c L) row id rs

/-- **The record behind the fold.** -/
def foldT (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat) (id : Nat)
    (rs : List Fmt.RoundView) : T12 :=
  { t with st := Ground.withGroup (spent t.st id) n.1 n.2
           pass := .single (foldOut t row L c id rs) t.st.groups.size }

end Johnson.Prover.Link

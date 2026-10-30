-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Says.lean: K15, (L2) «HANDS ON»: THE STATEMENTS ALONE, each a definition of type
Prop, with the three definitions that stand in them. NOTHING IS
PROVED IN THIS FILE. (A reader's ask: the statements apart from the proofs.) The proofs:
Johnson/Desc/K15/K15Law.lean (at the fold) · Johnson/Desc/K15/K15Run.lean (at the decision).
  ctxOf es d rs cols   a carried record with the rounds and columns still to come, in the form in
  which the library's facts are stated
  tailOf P             the link's two last blocks
  HandsOnFold          at the format's fold over the link's blocks 0 to 5, from a carried record AT
  WHOSE CODES THE PUBLIC SHAPE's CONDITIONS HOLD (a premise: the fold's own
  blocks do not ask them: the front does, on the plan)
  HandsOnRun           at (descOf P plan ok).run, for any parameters, plan and public test
  HandsOnLink          **at (linkDesc c plan).run**: the link as it was first described
  (Johnson/Desc/Link/LinkDescWithGroundSend.lean), at the planner's record c: P is no letter. VerifierAndGoals.theDescription
  does not run that text: it runs linkDescriptionAt (Johnson/Desc/Link/LinkDesc.lean), through linkDecisionAtParameterFile.
  linkDescV_yes (Johnson/Desc/K15/SendOwnPaid.lean): where linkDescV says yes, linkDesc says yes.
WHAT IT IS, IN ONE SENTENCE: where the entry file's link, written in
blocks, says yes on a view, with one answer to a sample,
its first five rounds have laid exactly the rows, statement, book and columns that the library's
record LinkRanR names, and no run of the hand-translated
program stands in a statement or a proof. IT IS THE TIE (L2), NOT THE KIND's LAW IN THE
FORM (a witness; bad values round by round): no row
K15_law | K15_rounds | K15_condition is met by it. It is the first of the records that hsem of
fr_link_joh | sr_link_joh needs; the batching's, the
folds', the switches' and the base case's are owed, as are the closed caller at the typed values and
the road from «written … dec».Sound to SoundAt.
(Where this and lean/THEOREM.md differ, the page holds.)
By itself it says nothing on soundness. Nothing on hiding.
-/
import Johnson.Desc.Link.LinkDescWithGroundSend
import OnBytes.Slice.BlkLinkRanRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block foldBlocks OneChainFileDescription OpenedColumn)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)

/-- A carried record, the rounds and the columns that are still to come, in the form in which the
library's facts on a link's run are
stated: A RECORD OF DATA: no program is run at it. es: the plan's entries that are still to come
(the facts count them; nothing
reads them). -/
def ctxOf (es : List Fmt.Entry) (d : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) : Ctx :=
  { ch :=
      { dry := false, firstTree := 0, samples := 1, entries := es, left := rs, opened := cols,
        roots := d.roots }
    st := d.st, book := d.book }

/-- The link's two last blocks: the proximity test and the chain's end. -/
def tailOf (P : P15) : List (Block St Unit) :=
  [testBlock P, chainEnd 1 7 false ((blocksOr P ++ [testBlock P]).flatMap (·.rounds)) fun d =>
    untestedL d.st]

/-- **K15's law, (L2) «hands on», at the fold**: the statement. -/
def HandsOnFold : Prop :=
  ∀ (P : P15) (es5 es : List Fmt.Entry) (d d' : St) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn),
    P.set.samples = 1 → entries P = some es5 → d.loc.key0.item = 0 → d.loc.key1.item = 1 →
    linkOk d.st.codes P.S 1 = true →
    foldBlocks 0 (frontBlock P :: blocksOr P) d rs cols = .ok (d', rest, cols') →
    ∃ X D, LinkRanR P.S d.loc.key0 d.loc.key1 (ctxOf es d rs cols) (ctxOf (es.drop 5) d' rest cols')
        X D ∧
      X.group = d'.loc.g ∧ X.mask = d'.loc.firstMask

/-- **K15's law, (L2) «hands on», at the link's decision itself**: the statement. WHERE (descOf P
plan ok).run SAYS YES ON A VIEW, the
library's record of facts on a link's five rounds holds between the first carried record and some
record d5; and from d5 the
format's fold over the link's two last blocks (the proximity test; the chain's end) says yes on what
is left, with nothing left
over; AND WHAT THE DECISION HAS ASKED BESIDE IS HANDED ON (the
library's head_claimR asks the items; whoever reads words as
field elements asks viewWordsBelowPrime; whoever prices the rounds asks planOk): the keys' items are 0 and 1;
every word of the view is below the prime; the tests on the plan have passed. ONE PREMISE IS LEFT:
one answer to a sample (public). (Not a premise: every
position drawn in round 3 is below 2 ^ logN: roundsFit
asks it, so the fold's yes gives it.) -/
def HandsOnRun : Prop :=
  ∀ (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (es : List Fmt.Entry)
      (x : TableKey × TableKey) (v : Fmt.View),
    P.set.samples = 1 → (descOf P plan ok).run x v = true →
    ∃ X D d5 rest cols' d', LinkRanR P.S x.1 x.2 (ctxOf es (first P.codes x) v.rounds v.opened)
        (ctxOf (es.drop 5) d5 rest cols') X D ∧
      X.group = d5.loc.g ∧ X.mask = d5.loc.firstMask ∧
      foldBlocks 0 (tailOf P) d5 rest cols' = .ok (d', [], []) ∧
      x.1.item = 0 ∧ x.2.item = 1 ∧ VerifiableInference.Desc.viewWordsBelowPrime v = true ∧
          (descOf P plan ok).planOk = true

/-- **The same at linkDesc, the link as it was first described**: the statement.
VerifierAndGoals.theDescription does not run that text; linkDescV_yes (Johnson/Desc/K15/SendOwnPaid.lean) carries a yes of linkDescV
(Johnson/Desc/Link/LinkDesc.lean) to it, one way. c: the planner's record of the three public files. -/
def HandsOnLink : Prop :=
  ∀ (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound) (es : List Fmt.Entry)
      (x : TableKey × TableKey) (v : Fmt.View),
    (p15Of c).set.samples = 1 → (linkDesc c plan).run x v = true →
    ∃ X D d5 rest cols' d', LinkRanR (p15Of c).S x.1 x.2
        (ctxOf es (first (p15Of c).codes x) v.rounds v.opened)
        (ctxOf (es.drop 5) d5 rest cols') X D ∧
      X.group = d5.loc.g ∧ X.mask = d5.loc.firstMask ∧
      foldBlocks 0 (tailOf (p15Of c)) d5 rest cols' = .ok (d', [], []) ∧
      x.1.item = 0 ∧ x.2.item = 1 ∧ VerifiableInference.Desc.viewWordsBelowPrime v = true ∧
          (linkDesc c plan).planOk = true

end Desc.K15

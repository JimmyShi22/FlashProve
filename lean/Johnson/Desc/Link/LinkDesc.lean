-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkDesc.lean: THE ENTRY FILE's ONE CHAIN (THE LINK) AS A DESCRIPTION IN BLOCKS.
Definitions with code; no theorem.

EIGHT BLOCKS AT ⟨1, none, 0 … 7⟩:
  0 the link's front        no round; on the plan: the public shape's conditions
  1 LINK point              K15   1 round
  2 send o_0, o_1           K1's OWN BLOCK (Johnson/Desc/K1/Own.lean: sendOwn), seated by
  Block.inside; 2 rounds: one tree, its tenants the two folds (and the test's first mask, where
  masks go ahead)
  3 (rec_gamma), twice      K15   no round
  4 LINK                    K15   1 round: TWO STORED TABLES are read, the draws cut in two
  5 LINK phi                K15   1 round: (eq_phi)
  6 the proximity test      K12's own block (proximityTestKind, Johnson/Desc/K12/Frame.lean; its parts joined in
  Johnson/Desc/K12/JoinGuarded.lean), seated by Block.inside; its
                            numbers OFF THE PLANNER's SIZED RECORD OF THE LINK: no entry and no
                            declared round goes in
  7 the end of chain 1      the chains' ends' one text (Johnson/Desc/ChainEnd.lean),
  unsealed
ONE TEXT: the sending is the kind K1's own block; the names bear the
word link (linkBlocksBeforeTest · linkProtocolChain · linkDescriptionAt · linkDescV).
The other text, whose sending calls the plain ground's sendP, is seated, run and walked nowhere: it
stands as a middle term inside the laws' proofs (Johnson/Desc/Link/LinkDescWithGroundSend.lean), and nothing on
this page names it.
Over Johnson/Desc/Block.lean: K15's four blocks
bear their kind's name; every Block literal writes claims and after; the plan
that is handed in is the plan's declared rounds, whole.
  P15 | p15Of c   the place's public parameters, out of the planner's chains
  entries         K15's and K1's rounds as entries of the plan, whole: priced as the planner's own
  list prices them
                  (OnBytes/Params/PlanListsChains.lean: linkBlockList: closeness · sample · — ·
                  query · field; the scope «once»)
  numsOf          the test's place's numbers, in the form of PlaceNums (PlaceOfPlan.lean)
  linkDescriptionAt P plan ok the description at any parameters
  linkDescV c plan **THE DESCRIPTION**: OneChainFileDescription (TableKey × TableKey): the instance: the first
  table's key, the copy's
THE TEST ON THE INSTANCE: every word of either key is below the prime; the first names item 0, the
copy item 1.
fin asks nothing: the chain's end is a block.
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Link.OneChainFileDescription
import Johnson.Desc.MadeOk
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K15.K15
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K1.Own
import Johnson.Desc.K12.Join
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14 (Round Says)
open VerifiableInference.Desc (Block Chain Place KindName OneChainFileDescription roundlessBlock named)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Ground (Clauses)

/-- **The place's public parameters.** -/
structure P15 where
  set : Setting
  codes : Codes
  S : LinkShape
  /-- the proximity test's stages as the planner has sized them -/
  stages : List StageSize

def P15.par (P : P15) : Par15 := { samples := P.set.samples, S := P.S }

/-- What the one message holds. -/
def sent (P : P15) : Array OracleNotice := linkMessage P.S P.set.samples

/-- **The kind K1's parameters at the link's one sending.** An entry file is the committer's: the
scope is «once». -/
def parK1 (P : P15) : VerifiableInference.Desc.K1.Par :=
  { place := ⟨1, none, 2, .K1⟩, codes := P.codes, gp := P.par.gp, work := P.set.workOf .sample .once
    parts := [("o_0, o_1 and, where masks go ahead, the test's first mask", sent P)] }

/-- An entry of the plan for a round of K15's own, whole: the prover sends nothing in it. why: by
which argument it is priced. -/
def entryOf (P : P15) (r : Round) (why : ErrorKind) : Fmt.Entry :=
  { name := r.name, work := P.set.workOf why .once, drawE := r.elems, drawNZ := r.nonzero, poss :=
      r.locations
    logN := r.logN }

/-- The five rounds in front of the test as entries of the plan: K15's "LINK point" · THE KIND K1's
TWO, AS THAT KIND's OWN PAGE SAYS THEM · K15's "LINK" and "LINK phi". -/
def fiveOf (P : P15) : List Fmt.Entry :=
  match rounds P.par with
  | [a, b, c] =>
    [entryOf P a .closeness, VerifiableInference.Desc.K1.seedEntry (parK1 P),
     VerifiableInference.Desc.K1.answerEntry (parK1 P), entryOf P b .query, entryOf P c .field]
  | _ => []

/-- The same; nothing where the one message's trees cannot be laid (K1's page says no root there,
and its test on the plan refuses). -/
def entries (P : P15) : Option (List Fmt.Entry) :=
  if (layTrees P.codes (sent P)).isSome then some (fiveOf P) else none

/-- A refusal under the name of the first clause that is false. -/
def why (l : Clauses) (x : Option St) : Except String St :=
  match x with
  | some d => .ok d
  | none => .error (((l.find? (!·.2)).map (·.1)).getD "a part called by name")

/-- **The sending of o_0 and o_1: the kind K1's own block** (Johnson/Desc/K1/Own.lean: sendOwn),
laid at the link's record by Block.inside, as Johnson/Desc/K14/Blocks.lean lays it (sendAt).
enter reads the statement, the book of
trees, the roots received, the columns not yet read, and says that no count of claims is owed (no
round in front of it counts a batched row: K15's "LINK point" alone stands there); leave writes
these four back, and what K15 notes of the
new messages' numbers (`behind`). The tenants' groups are told here. -/
def sendK1 (P : P15) : Block St Unit :=
  let own : Block (VerifiableInference.Desc.K1.Owing (DState (Array Nat))) Unit :=
    VerifiableInference.Desc.K1.sendOwn (parK1 P)
  let b := Block.inside
    (fun d : St => .ok { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                                 opened := d.opened, loc := #[] } })
    own
    (fun d t => named "the sending's numbers are not those that the kind notes"
      (behind P.par { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                             opened := t.held.opened } t.held.loc))
  { b with
    name := "send o_0, o_1"
    oracles := [Desc.K14.oraclesOf P.codes (sent P) ([[0], [0]] ++ if P.S.masksAhead then [[]] else
        []), []] }

/-- **The five blocks in front of the test**; nothing where the rounds cannot be said. G is the
chain's group 0; the one
tree is the chain's message 0. -/
def linkBlocksBeforeTest (P : P15) : Option (List (Block St Unit)) := do
  let es ← entries P
  let p := P.par
  let plain (n : String) (i : Nat) (kind : KindName) (first k : Nat)
      (oracles : List (List VerifiableInference.Desc.Oracle)) (before : List (Nat × Nat))
          (l : St → Clauses)
      (f : St → List Fmt.RoundView → Option St) : Block St Unit :=
    { name := n, place := ⟨1, none, i, kind⟩, planOk := true
      rounds := ((es.drop first).take k).map fun e => { entry := e }
      oracles := oracles, before := before, decide := fun d rs _ => why (l d) (f d rs)
      claims := [], after := [] }
  pure
    [plain "LINK point" 1 .K15 0 1 [[]] [] (fun _ => []) (point p),
     sendK1 P,
     plain "(rec_gamma), twice" 3 .K15 0 0 [] [] (fun d => laysRecL p d.loc) (laysRec p),
     { name := "LINK", place := ⟨1, none, 4, .K15⟩, planOk := true
       rounds := ((es.drop 3).take 1).map fun e => { entry := e, stored := readsAtLink P.S }
       oracles := [[]], before := [(1, 0)], decide := fun d rs gs => why [] (link p d rs gs)
       claims := [], after := [] },
     plain "LINK phi" 5 .K15 4 1 [[]] [(1, 0)] (fun _ => []) (phi p)]

/-- The five blocks; where the rounds cannot be said, one block that fails its test on the plan. -/
def blocksOrV (P : P15) : List (Block St Unit) :=
  (linkBlocksBeforeTest P).getD
      [{ roundlessBlock "the kind's rounds cannot be said" 1 none 1 .ok with planOk := false }]

/-- A block without a round at the chain's front: on the plan: the public shape's conditions. -/
def frontBlock (P : P15) : Block St Unit :=
  { roundlessBlock "the link's front" 1 none 0 .ok with
      planOk := P.codes.lengthsOk && linkOk P.codes P.S P.set.samples }

/-- **The numbers of the test's place**, off the planner's sized record: the rows that are batched:
for each table its
record's answers and its columns; (eq_phi); the two folds' sample rows. The group's one tree is the
chain's message 0. -/
def numsOf (P : P15) : Option H2U.PlaceNums := do
  let a := P.set.samples
  let l ← layTrees P.codes (sent P)
  guard (l.shapes.size == 1)
  let t ← l.shapes[0]?
  pure
    { chain := 1, start := 5
      nums := { rows := 2 * P.S.table.answers + P.S.columnsFirst + P.S.columnsFurther + 1 + 2 * a
                work := P.set.workOf .query .once, stages := P.stages.map H2U.stageNums
                ownMask := !P.S.masksAhead
                first := [(⟨t.logN, t.mainWidth + t.maskWidth, false, 0⟩, .own 0)], free := 1,
                    firstTree := 0 }
      idx := P.S.test.map fun s => (s.code, s.maskCode), firstGroup := 1, answers := a
      early := P.S.choice.masksRide }

/-- READS of the carried record: the statement, the book, the roots received, G's number, which
message holds the first
fold's mask. -/
def enter (d : St) : Except String T12 :=
  .ok { st := d.st, book := d.book, roots := d.roots, g := d.loc.g, pass := .nothing, mask :=
        d.loc.firstMask }

/-- WRITES: the first three. -/
def leave (d : St) (t : T12) : Except String St :=
  .ok { d with st := t.st, book := t.book, roots := t.roots }

/-- **The proximity test on G.** -/
def testBlock (P : P15) : Block St Unit :=
  let place : Place := ⟨1, none, 6, .K12⟩
  Block.inside enter (proximityTestKind guardedProximityTestParts (((numsOf P).map (H2U.proximityTestParametersAt place)).getD (H2U.noP12 place)))
      leave

/-- **The chain.** The end is handed the very list that is laid in front of it. -/
def linkProtocolChain (P : P15) : Chain St Unit :=
  let inFront := blocksOrV P ++ [testBlock P]
  { first := frontBlock P, front := [], links := []
    back := inFront, last := chainEnd 1 7 false (inFront.flatMap (·.rounds)) fun d => untestedL d.st }

/-- The state in front of the first round: the codes and the instance's two keys. -/
def first (codes : Codes) (x : TableKey × TableKey) : St :=
  { st := { codes := codes, oracles := #[], groups := #[] }, book := { trees := #[], place := #[] },
    roots := 0, opened := [], loc := { key0 := x.1, key1 := x.2 } }

/-- The test on one key. -/
def okKey (item : Nat) (key : TableKey) : Bool :=
  VerifiableInference.Desc.Own.seedsOk key && VerifiableInference.Desc.Own.recordOk key && key.item
      == item

/-- The parameters out of the planner's chains. -/
def p15Of (c : Model.Verify.Chains) : P15 :=
  let z := c.made.sized
  { set := z.set, codes := z.entryCodes, S := z.link.shape, stages := z.link.linked.stages }

/-- The description at any parameters and any plan's declared rounds. ok: the file's own public test
(`OneChainFileDescription.fileOk`): WITHOUT A DEFAULT:
whoever makes a description says what it is. -/
def linkDescriptionAt (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) : OneChainFileDescription (TableKey × TableKey) :=
  { S := St, Cl := Unit, plan := plan, tableDepth := P.S.table.tree.a, tables := 2, fileOk := ok
    okStart := fun x => okKey 0 x.1 && okKey 1 x.2
    start := first P.codes, chain := linkProtocolChain P, fin := fun _ _ => true }

/-- **The planner's record is of one piece, and the plan that is handed in is the priced plan's**: a
public test, with code. The planner's record c
holds the entry file's chain twice: as it was made (c.made: the sizes, the finished plan with its
rounds' prices) and as it was read back out of the chain's
parameter bytes (c.link: what a reader of an entry file is handed). The description's shape, codes
and setting are c.made's (`p15Of`); the declared rounds
off the plan (declLOf) are made of c.link's; `entryOk` prices c.made's. Asked: the entries of the
plan that is handed in are the priced plan's rounds' · the plan
read back has the priced plan's entries · the shape read back is the made one · so are the codes. -/
def tiesOk (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound) : Bool :=
  decide (plan.map (·.entry) = c.made.entry.plan.rounds) && decide
      (c.link.given.plan.entries = c.made.entry.plan.entries) &&
    decide (c.link.link = c.made.sized.link.shape) && decide
        (c.link.codes = c.made.sized.entryCodes)

/-- **The link's description.** Its own public test: `tiesOk`, and the public test on the prices of
the entry file's finished plan
(`entryOk`, Johnson/Desc/MadeOk.lean: every round holds at the target 128, work counted; the side
conditions; at most 32 bits of work a round). -/
def linkDescV (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound) : OneChainFileDescription
    (TableKey × TableKey) :=
  linkDescriptionAt (p15Of c) plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan)

end Desc.K15

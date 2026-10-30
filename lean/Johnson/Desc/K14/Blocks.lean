-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Blocks.lean: the shared rounds of the IOPP for linear constraints on the encoded
index, as blocks of the format in which a file's protocol is written (Johnson/Desc/Block.lean), and
the proof file's shared chain made of them.

This file holds definitions only; no theorem is stated.

Each block says side by side:
  ROUNDS: the plan's entry whole, made here of the kind's rounds as data and the setting's bits of
    work, not taken from a plan;
  READS: at "LOC" the encoded index, as a stored part;
  FIXED BEFORE THE DRAW: the block that draws a challenge names the messages which any test holds
    against it; they must have been sent, and their samples answered, before that draw: Q: o_u;
    z_fd: o_u, o_omega, o_sp; psi_sh: each instance's own message on the first chain, whose number
    is a parameter: "LIN point" refuses, on the plan, a list without a message; of a message of an
    EARLIER chain the format asks only that it is sent: that the shared chain's draws hang on it is
    the compiler's matter (the chains' seals). A sending names none: its seeds are drawn behind its
    own messages by the order inside the round, and in front of their answers;
  THE TESTS ON THE PLAN ALONE: the block's share (Johnson/Desc/OnPlan/OkShare.lean), a function of
    the place's numbers;
  DECIDES: the functions of Johnson/Desc/K14/Text.lean; no body is written again. A refusal bears
    "not met: " and the name of the first of the place's named clauses that is false, or says
    that a step refuses outside the named tests where none is. What a round holds and draws is not
    asked here: Block.step asks it, of ROUNDS.
    Among the rest it asks that a drawn position is below 2 ^ its entry's logN; "LOC" itself takes a
    drawn location modulo that number, and is no decision without Block.step.

The parameters P14 hold numbers of the place: the setting, who pays for the work, the codes, the
shape, the number of the statement's item that holds the index's root. No entry and no declared
round; and not the key, which is the instance's and is in the carried record from the start (first).

Eight blocks: "LIN point", the sending of o_u, "(rec_gamma)", "LOC", the sending of o_omega and
o_sp, the joinings, "LIN zeta", "SPLIT". The two sendings are the kind K1's own block
(Johnson/Desc/K1/Own.lean: sendOwn), at two sets of its parameters, laid at this chain's state by
Block.inside (sendAt):
  enter reads   the statement, the book of trees, the roots received, the columns not yet read.
  enter says    "no count of claims is owed" (owed := none). This chain's state has no field for
                that debt. The block's test on the plan asks that the entry handed to it as the
                round in front counts no claims. IN THE CHAIN THAT ENTRY IS THIS FILE's OWN MADE
                ONE, whose count is never set: so the test is true there by the making, and what
                ties it to a plan is the file's test that the blocks' rounds are the plan's.
  leave writes  these four back, and what Johnson/Desc/K14/Text.lean notes of the new messages'
                numbers.
  told here     the oracle messages' tenants with the groups that each joins (oraclesOf): o_u one,
                the mask beside it none, o_omega one, o_sp two.
Then the chain: a front block, the eight, the two proximity tests as arguments (another kind's
blocks, at the places 9 and 10), and the closing block, an argument too.

What is assumed. Nothing of the arguments: that the tests' blocks are the proximity test's, and the
last block a chain's end, is the caller's matter. Three blocks have no round (the front block,
"(rec_gamma)", the joinings): no test of the format notices where one of them is left out of the
list.

What is not claimed. That the tenants told here are those that the blocks lay. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Text
import Johnson.Desc.OnPlan.OkFrontC
import Johnson.Desc.K1.Own
import Johnson.Desc.Own.Trees
import Johnson.Desc.Own.KeyTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain Place KindName SymbolComponent roundlessBlock named)
open VerifiableInference.Desc.Ground (Clauses)

/-- An oracle message where it is sent, in the format's record. -/
abbrev Sent : Type := VerifiableInference.Desc.Oracle

/-- **The place's public parameters.** -/
structure P14 where
  set : Setting
  /-- who pays for a round's work -/
  scope : Scope
  codes : Codes
  S : LinShape
  /-- the number, from 0, of the item of the chain's statement that holds the index's root -/
  item : Nat
  /-- the messages of the first chain that must be fixed before psi_sh is drawn (chain, number):
  the instance's own vector, against which the second part holds psi_sh. NO DEFAULT; and "LIN
  point"'s test on the plan refuses an empty list. WHICH messages it must name no test here says -/
  beforePoint : List (Nat × Nat)

/-- What the page's functions read of the parameters. They read no entry, and no key there. -/
def P14.par (P : P14) : Par :=
  { S := P.S, key := {}, samples := P.set.samples, firstTree := 0, entries := [] }

/-- The bytes of a round's message in the plan: an element of E has 24. -/
def Says.bytes : Says → Nat
  | .nothing => 0
  | .scalars n => 24 * n

/-- By which argument each of the kind's own rounds is priced; none: the verifier says nothing, and
the round bears no work. The first: by closeness where the index has a record or the chain is a
key's. -/
def whys (P : P14) : List (Option ErrorKind) :=
  [some (if P.S.fold.index.answers != 0 || P.scope == .once then .closeness else .field),
   some .query, some .field, none]

/-- A round's entry of the plan, whole. -/
def Round.entry (P : P14) (r : Round) (why : Option ErrorKind) : Fmt.Entry :=
  { name := r.name, work := (why.map (P.set.workOf · P.scope)).getD 0, msg := r.prover.bytes,
    drawE := r.elems, drawNZ := r.nonzero, poss := r.locations, logN := r.logN }

/-- The kind's own rounds as entries of the plan, in order: "LIN point", "LOC", "LIN zeta", and
"SPLIT" where there is a split. -/
def entries (P : P14) : List Fmt.Entry :=
  ((rounds P.S).zip (whys P)).map fun x => x.1.entry P x.2

/-- K1's parameters at one of the chain's two sendings. -/
def parK1 (P : P14) (piece : Nat) (part : String) (sent : Array OracleNotice) :
    VerifiableInference.Desc.K1.Par :=
  { place := ⟨2, none, piece, .K1⟩, codes := P.codes, gp := P.par.toGPar
    work := P.set.workOf .sample P.scope, parts := [(part, sent)] }

/-- For each root of a sending the oracle message beneath it: its log-length, the words of a symbol,
and who shares a symbol, in the order of sending. groups: for each message of the sending the groups
that it joins. -/
def oraclesOf (codes : Codes) (sent : Array OracleNotice) (groups : List (List Nat)) :
    List Sent :=
  match VerifiableInference.Desc.Own.treesMade codes sent with
  | none => []
  | some l =>
    l.shapes.toList.zipIdx.map fun (t, i) =>
      { logLength := t.logN, words := t.mainWidth + t.maskWidth
        tenants := ((sent.toList.zip groups).zipIdx.filter fun x => l.tree[x.2]? == some i).map
          fun x =>
            let s := x.1.1.shape
            { main := s.mainRows * s.mainDeg, mask := s.maskRows * 3, degree := s.mainDeg
              sampled := s.answers != 0, groups := x.1.2 } }

/-- A refusal under the name of the first clause that is false, with "not met: " in front: a
clause's name says what is asked, not what was found. -/
def why (l : Clauses) (x : Option St) : Except String St :=
  match x with
  | some d => .ok d
  | none => .error (((l.find? (!·.2)).map ("not met: " ++ ·.1)).getD
      "a step of this place refuses, outside its named tests")

/-- **A sending at this chain's state**: K1's own block at the parameters Q. n: the place's name in
the print; inFront: the entry of the round in front; groups: for each message the groups that it
joins; behind: what this kind notes of the new messages' numbers. -/
def sendAt (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : St → Array Nat → Option St) : Block St Unit :=
  let own : Block (VerifiableInference.Desc.K1.Owing (DState (Array Nat))) Unit :=
    VerifiableInference.Desc.K1.sendOwn Q
  let b := Block.inside
    (fun d : St => .ok { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                                 opened := d.opened, loc := #[] } })
    own
    (fun d t => named "the messages just sent are not those that this place records"
      (behind { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                       opened := t.held.opened } t.held.loc))
  let ok := b.planOk && OkD.At.ofBlock n P.codes P.S && inFront.all (·.rows == 0)
  { b with name := n, planOk := ok, oracles := [oraclesOf P.codes Q.sent groups, []] }

/-- **The eight blocks**, in order; nothing where what goes out with o_u cannot be said. G_u is the
chain's group 0, G_omega its group 1; o_u's tree is the chain's message 0, o_omega's 1, o_sp's 2. -/
def blocks (P : P14) : Option (List (Block St Unit)) := do
  let es := entries P
  let p := P.par
  let plain (n : String) (i : Nat) (kind : KindName) (first k : Nat) (oracles : List (List Sent))
      (before : List (Nat × Nat)) (l : St → Clauses) (f : St → List Fmt.RoundView → Option St) :
      Block St Unit :=
    { name := n, place := ⟨2, none, i, kind⟩, planOk := OkD.At.ofBlock n P.codes P.S
      rounds := ((es.drop first).take k).map fun e => { entry := e }
      oracles := oracles, before := before, decide := fun d rs _ => why (l d) (f d rs)
      claims := [], after := [] }
  let split1 := if P.S.sharedSplitNeeded then 1 else 0
  let both := if P.S.sharedSplitNeeded then [(2, 1), (2, 2)] else [(2, 1)]
  pure
    [{ plain "LIN point" 1 .K14 0 1 [[]] P.beforePoint (linPointL p) (linPoint p) with
       planOk := OkD.At.ofBlock "LIN point" P.codes P.S && !P.beforePoint.isEmpty },
     sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" (← withU P.S)) es[0]? [[0], []]
       (behindU p),
     plain "(rec_gamma)" 3 .K14 0 0 [] [] (fun d => laysRecL p d.loc) (laysRec p),
     { name := "LOC", place := ⟨2, none, 4, .K14⟩, planOk := OkD.At.ofBlock "LOC" P.codes P.S
       rounds := ((es.drop 1).take 1).map fun e =>
         { entry := e, stored := [readsAtLoc P.S.fold P.item] }
       oracles := [[]], before := [(2, 0)], decide := fun d rs gs => why [] (loc p d rs gs)
       claims := [], after := [] },
     sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) es[1]? [[1], [1, 0]]
       (behindOmega p),
     plain "joins" 6 .K14 0 0 [] [] joinsL (joins p),
     plain "LIN zeta" 7 .K14 2 1 [[]] ((2, 0) :: both) (fun _ => []) linZeta,
     plain "SPLIT" 8 .K14 3 split1 (List.replicate split1 []) (both.drop 1)
       (fun d => foldL p.S d.loc ++
         (((fold p.S d.loc (linLayOmega d.st.codes p.S)).map (splitL d)).getD []))
       (split p)]

/-- The eight blocks; where the kind's rounds cannot be said, one block that fails its test on the
plan: so a file's description can be made at every parameter, and refuses there. -/
def blocksOr (P : P14) : List (Block St Unit) :=
  (blocks P).getD
    [{ roundlessBlock "the shared chain's rounds cannot be made from the plan" 2 none 1 .ok with
        planOk := false }]

/-- A block without a round at the shared chain's front: its test on the plan is the shared chain's
front's share, at the planner's chains. -/
def frontBlock (c : Model.Verify.Chains) : Block St Unit :=
  { roundlessBlock "the shared chain's front" 2 none 0 .ok with planOk := OkD.AtC.front2 c }

/-- The state in front of the first round: the codes and the instance's key; no message, no group,
no tree. -/
def first (codes : Codes) (key : TableKey) : St :=
  { st := { codes := codes, oracles := #[], groups := #[] }, book := { trees := #[], place := #[] },
    roots := 0, opened := [], loc := { key := key } }

/-- THE TEST ON THE INSTANCE: every word of the key is below the field's prime, the seeds' and the
record's; and the key names the item that READS names. -/
def okKey (P : P14) (key : TableKey) : Bool :=
  VerifiableInference.Desc.Own.seedsOk key && VerifiableInference.Desc.Own.recordOk key &&
    key.item == P.item

/-- Every group's test has begun, and every sampled message is in a group. -/
def tested (d : St) : Bool :=
  d.st.groups.all (·.inRun) && d.st.oracles.all fun x => !x.sampled || !x.groups.isEmpty

/-- The place's parameters out of the planner's chains. The item: IN A PROOF FILE's SHARED CHAIN THE
STATEMENT's ITEM 0 HOLDS THE INDEX's ROOT: a written constant of the format (the program
`verify-on-bytes` lays the same 0 where it makes the key: OnBytes/Proof/Tail.lean). -/
def p14Of (c : Model.Verify.Chains) (beforePoint : List (Nat × Nat)) : P14 :=
  let z := c.made.sized.proof
  { set := z.set, scope := if z.batch.lines.oneTime then .once else .shared, codes := z.codes,
    S := z.batch.shape, item := 0, beforePoint := beforePoint }

/-- **The shared chain.** tests: the proximity test on G_u and, where the shape splits, the one on
G_omega: another kind's blocks, at the places ⟨2, none, 9⟩ and ⟨2, none, 10⟩. last: the chain's
closing block, at ⟨2, none, 11⟩, AS A FUNCTION OF THE BLOCKS THAT ARE LAID IN FRONT OF IT: so what
it reads of them is read off the very list that is laid, by construction, and is typed by nobody.
The one general text for a chain's end is another file's. -/
def chainOf (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) : Chain St Unit :=
  let inFront := blocksOr P ++ tests
  { first := frontBlock c, front := [], links := [], back := inFront, last := last inFront }

/-- What a later chain reads of this chain's end, as a `Proof.SharedEnd`; nothing unless
all is tested. -/
def ended (d : St) : Option Proof.SharedEnd :=
  let l := d.loc
  if tested d then
    some { st := d.st, book := d.book
           lin := { psi := l.psiSh, zeta := l.zFd, u := l.oU, omega := l.oOmega, split := l.oSp,
                    groupU := l.gU, groupOmega := l.gOmega, mask := l.firstMask } }
  else none

end Desc.K14

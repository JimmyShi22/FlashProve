-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/ThirdAsk.lean: what the files lean/Ask/KeyThirdChainSmall.lean and
KeyThirdChainFull.lean share: they evaluate `third` (Johnson/KeyRun/Third.lean), a check of a key
file's third chain, on a stored example's key file and on changed copies of what was read from it.
Definitions with code. Nothing is evaluated here. No soundness: a test.

For the words chain, view, plan, program, block and dry run see the head of
Johnson/KeyRun/ThirdAtClaim.lean.
Where each input of `run` comes from.
  - From disk: the three public parameter files and the key file of one stored example.
  - c: bytes for the place of the public files' digest in the plan. `third` is asked at the key
    chains of `OnBytes.Tie.plannedAt` at c, which hold c where the digest stood; by `third_atCfg`
    (Johnson/KeyRun/ThirdNoDigest.lean) it does not read these bytes. `run` refuses a c that is the
    digest. Whether a plan is made at all still hangs on a hash: `publicOf`
    (OnBytes/Model/VerifyPublic.lean) holds the public tables against the parameter file by the
    format's second hash function, a fixed function in front of the planner, and refuses by it.
  - lists: for each of the three chains the written rounds (entry, kind, items, openings, stored
    tables) under which the reader reads the chain. `run` tests that their entries are the plan's
    rounds, and refuses with that reason if they are not. Kind, items, openings and stored tables
    are in no plan: they are the caller's word.
The reader. `readThree` is the text of the program's `Key.readKey` (OnBytes/Key/File.lean) and
`Proof.readTail` (OnBytes/Proof/Tail.lean) with the lists as an argument, where these two make them
by dry runs of the program's blocks. Each chain is read by the program's strict reader, whose
refusals are of the kinds description, form, work, listed positions, opening and one value at a
vertex (OnBytes/Proof/Reading.lean). It takes the key chains of `Model.Verify.planned`, with the
true digest, which the file's hash chains start from: that stands outside `third`. In a third
chain's list the three trees that are taken over from the first two chains stand under made-up
names; `realNames` puts in their place the roots and starts with which these chains were read. All
else that `readThree` calls is the program's own. The two tests that `Key.check` makes before it
reads (the field; `Key.admitted`) are not made by `run`; `third` asks both.
The rows. `rows` lists the questions: the arguments as read (row 0), and changes in them, most of
one thing. Every change is made in memory, behind the reader. Where a value is changed, 1 is added
to one machine word. Rows 1 to 31, 34, 35 and 90 to 98 change a view; the others behind row 0 change
the plan. At these the tests on the plan that say no are named, and `dec₃`, the part of `third` on
the views, is asked by itself as well: where it says yes, the tests on the plan alone stand between
the changed plan and a yes.

Limits.
  - `readThree`, the rows and `third` run no block of the program: no dry run, no call of
    `Key.readKey`. The planner is the program's own; what it returns holds the proof file's links,
    whose checks are blocks, and these are not run. These files hold no comparison of `third`, of
    its claim or of these views with the program's own run.
  - Since nothing is changed in the file's bytes, hashes, proof of work and openings are not tried
    by any row. No row aims at a word at or above the prime. A no shows that the changed
    value reaches a test, not that a test of its own guards it.
  - Each of the ten tests on the plan has a row at which it alone says no and `dec₃` says yes
    (lean/Ask/KeyThirdChainSmall.lean holds it). Not every clause of a test has such a row: none has
    "more than one column" in the third, W's mask code in the fifth, the mask codes in the tenth.
  - Of the 24 refusals of `decWith` the lists of lean/Ask/ expect eleven by their text. By reading,
    no change of `third`'s arguments reaches six; the others have no row that expects them.
  - An evaluation is no theorem. All that the head of Johnson/KeyRun/Third.lean says that `third` is
    not.
The program does not import this file.


-/
import Johnson.KeyRun.Third
import Johnson.KeyRun.ThirdPieces
import OnBytes.Key.File
import OnBytes.Model.Verify
import OnBytes.Three.Data
import OnBytes.Tie.ChainsAtCfg

set_option autoImplicit false

namespace Johnson.KeyRun.ThirdAsk

open OnBytes OnBytes.Proof OnBytes.Params Johnson.KeyRun.Third

/-! ## The reader under given lists -/

/-- A third chain's list with the file's own roots and starts for the made-up names. first, shared:
the first two chains as read. -/
def realNames (first shared : ChainRead) (R : Rounds) : Rounds :=
  R.map fun x => ({ x.1 with opens := x.1.opens.map fun o =>
    (o.1, match Three.named 2 o.2 with
      | some (0, n) => treesOf first n
      | some (1, n) => treesOf shared n
      | _ => o.2) }, x.2)

/-- Reads the three chains of a key file under the lists K. j: the place of the first byte after the
record's answers. It refuses a file with bytes left over. -/
def readThree (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    (K : Rounds × Rounds × Rounds) : OnBytes.Proof.Reading TailRead := do
  let p := k.oneTime
  let spec ← need "one-time-chain-parameters" (p.describe table K.1)
  let first ← readNamed "one-time-chain-" spec file j
  let tp := Key.tailPublic k table
  let g := tp.shared.given
  let seal1 ← need "first-chain-seal" first.seal
  let place ← need "place" (readPlace tp.binding g.cfg seal1 file first.next)
  let key ← need "table-record" (tableKey g.plan.field g.cfg tp.lin.fold.index tp.table 0)
  let spec2 ← need "shared-chain-parameters" (tp.shared.describe tp.lab₂ tp.table place.root K.2.1)
  let shared ← readNamed "shared-chain-" spec2 file place.next
  let seal2 ← need "shared-chain-seal" shared.seal
  let spec3 ← need "second-chain-parameters"
    (tp.second.describe tp.lab₃ seal1 seal2 (realNames first shared K.2.2) (secondFirstTree first))
  let second ← readNamed "second-chain-" spec3 file shared.next
  if second.next != file.size then throw "bytes-left-over"
  pure ⟨first, place, key, shared, second⟩

/-! ## Changes of one thing in a view -/

/-- 1 added to the first word of an element. -/
def bump3 (x : UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 := (x.1 + 1, x.2.1, x.2.2)

/-- The view with f applied to its round number i. -/
def onRound (v : Fmt.View) (i : Nat) (f : Fmt.RoundView → Fmt.RoundView) : Fmt.View :=
  { v with rounds := v.rounds.zipIdx.map fun r => if r.2 == i then f r.1 else r.1 }

/-- The first element that round i draws is changed. -/
def turnDrawn (i : Nat) (v : Fmt.View) : Fmt.View :=
  onRound v i fun r => { r with drawn := { r.drawn with elems :=
    match r.drawn.elems with
    | a :: t => bump3 a :: t
    | [] => [] } }

/-- The first item that is an element or an answer is changed. -/
def bumpFirst : List Fmt.ItemValue → List Fmt.ItemValue
  | [] => []
  | .e x :: l => .e (bump3 x) :: l
  | .answer x :: l => .answer (bump3 x) :: l
  | g :: l => g :: bumpFirst l

/-- The first element or answer that the prover sent in round i is changed. -/
def turnSent (i : Nat) (v : Fmt.View) : Fmt.View :=
  onRound v i fun r => { r with vals := bumpFirst r.vals }

/-- Opened columns, cut into runs of one key and one width, in their order. Two trees' columns that
follow each other under one key and at one width would count as one run. -/
def runsOf (l : List Ent) : List (List Ent) :=
  (l.foldl (fun (acc : List (List Ent)) e =>
    match acc with
    | (f :: r) :: more =>
      if f.1 == e.1 && f.2.2.length == e.2.2.length then (e :: f :: r) :: more
      else [e] :: (f :: r) :: more
    | _ => [e] :: acc) []).reverse.map List.reverse

/-- 1 is added to word number j of the first column of run number n of the opened columns. -/
def turnCol (n j : Nat) (v : Fmt.View) : Fmt.View :=
  let runs := runsOf v.opened
  { v with opened := (runs.zipIdx.flatMap fun r =>
      if r.2 == n then
        match r.1 with
        | o :: t => (o.1, o.2.1, o.2.2.zipIdx.map fun w => if w.2 == j then w.1 + 1 else w.1) :: t
        | [] => []
      else r.1) }

/-- 1 is added to the first position that round i draws. -/
def turnPos (i : Nat) (v : Fmt.View) : Fmt.View :=
  onRound v i fun r => { r with drawn := { r.drawn with poss :=
    match r.drawn.poss with
    | a :: t => (a + 1) :: t
    | [] => [] } }

/-- Runs number a and a + 1 of the opened columns are exchanged. -/
def swapRuns (a : Nat) (v : Fmt.View) : Fmt.View :=
  let runs := runsOf v.opened
  { v with opened := (runs.take a ++ (runs.drop (a + 1)).take 1 ++ (runs.drop a).take 1 ++
      runs.drop (a + 2)).flatten }

/-! ## Changes of one thing in the plan -/

/-- The key chains with f applied to the shape of the test on the table, in both chains that hold a
copy of it. -/
def onShape (k : KeyChains) (f : LinShape → LinShape) : KeyChains :=
  { k with oneTime := { k.oneTime with lin := f k.oneTime.lin },
           shared := { k.shared with lin := f k.shared.lin } }

/-- The key chains with f applied to the codes, in both chains that hold a copy of them. -/
def onCodes (k : KeyChains) (f : Codes → Codes) : KeyChains :=
  { k with oneTime := { k.oneTime with codes := f k.oneTime.codes },
           shared := { k.shared with codes := f k.shared.codes } }

/-- The key chains with f applied to the first chain's parameters. -/
def onOneTime (k : KeyChains) (f : OneTime → OneTime) : KeyChains :=
  { k with oneTime := f k.oneTime }

/-- A chain's given values with f applied to its plan. -/
def onPlan (g : Given) (f : Fmt.Plan → Fmt.Plan) : Given := { g with plan := f g.plan }

/-- A chain's given values with f applied to each entry of its plan that is a round. f also gets the
round's number. The entry "RECORD", which is no round, stays. -/
def onEntries (g : Given) (f : Nat → Fmt.Entry → Fmt.Entry) : Given :=
  onPlan g fun p => { p with entries :=
    (p.entries.foldl (fun (acc : Nat × List Fmt.Entry) e =>
      if e.name == "RECORD" then (acc.1, e :: acc.2)
      else (acc.1 + 1, f acc.1 e :: acc.2)) (0, [])).2.reverse }

/-- The key chains with f applied to the three plans. f also gets the chain's number, from 1. -/
def onPlans (k : KeyChains) (f : Nat → Fmt.Plan → Fmt.Plan) : KeyChains :=
  ⟨{ k.oneTime with given := onPlan k.oneTime.given (f 1) },
    { k.shared with given := onPlan k.shared.given (f 2) },
    { k.second with given := onPlan k.second.given (f 3) }⟩

/-- f applied to the plan of chain number i alone. -/
def inChain (i : Nat) (f : Fmt.Plan → Fmt.Plan) : Nat → Fmt.Plan → Fmt.Plan :=
  fun j p => if j == i then f p else p

/-- The key chains with f applied to each entry of the first chain's plan. -/
def onFirst (k : KeyChains) (f : Nat → Fmt.Entry → Fmt.Entry) : KeyChains :=
  { k with oneTime := { k.oneTime with given := onEntries k.oneTime.given f } }

/-- The same for the second chain's plan. -/
def onSecond (k : KeyChains) (f : Nat → Fmt.Entry → Fmt.Entry) : KeyChains :=
  { k with shared := { k.shared with given := onEntries k.shared.given f } }

/-- The same for the third chain's plan. -/
def onThird (k : KeyChains) (f : Nat → Fmt.Entry → Fmt.Entry) : KeyChains :=
  { k with second := { k.second with given := onEntries k.second.given f } }

/-- f applied to entry number i alone. -/
def atEntry (i : Nat) (f : Fmt.Entry → Fmt.Entry) : Nat → Fmt.Entry → Fmt.Entry :=
  fun j e => if j == i then f e else e

/-- f applied to the entries of one name. -/
def atName (name : String) (f : Fmt.Entry → Fmt.Entry) : Nat → Fmt.Entry → Fmt.Entry :=
  fun _ e => if e.name == name then f e else e

/-- f applied to the first element of a list. -/
def onHead {α : Type} (f : α → α) : List α → List α
  | a :: l => f a :: l
  | [] => []

/-- f applied to the last element of a list. -/
def onLast {α : Type} (f : α → α) (l : List α) : List α := (onHead f l.reverse).reverse

/-! ## The rows -/

/-- The arguments of one question. -/
structure Asked where
  k : KeyChains
  /-- the first chain's view without its sealing round, as `decide3` takes it
  (OnBytes/Maker/Decide3.lean) -/
  v₁ : Fmt.View
  v₂ : Fmt.View
  v₃ : Fmt.View

def Asked.answer (x : Asked) : Bool := third x.k x.v₁ x.v₂ x.v₃

/-- The answer of the test on the views by itself. -/
def Asked.alone (x : Asked) : Bool := dec₃ x.k x.v₁ x.v₂ x.v₃

/-- The first piece of `dec₃`, told in pieces, that says no, with its note; "none" if all say
yes. -/
def Asked.aloneNo (x : Asked) : String :=
  match FirstClaim.claim₁ x.k.oneTime x.v₁ 0 with
  | none => "no claim is made of the first view"
  | some c =>
    match (staged (pubOf x.k) c x.v₁ x.v₂ x.v₃).find? fun l => !l.ok with
    | some l => l.name ++ (if l.note.isEmpty then "" else " (" ++ l.note ++ ")")
    | none => "none"

/-- The first piece of `third` that says no: a test on the plan, or else a piece of `dec₃`. -/
def Asked.firstNo (x : Asked) : String :=
  match (thirdPublic x.k).find? fun t => !t.2 with
  | some t =>
    let es := (pubOf x.k).e₃
    let ws := wants₃ x.k
    "the plan: " ++ t.1 ++
      (if t.1 != roundsTest then ""
       else if es.length != ws.length then
         s!" (the plan has {es.length} rounds, the test {ws.length})"
       else ((TestPlan.firstMiss ws es 0).map fun m => " (" ++ m ++ ")").getD "")
  | none => x.aloneNo

/-- What two views hold is the same. -/
def sameView (a b : Fmt.View) : Bool :=
  (a.rounds.map fun r => (r.vals, r.drawn)) == (b.rounds.map fun r => (r.vals, r.drawn)) &&
    a.opened == b.opened

/-- What a row can change is the same in both: the three views; both copies of the codes and of the
shape; the index-mask message; the binding tree; the three plans but for their bits of work. A new
row that changes another field must add it here, or it counts as a row that changes nothing. -/
def Asked.same (a b : Asked) : Bool :=
  sameView a.v₁ b.v₁ && sameView a.v₂ b.v₂ && sameView a.v₃ b.v₃ &&
    a.k.oneTime.lin == b.k.oneTime.lin && a.k.shared.lin == b.k.shared.lin &&
    a.k.oneTime.codes == b.k.oneTime.codes && a.k.shared.codes == b.k.shared.codes &&
    a.k.oneTime.indexMasks == b.k.oneTime.indexMasks &&
    a.k.oneTime.binding == b.k.oneTime.binding &&
    [a.k.oneTime.given, a.k.shared.given, a.k.second.given].map
        (fun g => (g.plan.entries, g.plan.samples, g.plan.salt, g.plan.nonce, g.plan.posB,
          g.plan.saved, g.plan.field)) ==
      [b.k.oneTime.given, b.k.shared.given, b.k.second.given].map
        (fun g => (g.plan.entries, g.plan.samples, g.plan.salt, g.plan.nonce, g.plan.posB,
          g.plan.saved, g.plan.field))

/-- One question: its number, what is changed, the answer of `third` that is expected, for a row
that changes the plan the answer of `dec₃` by itself that is expected, and the arguments. -/
structure Row where
  no : Nat
  what : String
  want : Bool
  alone : Option Bool := none
  asked : Unit → Asked

/-- **The rows** at what was read. Row 0: nothing is changed. Rows 6 and 8 change a value of the
first chain that `third` does not use, and expect a yes. Every other row expects a no. A row on the
codes or the shape changes both chains' copies, unless its words name one. -/
def rows (r : Asked) : List Row :=
  let P := pubOf r.k
  let read := FirstClaim.roundsRead r.k.oneTime
  let iB := (named P.e₁ "BAT-sigma").getLastD 0
  let iI := (named P.e₁ "SEND seed").headD 0
  let iW := (named P.e₁ "SEND seed").getLastD 0
  let mid := read.getD (read.length / 4) 0
  let unread := ((List.range r.v₁.rounds.length).find? fun i =>
    4 ≤ i && i != iW && i != iW + 1 && !read.contains i && !(sentAt r.v₁ i).isEmpty).getD 0
  let n₃ := r.v₃.rounds.length
  let runs := (runsOf r.v₃.opened).length
  let iO := (named P.e₂ "SEND seed").getD 1 0
  let iC := ((P.e₃.zipIdx.filter fun e => e.1.poss != 0).map (·.2)).headD 0
  let iL := (named P.e₃ "CS").getLastD 0
  let wW := wordsOf P.S.w
  let far := P.codes.base.size
  let sL := P.S.testOwn.getLast?.getD ⟨far, far, 0, 0⟩
  let kRows : KeyChains :=
    { r.k with shared := { r.k.shared with
        lin := { r.k.shared.lin with matrixRows := r.k.shared.lin.matrixRows - 1 } } }
  let one (f : Fmt.View → Fmt.View) : Unit → Asked := fun _ => { r with v₁ := f r.v₁ }
  let two (f : Fmt.View → Fmt.View) : Unit → Asked := fun _ => { r with v₂ := f r.v₂ }
  let three (f : Fmt.View → Fmt.View) : Unit → Asked := fun _ => { r with v₃ := f r.v₃ }
  let plan (k : KeyChains) : Unit → Asked := fun _ => { r with k := k }
  let withRecord (p : Fmt.Plan) : Fmt.Plan :=
    { p with entries := p.entries ++ [{ name := "RECORD" }] }
  let stages (f : List IoppStage → List IoppStage) : Unit → Asked :=
    plan (onShape r.k fun S => { S with testOwn := f S.testOwn })
  [⟨0, "nothing: the plan and the three views as they were read", true, none, fun _ => r⟩,
   ⟨1, s!"chain 1, round {iB + 2} (a PSC round behind BAT-sigma): the first sent element", false,
      none, one (turnSent (iB + 2))⟩,
   ⟨2, s!"chain 1, round {iB} (BAT-sigma): the drawn element", false, none, one (turnDrawn iB)⟩,
   ⟨3, s!"chain 1, round {iB + 1} (the PSC epsilon behind BAT-sigma): the sent element", false,
      none, one (turnSent (iB + 1))⟩,
   ⟨4, s!"chain 1, round {iB + 3} (a PSC round behind BAT-sigma): the drawn element", false, none,
      one (turnDrawn (iB + 3))⟩,
   ⟨5, s!"chain 1, round {read.headD 0} (the first of which the claim reads a value): the drawn \
      element", false, none, one (turnDrawn (read.headD 0))⟩,
   ⟨6, s!"chain 1, round {mid} (in the last level of a part's key tree): the first sent element, \
      WHICH THE CLAIM DOES NOT USE: A KNOWN LIMIT", true, none, one (turnSent mid)⟩,
   ⟨7, s!"chain 1, round {mid}, the same round: the drawn element", false, none,
      one (turnDrawn mid)⟩,
   ⟨8, s!"chain 1, round {unread}, WHICH THE CHECK DOES NOT READ: A KNOWN LIMIT: the first sent \
      element", true, none, one (turnSent unread)⟩,
   ⟨9, "chain 3, round 0 (BAT): the drawn element", false, none, three (turnDrawn 0)⟩,
   ⟨10, "chain 2, round 0 (LIN point): the shared point's first coordinate", false, none,
      two (turnDrawn 0)⟩,
   ⟨11, s!"chain 1, round {iW} (W's SEND seed): the first drawn element", false, none,
      one (turnDrawn iW)⟩,
   ⟨12, "chain 3, opened columns: word 0 of Omega's first column", false, none,
      three (turnCol 2 0)⟩,
   ⟨13, "chain 3, round 2 (a FOLD round): the first sent element", false, none,
      three (turnSent 2)⟩,
   ⟨14, s!"chain 3, round {n₃ - 1} (BASE): the first sent element", false, none,
      three (turnSent (n₃ - 1))⟩,
   ⟨15, "chain 3, opened columns: word 0 of W's first column", false, none, three (turnCol 1 0)⟩,
   ⟨16, "chain 3, opened columns: word 0 of the index-mask message's first column", false, none,
      three (turnCol 0 0)⟩,
   ⟨17, s!"chain 3, opened columns: word {wW} of W's first column (the fresh mask's first)", false,
      none, three (turnCol 1 wW)⟩,
   ⟨18, "chain 3, opened columns: word 0 of the last tree's first column", false, none,
      three (turnCol (runs - 1) 0)⟩,
   ⟨19, s!"chain 2, round {iO + 1}: Omega's first answer", false, none, two (turnSent (iO + 1))⟩,
   ⟨20, s!"chain 1, round {iI + 1}: the index-mask message's first answer", false, none,
      one (turnSent (iI + 1))⟩,
   ⟨21, s!"chain 3, round {iC} (the first stage's CS): the first drawn position", false, none,
      three (turnPos iC)⟩,
   ⟨22, "chain 3, opened columns: word 0 of the first column of the second stage's tree", false,
      none, three (turnCol 3 0)⟩,
   ⟨23, "chain 3, opened columns: word 0 of the first column of the third stage's tree", false,
      none, three (turnCol 4 0)⟩,
   ⟨24, s!"chain 3, round {iC} (the first stage's CS): the sent answer", false, none,
      three (turnSent iC)⟩,
   ⟨25, s!"chain 3, round {iC - 1} (SEND seed): the first drawn element", false, none,
      three (turnDrawn (iC - 1))⟩,
   ⟨26, s!"chain 1, round {iW + 1}: W's first answer", false, none, one (turnSent (iW + 1))⟩,
   ⟨27, s!"chain 1, round {iI} (the index-mask message's SEND seed): the first drawn element",
      false, none, one (turnDrawn iI)⟩,
   ⟨28, s!"chain 2, round {iO} (Omega's SEND seed): the first drawn element", false, none,
      two (turnDrawn iO)⟩,
   ⟨29, "chain 3, opened columns: W's and Omega's exchanged", false, none, three (swapRuns 1)⟩,
   ⟨30, "chain 3, opened columns: one too many (the last once more, at the end)", false, none,
      three fun v => { v with opened := v.opened ++ v.opened.reverse.take 1 }⟩,
   ⟨31, "chain 3, opened columns: one too few (the first is left out)", false, none,
      three fun v => { v with opened := v.opened.drop 1 }⟩,
   ⟨32, "the plan: the matrix's rows less one, in the second chain's copy of the shape alone",
      false, some false, plan kRows⟩,
   ⟨33, "the plan, chain 3: the number of rows that BAT counts, plus one", false, some false,
      plan (onThird r.k (atName "BAT" fun e => { e with rows := e.rows + 1 }))⟩,
   ⟨34, "chain 3: its last round is left out", false, none,
      three fun v => { v with rounds := v.rounds.dropLast }⟩,
   ⟨35, "chain 3: one round too many (its last once more)", false, none,
      three fun v => { v with rounds := v.rounds ++ v.rounds.reverse.take 1 }⟩,
   ⟨36, "the plan: the last stage names a code that the plan does not have", false, some false,
      stages (onLast fun s => { s with code := far })⟩,
   ⟨37, "the plan: W and Omega name a code that the plan does not have", false, some false,
      plan (onShape r.k fun S =>
        { S with w := { S.w with code := far }, omega := { S.omega with code := far } })⟩,
   ⟨38, s!"the plan, chain 3, round {iC} (the first stage's CS): the range of its positions halved",
      false, some true, plan (onThird r.k (atEntry iC fun e => { e with logN := e.logN - 1 }))⟩,
   ⟨39, "the plan: the first stage names the next mask code", false, some false,
      stages (onHead fun s => { s with maskCode := s.maskCode + 1 })⟩,
   ⟨40, "the plan, chain 3, round 2: another name than FOLD round", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with name := "FOLD" }))⟩,
   ⟨41, s!"the plan, chain 3, round {iC - 1} (SEND seed): one more draw that must not be 0", false,
      some true, plan (onThird r.k (atEntry (iC - 1) fun e => { e with drawNZ := e.drawNZ + 1 }))⟩,
   ⟨42, s!"the plan, chain 3, round {iC} (the first stage's CS): the number of rows that it \
      counts, plus one", false, some true,
      plan (onThird r.k (atEntry iC fun e => { e with rows := e.rows + 1 }))⟩,
   ⟨43, "the plan, chain 3: two answers to a sample", false, some true,
      plan { r.k with second := { r.k.second with given := { r.k.second.given with
        plan := { r.k.second.given.plan with samples := 2 } } } }⟩,
   ⟨44, "the plan: the later stages' masks do not ride with the code switch", false, some true,
      plan (onShape r.k fun S => { S with choice := { S.choice with masksRide := false } })⟩,
   ⟨45, "the plan, chain 3, round 0: another name than BAT", false, some false,
      plan (onThird r.k (atEntry 0 fun e => { e with name := "BATCH" }))⟩,
   ⟨46, "the plan, chain 2, round 0: another name than LIN point", false, some false,
      plan (onSecond r.k (atEntry 0 fun e => { e with name := "POINT" }))⟩,
   ⟨47, "the plan, chain 1: no round is called SEND seed", false, some false,
      plan (onFirst r.k (atName "SEND seed" fun e => { e with name := "SEED" }))⟩,
   ⟨48, "the plan, chain 3: BASE draws no position", false, some false,
      plan (onThird r.k (atName "BASE" fun e => { e with poss := 0 }))⟩,
   ⟨49, "the plan: the first stage has twice as many main rows", false, some false,
      stages (onHead fun s => { s with k := s.k + 1 })⟩,
   ⟨50, "the plan: Omega names another code than W", false, some false,
      plan (onShape r.k fun S => { S with omega := { S.omega with code := S.omega.code + 1 } })⟩,
   ⟨51, "the plan: W's main rows are over the base field", false, some false,
      plan (onShape r.k fun S => { S with w := { S.w with mainDeg := 1 } })⟩,
   ⟨52, "the plan, chain 1: no round is called SEND answer", false, some true,
      plan (onFirst r.k (atName "SEND answer" fun e => { e with name := "ANSWER" }))⟩,
   ⟨53, "the plan: the group of W and Omega names the next mask code", false, some true,
      plan (onShape r.k fun S => { S with ownMaskCode := S.ownMaskCode + 1 })⟩,
   ⟨54, "the plan, chain 1: two answers to a sample", false, some true,
      plan (onOneTime r.k fun o =>
        { o with given := onPlan o.given fun p => { p with samples := 2 } })⟩,
   ⟨55, "the plan: W's class of leaves plus one, in the first chain's copy of the shape alone",
      false, some true,
      plan (onOneTime r.k fun o =>
        { o with lin := { o.lin with wLeafClass := o.lin.wLeafClass + 1 } })⟩,
   ⟨56, "the plan, chain 3: one more byte of salt in a leaf", false, some true,
      plan { r.k with second := { r.k.second with
        given := onPlan r.k.second.given fun p => { p with salt := p.salt + 1 } } }⟩,
   ⟨57, "the plan: the binding tree has two leaves", false, some true,
      plan (onOneTime r.k fun o => { o with binding := { o.binding with logLeaves := 1 } })⟩,
   ⟨58, "the plan: one more main code, which nothing names, with messages of 3 entries", false,
      some true, plan (onCodes r.k fun c => { c with base := c.base.push ⟨2, 3, 0⟩ })⟩,
   ⟨59, "the plan: the group's mask code stands a second time at the end of the list, and the \
      index-mask message names that copy", false, some true,
      plan (onOneTime
        (onCodes r.k fun c => { c with mask := c.mask.push (c.mask.getD P.S.ownMaskCode default) })
        fun o => { o with indexMasks := { o.indexMasks with
          shape := { o.indexMasks.shape with maskCode := P.codes.mask.size } } })⟩,
   ⟨60, "the plan, chain 2: two answers to a sample", false, some true,
      plan { r.k with shared := { r.k.shared with
        given := onPlan r.k.shared.given fun p => { p with samples := 2 } } }⟩,
   ⟨61, "the plan, chain 2: no round is called SEND answer", false, some true,
      plan (onSecond r.k (atName "SEND answer" fun e => { e with name := "ANSWER" }))⟩,
   ⟨62, "the plan: the first fold's mask does not come ahead with W", false, some false,
      plan (onShape r.k fun S => { S with masksAhead := false })⟩,
   ⟨63, "the plan: the last stage's two codes have the length 2^33, and BASE draws from that range",
      false, some true,
      plan (onThird
        (onCodes r.k fun c =>
          { base := c.base.modify sL.code fun x => { x with logN := 33 },
            mask := c.mask.modify sL.maskCode fun x => { x with logN := 33 } })
        (atName "BASE" fun e => { e with logN := 33 }))⟩,
   ⟨64, "the plan: the last stage's main code has the length 2^33, and BASE draws from that range",
      false, some true,
      plan (onThird
        (onCodes r.k fun c =>
          { c with base := c.base.modify sL.code fun x => { x with logN := 33 } })
        (atName "BASE" fun e => { e with logN := 33 }))⟩,
   ⟨65, "the plan, chain 3: the range of BASE's positions halved", false, some true,
      plan (onThird r.k (atName "BASE" fun e => { e with logN := e.logN - 1 }))⟩,
   ⟨66, s!"the plan, chain 3, round {iL} (the last CS): the range of its positions halved", false,
      some true, plan (onThird r.k (atEntry iL fun e => { e with logN := e.logN - 1 }))⟩,
   ⟨67, "the plan: the last stage's mask code is twice as long as its main code", false, some true,
      plan (onCodes r.k fun c => { c with mask := c.mask.modify sL.maskCode fun z =>
        { z with logN := (c.base.getD sL.code default).logN + 1 } })⟩,
   ⟨68, "the plan: one more main code, which nothing names, in the first chain's copy alone", false,
      some true,
      plan (onOneTime r.k fun o =>
        { o with codes := { o.codes with base := o.codes.base.push ⟨2, 2, 0⟩ } })⟩,
   ⟨69, "the plan: the other field in all three plans", false, some true,
      plan (onPlans r.k fun _ p => { p with field := .one })⟩,
   ⟨70, "the plan, chain 3: the other field", false, some true,
      plan (onPlans r.k (inChain 3 fun p => { p with field := .one }))⟩,
   ⟨71, "the plan, chain 2: one more byte of salt in a leaf", false, some true,
      plan (onPlans r.k (inChain 2 fun p => { p with salt := p.salt + 1 }))⟩,
   ⟨72, "the plan, chain 3: one more byte in a nonce", false, some true,
      plan (onPlans r.k (inChain 3 fun p => { p with nonce := p.nonce + 1 }))⟩,
   ⟨73, "the plan, chain 3: one more byte in a listed position", false, some true,
      plan (onPlans r.k (inChain 3 fun p => { p with posB := p.posB + 1 }))⟩,
   ⟨74, "the plan: the word saved is 0 in all three plans", false, some true,
      plan (onPlans r.k fun _ p => { p with saved := 0 })⟩,
   ⟨75, "the plan, chain 3: the word saved is 0", false, some true,
      plan (onPlans r.k (inChain 3 fun p => { p with saved := 0 }))⟩,
   ⟨76, "the plan, chain 2: one more entry, RECORD", false, some true,
      plan (onPlans r.k (inChain 2 withRecord))⟩,
   ⟨77, "the plan, chain 3: one more entry, RECORD", false, some true,
      plan (onPlans r.k (inChain 3 withRecord))⟩,
   ⟨78, "the plan: one more mask code, which nothing names, with messages of 3 entries", false,
      some true, plan (onCodes r.k fun c => { c with mask := c.mask.push ⟨2, 3, 0⟩ })⟩,
   ⟨79, "the plan, chain 3, round 2: the entry counts for two rounds", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with count := e.count + 1 }))⟩,
   ⟨80, "the plan, chain 3, round 2: one more byte in the prover's message", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with msg := e.msg + 1 }))⟩,
   ⟨81, "the plan, chain 3, round 2: one more root", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with roots := e.roots + 1 }))⟩,
   ⟨82, "the plan, chain 3, round 2: one more answer", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with answers := e.answers + 1 }))⟩,
   ⟨83, "the plan, chain 3, round 2: one more drawn element", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with drawE := e.drawE + 1 }))⟩,
   ⟨84, "the plan, chain 3, round 2: one drawn matrix entry", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with trits := e.trits + 1 }))⟩,
   ⟨85, "the plan, chain 3, round 2: a range of positions where none is drawn", false, some true,
      plan (onThird r.k (atEntry 2 fun e => { e with logN := 1 }))⟩,
   ⟨86, "the plan, chain 3, round 2: one drawn position", false, some false,
      plan (onThird r.k (atEntry 2 fun e => { e with poss := 1 }))⟩,
   ⟨87, s!"the plan, chain 1, round {iI + 1}: another name than SEND answer", false, some true,
      plan (onFirst r.k (atEntry (iI + 1) fun e => { e with name := "ANSWER" }))⟩,
   ⟨88, s!"the plan, chain 1, round {iW + 1}: another name than SEND answer", false, some true,
      plan (onFirst r.k (atEntry (iW + 1) fun e => { e with name := "ANSWER" }))⟩,
   ⟨89, "the plan, chain 1: no round is called BAT-sigma", false, some false,
      plan (onFirst r.k (atName "BAT-sigma" fun e => { e with name := "SIGMA" }))⟩,
   ⟨90, "chain 3, round 0 (BAT): one more drawn element", false, none,
      three fun v => onRound v 0 fun x =>
        { x with drawn := { x.drawn with elems := x.drawn.elems ++ x.drawn.elems.take 1 } }⟩,
   ⟨91, s!"chain 1, round {iW} (W's SEND seed): every drawn element is 0", false, none,
      one fun v => onRound v iW fun x =>
        { x with drawn := { x.drawn with elems := x.drawn.elems.map fun _ => (0, 0, 0) } }⟩,
   ⟨92, s!"chain 1, round {iW + 1}: W's answers are left out", false, none,
      one fun v => onRound v (iW + 1) fun x => { x with vals := [] }⟩,
   ⟨93, "chain 3, round 1 (FOLD epsilon): what the prover sent is left out", false, none,
      three fun v => onRound v 1 fun x => { x with vals := [] }⟩,
   ⟨94, "chain 3, round 2 (a FOLD round): one more drawn element", false, none,
      three fun v => onRound v 2 fun x =>
        { x with drawn := { x.drawn with elems := x.drawn.elems ++ x.drawn.elems.take 1 } }⟩,
   ⟨95, s!"chain 3, round {iC - 1} (SEND seed): the last drawn element is left out", false, none,
      three fun v => onRound v (iC - 1) fun x =>
        { x with drawn := { x.drawn with elems := x.drawn.elems.dropLast } }⟩,
   ⟨96, s!"chain 3, round {iC} (the first stage's CS): the sent answer is left out", false, none,
      three fun v => onRound v iC fun x => { x with vals := [] }⟩,
   ⟨97, s!"chain 3, round {n₃ - 2} (BASE lambda): what the prover sent is left out", false, none,
      three fun v => onRound v (n₃ - 2) fun x => { x with vals := [] }⟩,
   ⟨98, s!"chain 3, round {n₃ - 1} (BASE): the last sent element is left out", false, none,
      three fun v => onRound v (n₃ - 1) fun x => { x with vals := x.vals.dropLast }⟩,
   ⟨99, "the plan, chain 1: no round is called LKP", false, some false,
      plan (onFirst r.k (atName "LKP" fun e => { e with name := "LOOKUP" }))⟩]

/-! ## The run -/

/-- A line to the error stream, at once. -/
def say (s : String) : IO Unit := do
  IO.eprintln s
  (← IO.getStderr).flush

def yesNo (b : Bool) : String := if b then "YES" else "no"

def asExpected (b : Bool) : String := if b then "as expected" else "NOT AS EXPECTED"

/-- Prints a first piece that says no. p: a part of the text that is expected. Returns whether the
text holds it. -/
def sayPiece (whose n p : String) : IO Bool := do
  let fits := (n.splitOn p).length != 1
  say s!"  the first piece of {whose} that says no: \"{n}\", {asExpected fits}\
    {if fits then "" else " (expected: \"" ++ p ++ "\")"}"
  pure fits

/-- Which row to ask, and what an asking file expects of it beyond the row's own answers. -/
structure Pick where
  no : Nat
  /-- a part of the text of the first piece of `third` that is expected to say no, then the same for
  `dec₃` by itself; where one is given, the pieces are evaluated as well -/
  pins : List String := []
  /-- at a row that changes the plan: the numbers, from 1, of the tests on the plan that are
  expected to say no -/
  tests : Option (List Nat) := none

/-- Asks one row and prints it. base: the arguments as read. Returns whether all was as expected. A
row behind row 0 that changes nothing is not as expected. -/
def askRow (base : Asked) (x : Row) (w : Pick) : IO Bool := do
  let pins := w.pins
  let t0 ← IO.monoMsNow
  let a := x.asked ()
  let got := a.answer
  say s!"row {x.no}: the check says {yesNo got}, {asExpected (got == x.want)}. Changed: {x.what}"
  let mut ok := got == x.want
  if x.no != 0 && a.same base then
    say "  NOT AS EXPECTED: THIS ROW HAS CHANGED NOTHING"
    ok := false
  if let some p := pins[0]? then
    ok := (← sayPiece "the check" a.firstNo p) && ok
  if let some want := x.alone then
    let no := (thirdPublic a.k).zipIdx.filter (!·.1.2)
    let fits := (w.tests.map (· == no.map (·.2 + 1))).getD true
    let shown := no.map fun t => s!"{t.2 + 1} ({t.1.1})"
    say s!"  the tests on the plan that say no: {shown}\
      {if w.tests.isNone then "" else ", " ++ asExpected fits}"
    ok := ok && fits
    let alone := a.alone
    say s!"  the test on the views by itself says {yesNo alone}, {asExpected (alone == want)}"
    ok := ok && alone == want
    if let some p := pins[1]? then
      ok := (← sayPiece "the test on the views" a.aloneNo p) && ok
  say s!"  this row took {(← IO.monoMsNow) - t0} ms"
  pure ok

/-- **One run.** dir: the stored example's directory. lists, c: see the head. which: the numbers of
the rows to ask, each with what is expected of it (`Pick`). Row 0 is always asked first, with what
the list gives for it, if anything; if it is not as expected the other rows are not asked. It throws
unless every line that holds an expectation is as expected, and at a number that is no row's. -/
def run (dir : System.FilePath) (lists : Rounds × Rounds × Rounds) (c : ByteArray)
    (which : List Pick) : IO Unit := do
  let pol ← IO.FS.readBinFile (dir / "config" / "policy.txt")
  let kl ← IO.FS.readBinFile (dir / "config" / "KL.bin")
  let lay ← IO.FS.readBinFile (dir / "config" / "layout.txt")
  let key ← IO.FS.readBinFile (dir / "ivk" / "key.bin")
  say "No soundness: a test. The check is third (Johnson/KeyRun/Third.lean): it checks the third \
    of a key file's three hash chains, on what a reader has taken out of the file"
  say s!"the stored example: {dir}"
  say s!"read, in bytes: policy.txt {pol.size}; KL.bin {kl.size}; layout.txt {lay.size}; key.bin \
    {key.size}"
  let p₀ ← IO.ofExcept ((OnBytes.Tie.plannedAt pol kl (some lay) c).mapError fun e =>
    IO.userError s!"NO PLAN CAN BE MADE OF THE PUBLIC PARAMETER FILES: {e}")
  let p ← IO.ofExcept ((Model.Verify.planned pol kl (some lay)).mapError fun e =>
    IO.userError s!"NO PLAN CAN BE MADE OF THE PUBLIC PARAMETER FILES: {e}")
  let k₀ := p₀.chains.key
  let held := k₀.oneTime.given.cfg == c && k₀.shared.given.cfg == c && k₀.second.given.cfg == c
  say s!"the key chains at which the check is asked hold this run's {c.size} bytes in the place of \
    the public files' digest: {yesNo held} (YES is expected); these bytes are that digest: \
    {yesNo (p.cfg == c)} (no is expected)"
  unless held && p.cfg != c do
    throw (IO.userError "THE BYTES IN THE DIGEST'S PLACE ARE NOT AS EXPECTED (SEE THE LINE ABOVE)")
  let fit := [lists.1.map (·.1.entry) == k₀.oneTime.given.rounds,
    lists.2.1.map (·.1.entry) == k₀.shared.given.rounds,
    lists.2.2.map (·.1.entry) == k₀.second.given.rounds]
  say s!"the entries of the lists under which the key file is read are the plan's rounds, chain by \
    chain: {fit.map yesNo}"
  unless fit.all id do
    throw (IO.userError "THE LISTS OF ROUNDS ARE NOT THOSE OF THESE PUBLIC PARAMETER FILES")
  let (table, j) ← IO.ofExcept ((Key.readTable p.chains.tableShape p.cfg key).mapError fun e =>
    IO.userError s!"THE READER REFUSES THE KEY FILE'S TABLE: {e.check}")
  let t ← IO.ofExcept ((readThree p.chains.key table key j lists).fromStart.mapError fun e =>
    IO.userError s!"THE READER REFUSES THE KEY FILE: {e}")
  let r : Asked :=
    ⟨k₀, { t.first.view with rounds := t.first.view.rounds.dropLast }, t.shared.view, t.second.view⟩
  say s!"the reader has read the whole key file under the lists. Rounds: {r.v₁.rounds.length} \
    (without the sealing round), {r.v₂.rounds.length}, {r.v₃.rounds.length}; opened columns: \
    {r.v₁.opened.length}, {r.v₂.opened.length}, {r.v₃.opened.length}"
  say s!"of chain 1's rounds the check reads a value in \
    {(FirstClaim.roundsRead k₀.oneTime).length} and in four more (seeds and answers)"
  unless (runsOf r.v₃.opened).length == 2 + k₀.shared.lin.testOwn.length do
    throw (IO.userError
      "TWO TREES OF CHAIN 3 HAVE ONE KEY AND ONE WIDTH: THE ROWS ON COLUMNS CANNOT TELL THEM APART")
  let shownAll := (thirdPublic k₀).zipIdx.map fun t => s!"{t.2 + 1} ({t.1.1})"
  say s!"the check: {(thirdPublic k₀).length} tests on the plan, then the test on the views. The \
    tests on the plan: \
    {shownAll}"
  say "each row: the check's answer, whether it is the expected one, and what was changed in the \
    check's arguments (a value: 1 is added to one machine word)"
  let all := rows r
  let some first := all.head? | throw (IO.userError "there is no row")
  let w₀ := (which.find? fun w => w.no == 0).getD { no := 0 }
  unless ← askRow r first w₀ do
    if w₀.pins.isEmpty then say s!"  the first piece of the check that says no: \"{r.firstNo}\""
    throw (IO.userError "ROW 0 IS NOT AS EXPECTED: THE OTHER ROWS ARE NOT ASKED")
  let mut off : List Nat := []
  let mut n := 1
  for w in which do
    if w.no != 0 then
      let some x := all.find? fun x => x.no == w.no
        | throw (IO.userError s!"THERE IS NO ROW {w.no}")
      n := n + 1
      unless ← askRow r x w do off := off ++ [w.no]
  unless off.isEmpty do throw (IO.userError s!"ROWS NOT AS EXPECTED: {off}")
  say s!"ALL {n} ROWS THAT WERE ASKED, OF {all.length}, ARE AS EXPECTED. THIS IS NO VERIFICATION \
    OF THE KEY FILE: one chain of three was checked, and every change was made in memory after \
    the file was read, so hashes, proof of work and openings were not tried"

end Johnson.KeyRun.ThirdAsk

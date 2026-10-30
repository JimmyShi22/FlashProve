-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/State.lean: THE STATE THAT THE PROOF FILE's FIRST CHAIN CARRIES FROM STEP TO
STEP, AS ONE RECORD S. Definitions with code; one theorem (unmarked_ok). What ties its own texts to
`verify-on-bytes`'s routines stands beside it: Johnson/Desc/First/StateLaws.lean.

What it is for. Each kind's step is typed at a state of its own. To stand in one fold they want one
carried record and, for each kind's state, a way to read it out of that record and to write it back.
COARSE: the fields are `verify-on-bytes`'s own plain records. No field is a function.

THE RECORD. S := what a context of that verifier holds between two rounds, less the rounds
themselves (st . book . roots . rowsOwed . failed) . what the walk over the links holds (check .
out) . "here": where the chain stands, with what is held there alone.
  The opened columns are NO field: the type of a step threads them beside the state.
  The plan's entries and the view's rounds are NO fields: a step is handed its stretch.
  rowsOwed : Option Nat stands for two fields of the channel, last and askedRows: some n: the round
  closed last counts n batched rows and no step has compared that number. IT STANDS AT THE TOP,
  NOT IN A LINK's PART: such a round is also closed where no link is open: in the finish's proximity
  test and in the batching of the rows on the table.
  failed: the name of the first named test on values that has failed, for steps that mark and go on.
  req: WHAT A PLACE READS OF THE INSTANCE HAS ONE HOME: the words of the request file. WHY IT RIDES
  IN S: a description's blocks are not handed the instance: so what a place reads of it rides in the
  state from the start. The tokens (every layers' link reads them) and the two positions are
  FUNCTIONS of the words (tokv, rowR, rowE); so are the covered positions, which the head's link
  reads: of the words and the HEARD reply (covered): NO FIELD. T is told twice, by the plan and by
  the words' number: reqOk compares.

FIELD FOR FIELD AGAINST THE SKELETON (the five records in Johnson/Top/H/Course/): LayLoc = check .
out . LayOwn's five AND slotA; AttLoc = check . out . AttOwn's nine AND slotA; HeadLoc = check . out
. HeadOwn's twelve AND plain, slotA; FinishLoc = check . out . FinOwn's ten (cur and later are one
field, stages) AND D; MemberLoc = check . out . rows . MemOwn's three. Names and types are the
skeleton's, but that a field which a step must have written before it is read is an Option here.
  OTHERWISE THAN THE SKELETON: MemberLoc.rows is no field (one home: two can part). In front of the
  batching's place the rows are the pile, out.pending, and lin is none. THE STEP AT THAT PLACE lays
  lin := some { claim := memberClaim (the one row) }, its four numbers still at their first form:
  ALSO WHERE THE PILE HAS ONE ROW, where there is no batching and the step takes no round: else W's
  sending's quiet step, which fills the four, would meet none. S.rows reads the rows back. LEFT OUT:
  FinishLoc.D : LocTaken. By its own file it is no local of the verifier's text, and its type's
  module (OnBytes/Tie/Pv/Switch/LocRan.lean) stands over Mathlib. Why that bars it: this folder's
  code is compiled to a program without Mathlib, and Johnson/Desc/ is kept free of it by import.
  LEFT OUT: slotA, in all three links. `verify-on-bytes` notes the engine's next free slot at the
  reads' quiet step and lays the note into tl at the lookup on the digits, behind the matrix's draw
  and the digits' sending. No kind's text reads such a note out of S: the lookup on the digits lays
  tl.slotA from the engine as it stands in front of that step (F.next). That the steps between leave
  F.next where it was is a law on these steps, no field: NOT PROVED HERE. WHAT HANGS ON IT: tl.slotA
  is the low end of the stretch of slots that the smallness test's claims read: had a step between
  taken a slot, the stretch here would be the narrower one: the weaker test. A lens to the
  skeleton's records lays for the note: 0 until the list of tables is closed, then F.next, then
  tl.slotA once the lookup on the digits is heard. LEFT OUT: HeadLoc.plain, the scalar heard in the
  round "REPLY". THE HEARD REPLY HAS ONE HOME, out.reply, laid by the hearing of that round; the
  switch behind it reads it there. THAT NO OTHER STEP TURNS IT IS NOT SAID BY A TYPE OF THIS FILE: a
  step's text can write S.out: it is a law on the steps' texts, or on the fold that lifts them: NOT
  PROVED HERE. `verify-on-bytes` carries the scalar across the switch in a local and lays out.reply
  behind: so at the one border between these two steps S.out.reply is laid and `verify-on-bytes`'s
  is not yet.
  LEFT OUT: a log of the values put under slots: coarse, the engine's own marks are that log
  (Fork.gotF, with next): a kind's state that keeps a list drops it at its lens; the link's last
  step asks the four conditions on slots of gotF, next and ns. LEFT OUT: the one equation at the
  door: the door is cut BEHIND the laying of the row: what crosses is the statement. LEFT OUT: the
  reply that the caller asks about, with which the heard reply is compared at the chain's end: a
  parameter, as the plan and the request are: no step writes it. IT NEVER ENTERS S: so no text over
  S can read it, BY TYPE: what was heard cannot have been made from what was asked; the last test is
  handed it (S.finAsked). KEPT, though no local of the text either: HeadOwn.Fm. MORE THAN THE
  SKELETON: HeadOwn.squaresP (none by default): the state of the squares' level's sumcheck. MORE
  THAN THE SKELETON: AttOwn.heard5 (none by default): what the text of an attention segment's own
  rounds hands on: WHY: `verify-on-bytes`'s four records planes, scores, d, x do not hold all that
  these rounds heard, so that kind's own text behind the hearing would have no place to read it
  from; `verify-on-bytes`'s routines read it nowhere; planes, scores, d and x stay beside it, for
  whoever reads these. OTHERWISE THAN THE SKELETON: x.win, the token that is checked at each covered
  position. The skeleton's quiet step behind the switch lays it into a blank x. Here x is none until
  the head's own rounds' hearing lays it whole, and that hearing makes win anew: IT IS A FUNCTION OF
  THE REQUEST's WORDS AND THE HEARD REPLY, as the covered positions are: NO FIELD in front of the
  hearing; no kind's text reads it there. (What that hearing's text does where no reply is heard is
  its own matter: nothing here asks that one is.) MORE THAN THE SKELETON: HeadOwn.opened (false by
  default): in the head's first four steps L and F are blanks: until S.openHead the shared readers
  (fork?, link?, tl?, look?, funs?, inLink) say none. As in the skeleton the state of the calls
  stands twice inside a link: check (stale there) and L.check (live); the link's last step takes the
  second back. READ IT BY S.live, WRITE IT BY S.putLive. A third frame, fr, moves alone in the
  head's first four steps and in the finish: there the state of the calls rests and fr is the frame
  that the calls turn.

WHO TURNS "here". A layers' or an attention link: ENTERED AT ITS FirstQuiet (enterLay, enterAtt):
its first call runs at "between" and turns S.check alone; FirstQuiet lays L and F anew, whole, so no
blank of these is ever read. The head's: at sFront (enterHead). The finish: at fFront (enterFin).
The members' places: at mFront (enterMem), OUT OF THE FINISH ALONE. LEFT AT ..DoorQuiet (leaveLink):
to "between", the live copy taken back: so all that a link held is dead behind it, by the type. Not
exact against the skeleton: its records lie from in front of the first call, with blanks; S has none
there, and an Option where the skeleton has a blank: a lens to the skeleton's records says which
blank stands for none, and lays "some" only of what its step has written.

Main names:
  LayOwn, AttOwn, HeadOwn, FinOwn, MemOwn, Here, S.
  S.start: the state in front of the first link, of a given state of the calls: BARE: IT GOES PAST
    ALL FOUR TESTS OF startP: for a harness and for toys. S.blank: a state for a start that must be
    total: marked, so that fin refuses it.
  S.fork?, putFork . link?, putLink . tl?, putTl . look?, putLook . funs?: the parts that steps of
    several kinds of link share; a put where there is no such part changes nothing. S.inLink.
  S.unmarked, unmarked_ok: the state if it bears no mark, else a refusal under the mark's name;
    the ?-form of each of the ten functions that mark, and putLive?, is that function followed by
    this: f? s = .ok t just where f s = t and t bears no mark. The four other puts' ?-forms have a
    test in front: they also refuse where the bare put, unmarked, changes nothing.
  S.lookHeard?, hearLook: the lookup on the calls, with nothing to read until it is heard.
  S.own?, headX?, stages?: parts that have no put: none until their step has laid them.
  S.heard5?, hear5: what an attention segment's own rounds hand on: the like.
  S.live, putLive. S.mark. blankOwn, blankHeard, enterLay, enterAtt, enterHead, openHead, enterFin,
    enterMem, leaveLink. S.onlyInLink: a step that refuses where no link is open. S.closeOk, owe,
    pay, closed, noneWaits: the debt of rows for a step that is no call. S.frame: the frame that the
    calls turn.
  parP, S.startOk, firstRecord, startP (start?): THE START IN PLAIN TEXT: the four tests on the
    public parameters; the first record; the two together. S.firstEnd?, S.fin: what goes on to the
    third chain; what the fold's last test asks.
  rowOfClaim, S.rows: a claim on the table read back as a row; the rows at the chain's end.
  S.req; S.reqT, tokv, rowR, rowE; reqOk; withReq, startReqP (startReq?); coveredAt, replyTok?,
    covered: the request. coveredAt: IN THIS FILE's OWN TEXT.
  TOOLS OF STAND-INS ALONE: Par's use in S.ctx, S.back, S.call:
    a context of `verify-on-bytes` laid around S with a stretch's entries, rounds and the columns
    left; what is read back; one call of A ROUTINE OF `verify-on-bytes` as a step: refused where the
    routine fails, a message is left open, or the stretch is not used up; it says how many columns
    were taken. S.callE, why, leftOver: the same with the reason kept. NO BLOCK THAT IS A KIND's OWN
    TEXT CALLS THESE.

DUTIES THAT THIS FILE NAMES AND DOES NOT TEST. (1) OF WHOEVER MAKES THE TABLE OF STEPS: the rounds
are cut by the fold, which also asks that none is left; THE ENTRIES ARE CUT BY NOBODY HERE: es is an
argument of ctx and call. That the stretches' entries, joined in order, are the plan's list with
none left over is a guard of `verify-on-bytes` (OnBytes/Iop/Ground.lean:823, :958, :981): cut ONE
list by the rows' numbers of rounds. (2) OF WHOEVER HANDS IN P : Par: samples and firstTree are the
plan's, read from the chain's hashed parameter bytes (firstTree is 0 for a first chain), AND THE
SAME P GOES TO startP AND TO EVERY call: nothing here ties them. At P.samples := shape.answers the
third test of startOk is empty. (3) OF WHOEVER LAYS A STATE OR A CONTEXT BY ANOTHER ROAD THAN startP
(S.start or firstRecord bare; a literal; S.back at a context laid by hand; S.call lays one at every
step): ctx, back, call and fin ask the codes' lengths nowhere: THEY RELY ON THE START FOR IT. (4) OF
WHOEVER LAYS req: THE WORDS ARE THE VERY WORDS THAT THE CHAIN's HASHED STATEMENT HOLDS, and T and V
at reqOk, startReqP, coveredAt and covered are the plan's: nothing here ties them. withReq asks no
test; start, startP and blank lay no request: reqOk then says no, and a layers' link's claim on the
embedding refuses (OnBytes/Model/LayerPanels.lean:496). (5) OF WHOEVER MAKES A DESCRIPTION's TEST ON
THE INSTANCE AT THE START: `verify-on-bytes`'s three tests on the reply that the caller asks about,
which no text over S can make: it is one word; it is an entry of the vocabulary; it is 0 where e < T
(OnBytes/Model/HeadLayout.lean:481, :485, :514). (6) OF WHOEVER LAYS A LINK's PART BACK FROM OUTSIDE
THIS FILE (a lens to another record): LAY BY "{ a with .. }": a new literal of named fields sets
every field that has a default (lookHeard, heard5, each of the Options; in the head's link opened
and squaresP too) back to it, in silence: what was heard is then gone, and the mark at a second
hearing does not come.

THE DEBT's TWO FORMS. Behind a close whose entry counts no rows `verify-on-bytes` holds that entry
(settled: 0 rows), and a text that lays the entry's count as it stands holds "some 0"; owe and back
lay none. BOTH ARE LET BY ALIKE HERE, AS `verify-on-bytes` DOES: noneWaits is what closeOk, owe,
closed and fin ask, and ctx lays an entry of 0 rows for "some 0", which `verify-on-bytes`'s close
lets by. They part at one place: pay 0 passes at "some 0" and refuses at none.

NOTHING TO READ BEFORE BIRTH. Inside a layers' or an attention link L, F and tl are laid whole at
the entry: tl is the plan's record, with the true numbers and its list of tables OPEN, which the
smallness test's transcript refuses. EVERY OTHER PART THAT A STEP MUST HAVE WRITTEN BEFORE IT IS
READ IS none UNTIL THAT STEP: the lookup's value (look?: until the lookup), the own rounds' record
(own?, funs? in a layers' link), the tables (funs? in an attention link and the head: until
ReadsQuiet), planes and scores, the head's x (headX?: until the head's own rounds' hearing, which
lays it whole), claim, wo, slot, the finish's G, answers and stages (stages?). SO A QUIET STEP LEFT
OUT OF A DESCRIPTION IS A REFUSAL ON THE HONEST PROOF: whoever reads behind it meets none. WHO LAYS
A PART FIRST: hearLook, for the lookup's value; else the step's own "{ a with own := some .. }". A
bare put turns a part only where it is laid (the rule: a put where there is no such part changes
nothing): so the laws of a part keep their form. BLANKS THAT STAND: AttOwn.d, x; HeadOwn.Fm;
FinOwn.row, L, st, sw. FOR THE LOOKUP ON THE CALLS THERE ARE TWO ROADS: lookHeard? reads what
hearLook laid, which no put writes; look? reads the home that a put can turn: a putLook BEHIND
hearLook turns the second and not the first, without a mark: whoever hears by hearLook reads by
lookHeard?. IN THE HEAD's LINK that second home is x.g1, which the head's own rounds' hearing makes
of what was heard: so between the lookup and that hearing look? says none and a putLook changes
nothing. ONE VALUE HAS A COPY INSIDE x: g1 (of lookHeard): a text outside this file that lays an x
whose g1 is not what was heard parts the two, and one that lays an x whose win is not made of the
words and the heard reply lays a wrong win: nothing here sees either. heard5 HAS ONE HOME: none
until hear5, then what that laid; heard5? reads it; no other function of this file names it. The
sum's tooth (a step at a wrong place refuses) bites between links, in the head's front, in the
finish and at the members' places; between two steps of one open link it is these Options that bite.

AT A WRONG PLACE. owe where rows are owed already; an enter.. where "here" is not what it should be;
leaveLink, openHead or hearLook where no such link is open; a second hearLook in one link; hear5
where no attention link is open; a second hear5 in one link: each leaves the state as it is and
MARKS it: failed := the first mark. S.fin refuses a mark; a fold may look behind every step. A put
where there is no such part still changes nothing and marks nothing: ask inLink, or match on the
reader's Option; or go through a lift that refuses where the part is not there. THREE WAYS TO ANSWER
A WRONG CALL STAND IN THIS FILE: to refuse, to mark and go on, to do nothing and say nothing. EACH
FUNCTION OF THE SECOND AND THE THIRD WAY HAS A FORM THAT REFUSES AT ONCE, UNDER THE MARK's OWN NAME
("state-put-.." for a put): A BLOCK's TEXT USES THESE; then a kind's lemma on "decide s = .ok t"
need carry no invariant of the whole fold. The marking forms and the bare puts stay for the lenses:
the laws of a part are proved of the bare puts. A ?-FORM ALSO REFUSES A STATE THAT CAME IN MARKED. A
QUIET STEP CAN BE LEFT OUT OF A DESCRIPTION UNSEEN BY ANY TEST ON THE PLAN (a step with a round
cannot): and it is the quiet steps that write much of what later steps read: see NOTHING TO READ
BEFORE BIRTH. ONCE failed IS some, every named test on values of `verify-on-bytes` behind it is
skipped: no verdict turns (fin refuses); the reason in a print is the mark's. A literal "{ s with
failed := none }" clears a mark: no text of a block may write failed.

Limits. S.fin is true in front of the sealing round as behind it: that the finish ran and the seal
is closed leaves no trace in S: the fold's "no round left" alone sees it. S.pay refuses 0 where
nothing is owed, and a second asking, where `verify-on-bytes` passes both: the refusing side. THE
START's FOUR TESTS: three are `verify-on-bytes`'s own plain tests, called by name (see
startOk). That startP or startReqP says yes at a lawful shape is tried by nothing that needs no
reader of files. Nothing is proved here but unmarked_ok. covered parts from `verify-on-bytes` in
WHEN and OF WHAT: that one makes the record in front of the chain, of the reply that the caller asks
about, which never enters S; so a layers' link, which stands in front of the hearing, has tokv
alone. What a link's routines are made of beside (the public files' letters) is no matter of S. why
joins name and place by " @ ": a form of this file's, no word of `verify-on-bytes`'s. S.ctx lays
"last" from rowsOwed alone: a made-up entry that holds the number of rows and no more: a routine
that begins by reading the entry of a round closed in an EARLIER step (Blk.lastEntry) is not served.
S.call and S.callE do not look at failed: whoever folds decides whether a mark refuses at once. That
rowOfClaim undoes memberClaim is not proved. There is no log of the values put under slots: coarse,
the engine's marks (Fork.gotF, next) stand for it. S.check's, S.st's and the links' parts' TYPES are
`verify-on-bytes`'s records. Nothing on soundness or on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.StagesLinks
import OnBytes.Model.Layer
import OnBytes.Model.Attention
import OnBytes.Model.Head
import Johnson.Desc.First.Att.K5Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

/-- An opened column, as a view holds it: the tree's key, the leaf, the words. -/
abbrev Col : Type := Nat × Nat × List UInt64

/-! ## What is held at one kind of place alone -/

/-- Inside a layers' link. -/
structure LayOwn where
  /-- the link, with the live state of the calls -/
  L : LinkCtx
  /-- the sub-proof's engine -/
  F : Fork
  /-- what the lookup on the calls returned: none until that step lays it -/
  fo : Option Forest.Heard := none
  /-- what the own rounds returned: none until that step lays it -/
  own : Option Layer.Own := none
  /-- the smallness test's record: FROM THE ENTRY ON THE PLAN's, its list of tables open; its field
  heard: what the lookup on the digits returned -/
  tl : HTailF2
  /-- what S.hearLook laid: none until then; no put writes it -/
  lookHeard : Option Forest.Heard := none

/-- Inside an attention link. -/
structure AttOwn where
  L : LinkCtx
  F : Fork
  tl : HTailF2
  /-- what the lookup on the calls returned: none until that step lays it -/
  g : Option Forest.Heard := none
  /-- of the segment's own rounds: none until their step lays them -/
  planes : Option (Array Attention.PlaneClaim) := none
  scores : Option (Array Attention.Score) := none
  d : Attention.Divide
  x : Attention.Attain
  /-- the tables: none until the reads' quiet step lays them -/
  t : Option Attention.Tables := none
  /-- what S.hearLook laid: none until then; no put writes it -/
  lookHeard : Option Forest.Heard := none
  /-- what S.hear5 laid: what the segment's own rounds hand on: none until then; no put writes it;
  `verify-on-bytes`'s routines read it nowhere -/
  heard5 : Option Att.P.Heard := none

/-- Inside the head's link. The first three: across the round "REPLY" and the switch behind it. -/
structure HeadOwn where
  fr : ReqFrame
  kept : Array Nat
  ids : Array Nat
  L : LinkCtx
  F : Fork
  /-- what the head's own rounds heard: LAID WHOLE BY THAT HEARING, none until then: so "none" means
  "not laid" of every field of it. Its field g1 is a copy that the hearing makes of lookHeard; its
  field win the hearing makes of the request's words and the heard reply -/
  x : Option Head.Heard := none
  /-- the tables: none until the reads' quiet step lays them -/
  t : Option Head.Tables := none
  /-- from the entry on the plan's, its list of tables open -/
  tl : HTailF2
  /-- none until the quiet step behind the digits' lookup lays it -/
  claim : Option WsClaim := none
  /-- none until the merge lays it -/
  wo : Option WsForkOut := none
  /-- the engine in front of the merge: no local of the verifier's text -/
  Fm : Fork
  /-- none until the quiet step behind the merge lays it -/
  slot : Option Nat := none
  /-- L and F are laid: false in the first four steps -/
  opened : Bool := false
  /-- the state of the sumcheck of the squares' level, which x.wpl does not keep: for a text of the
  head's own rounds that makes that level's claim later; `verify-on-bytes`'s routines read it
  nowhere -/
  squaresP : Option Model.Psc := none
  /-- what S.hearLook laid: none until then; no put writes it -/
  lookHeard : Option Forest.Heard := none

/-- In the finish: the last switch and the last proximity test. -/
structure FinOwn where
  /-- none until the finish's front lays it -/
  G : Option ReqGroup := none
  fr : ReqFrame
  sw : Switched
  /-- none until the batching's front lays it -/
  answers : Option Nat := none
  /-- the stage in hand and the stages behind it: ONE FIELD: none until the quiet step behind the
  batching lays it: so "no stage is left" is said of no blank -/
  stages : Option (Params.IoppStage × List Params.IoppStage) := none
  row : GroupRow
  L : GroupLayout
  mask : Option Nat
  st : Switched

/-- At the chain's end: the rows on the table, W's sending, what goes on to the third chain. -/
structure MemOwn where
  msg : Array OracleNotice
  ids : Array Nat
  /-- none in front of the batching's place; behind it the claim; behind W's sending all five -/
  lin : Option LinFirst

/-- Where the chain stands. -/
inductive Here where
  /-- in front of the first link, or between two links -/
  | between
  | lay (a : LayOwn)
  | att (a : AttOwn)
  | head (a : HeadOwn)
  | fin (a : FinOwn)
  | mem (a : MemOwn)

/-! ## The record -/

/-- **The state that the first chain carries.** -/
structure S where
  st : Statement
  book : TreeBook
  /-- the roots received so far on this chain -/
  roots : Nat
  /-- some n: the round closed last counts n batched rows, and that number is not yet compared -/
  rowsOwed : Option Nat
  /-- the first named test on values that has failed -/
  failed : Option String
  /-- the state of the calls over the links; its field frame: the frame's twelve -/
  check : ChainCheck
  /-- the index masks' message . the pile . the reply -/
  out : Proof.LinksResult
  here : Here
  /-- the request, as far as it is public: all words of the request file: the T tokens, then the
  first covered position and the position after the last covered one. Laid at the start
  (S.withReq, S.startReq?); no function of this file writes it later -/
  req : Array UInt32 := #[]

namespace S

/-- In front of the first link: the codes; nothing sent; no tree; no root. BARE: any codes and any
state of the calls: NONE OF THE FOUR TESTS OF startP IS ASKED: for a harness and for toys. -/
def start (codes : Codes) (check : ChainCheck) : S :=
  { st := { codes := codes }, book := {}, roots := 0, rowsOwed := none, failed := none,
    check := check, out := {}, here := .between }

/-- A state that stands for "no lawful start": for a description whose start must be total, with its
own test beside. IT IS MARKED, and S.fin refuses a mark. The mark rides through S.call (ctx lays it,
back reads it) and through every function of this file but one: S.back at a context that another
hand has laid takes THAT context's mark; and a literal can clear it. -/
def blank : S :=
  { start default { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ } with
    failed := some "state-blank" }

/-- Marks the state: the first mark stays, as with `verify-on-bytes`'s named tests. -/
def mark (s : S) (name : String) : S :=
  match s.failed with
  | some _ => s
  | none => { s with failed := some name }

/-- **The state, if it bears no mark; else a refusal under the mark's own name.** What every ?-form
of this file that returns ends in: so a ?-form refuses at once where its marking form marks, under
the same name, and it refuses a state that came in marked, under that mark. -/
def unmarked (s : S) : Except String S :=
  match s.failed with
  | none => .ok s
  | some m => .error m

/-- THE TIE OF A ?-FORM TO ITS MARKING FORM (the ten functions that mark; putLive): f? s :=
(f s).unmarked: it returns just where f leaves no mark, and then it returns what f returns. (The
four other puts' ?-forms ask in front that the part is there.) -/
theorem unmarked_ok (s t : S) : s.unmarked = .ok t ↔ s = t ∧ t.failed = none := by
  unfold unmarked
  cases h : s.failed with
  | none =>
    constructor
    · intro e
      cases e
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, _⟩
      rfl
  | some m =>
    constructor
    · intro e
      cases e
    · rintro ⟨rfl, e⟩
      rw [h] at e
      cases e

/-- In front of the first link, or between two links. -/
def atBetween (s : S) : Bool :=
  match s.here with
  | .between => true
  | _ => false

/-! ## The parts that steps of several kinds of link share -/

def fork? (s : S) : Option Fork :=
  match s.here with
  | .lay a => some a.F
  | .att a => some a.F
  | .head a => if a.opened then some a.F else none
  | _ => none

def putFork (s : S) (F : Fork) : S :=
  match s.here with
  | .lay a => { s with here := .lay { a with F := F } }
  | .att a => { s with here := .att { a with F := F } }
  | .head a => if a.opened then { s with here := .head { a with F := F } } else s
  | _ => s

/-- putFork, REFUSING where no sub-proof's engine is there to be written (putFork drops the value
there, in silence), and at a marked state. A BLOCK's TEXT USES THIS FORM. -/
def putFork? (s : S) (F : Fork) : Except String S :=
  if s.fork?.isSome then (s.putFork F).unmarked else .error "state-put-fork"

def link? (s : S) : Option LinkCtx :=
  match s.here with
  | .lay a => some a.L
  | .att a => some a.L
  | .head a => if a.opened then some a.L else none
  | _ => none

def putLink (s : S) (L : LinkCtx) : S :=
  match s.here with
  | .lay a => { s with here := .lay { a with L := L } }
  | .att a => { s with here := .att { a with L := L } }
  | .head a => if a.opened then { s with here := .head { a with L := L } } else s
  | _ => s

/-- putLink, refusing where no link is open, and at a marked state. -/
def putLink? (s : S) (L : LinkCtx) : Except String S :=
  if s.link?.isSome then (s.putLink L).unmarked else .error "state-put-link"

def tl? (s : S) : Option HTailF2 :=
  match s.here with
  | .lay a => some a.tl
  | .att a => some a.tl
  | .head a => if a.opened then some a.tl else none
  | _ => none

def putTl (s : S) (tl : HTailF2) : S :=
  match s.here with
  | .lay a => { s with here := .lay { a with tl := tl } }
  | .att a => { s with here := .att { a with tl := tl } }
  | .head a => if a.opened then { s with here := .head { a with tl := tl } } else s
  | _ => s

/-- putTl, refusing where no link is open, and at a marked state. -/
def putTl? (s : S) (tl : HTailF2) : Except String S :=
  if s.tl?.isSome then (s.putTl tl).unmarked else .error "state-put-tl"

/-- What the lookup on the calls returned, where a put can turn it. IN THE HEAD's LINK: none until
the head's own rounds' hearing has laid x, then x.g1: between the lookup and that hearing the value
has one home, lookHeard, which no put writes: read lookHeard?. It answers wherever x is laid, heard
or not: a text that lays x early, by hand, makes it answer in front of the lookup. -/

def look? (s : S) : Option Forest.Heard :=
  match s.here with
  | .lay a => a.fo
  | .att a => a.g
  | .head a => if a.opened then a.x.map (·.g1) else none
  | _ => none

def putLook (s : S) (g : Forest.Heard) : S :=
  match s.here with
  | .lay a => if a.fo.isSome then { s with here := .lay { a with fo := some g } } else s
  | .att a => if a.g.isSome then { s with here := .att { a with g := some g } } else s
  | .head a =>
    if a.opened then
      { s with here := .head { a with x := a.x.map fun x => { x with g1 := g } } }
    else s
  | _ => s

/-- putLook, refusing where no link is open, and at a marked state. -/
def putLook? (s : S) (g : Forest.Heard) : Except String S :=
  if s.look?.isSome then (s.putLook g).unmarked else .error "state-put-look"

/-- What the lookup on the calls returned, AND NOTHING UNTIL IT IS HEARD: none until S.hearLook, and
then what THAT laid: it has a field of its own, which no put writes. -/
def lookHeard? (s : S) : Option Forest.Heard :=
  match s.here with
  | .lay a => a.lookHeard
  | .att a => a.lookHeard
  | .head a => if a.opened then a.lookHeard else none
  | _ => none

/-- **The hearing of the lookup on the calls**: IT IS THIS FUNCTION THAT LAYS THE LOOKUP's VALUE
FIRST: in lookHeard, and, in a layers' and an attention link, where look? reads it. In the head's
link lookHeard alone is laid: x is the later hearing's. No put: where no link is open, and at a
second hearing in one link, the state stays and is MARKED. -/
def hearLook (s : S) (g : Forest.Heard) : S :=
  match s.here with
  | .lay a =>
    if a.lookHeard.isSome then s.mark "state-look-twice"
    else { s with here := .lay { a with fo := some g, lookHeard := some g } }
  | .att a =>
    if a.lookHeard.isSome then s.mark "state-look-twice"
    else { s with here := .att { a with g := some g, lookHeard := some g } }
  | .head a =>
    if !a.opened then s.mark "state-hear-look"
    else if a.lookHeard.isSome then s.mark "state-look-twice"
    else { s with here := .head { a with lookHeard := some g } }
  | _ => s.mark "state-hear-look"

/-- hearLook, refusing at once where it marks ("state-hear-look", "state-look-twice"). -/
def hearLook? (s : S) (g : Forest.Heard) : Except String S := (s.hearLook g).unmarked

/-- What an attention segment's own rounds handed on, AND NOTHING UNTIL IT IS HEARD: none until
S.hear5, then what that laid; none wherever no attention link is open. -/
def heard5? (s : S) : Option Att.P.Heard :=
  match s.here with
  | .att a => a.heard5
  | _ => none

/-- **The hearing of an attention segment's own rounds**: the value is laid in heard5, AND NO OTHER
FIELD TURNS: planes, scores, d and x are laid by whoever wants them. No put: where no
attention link is open, and at a second hearing in one link, the state stays and is MARKED. -/
def hear5 (s : S) (h : Att.P.Heard) : S :=
  match s.here with
  | .att a =>
    if a.heard5.isSome then s.mark "state-heard5-twice"
    else { s with here := .att { a with heard5 := some h } }
  | _ => s.mark "state-hear5"

/-- hear5, refusing at once where it marks ("state-hear5", "state-heard5-twice"). -/
def hear5? (s : S) (h : Att.P.Heard) : Except String S := (s.hear5 h).unmarked

/-- The tables with their weights, as the smallness test's claims take them. -/
def funs? (s : S) : Option (Array HFun) :=
  match s.here with
  | .lay a => a.own.map (·.funs)
  | .att a => a.t.map (·.funs)
  | .head a => if a.opened then a.t.map (·.funs) else none
  | _ => none

/-- What a layers' link's own rounds returned: none until that step has laid it. -/
def own? (s : S) : Option Layer.Own :=
  match s.here with
  | .lay a => a.own
  | _ => none

/-- What the head's own rounds heard: none until that hearing has laid it, whole. -/
def headX? (s : S) : Option Head.Heard :=
  match s.here with
  | .head a => if a.opened then a.x else none
  | _ => none

/-- The finish's stage in hand and the stages behind it: none until they are laid. -/
def stages? (s : S) : Option (Params.IoppStage × List Params.IoppStage) :=
  match s.here with
  | .fin a => a.stages
  | _ => none

/-- A link is open. A STEP THAT WANTS A LINK's PART ASKS THIS, OR MATCHES ON THE Option: it never
takes a blank in the part's place: at a wrong place it would run on the blank and its put would be
dropped without a word. -/
def inLink (s : S) : Bool := s.fork?.isSome

/-- A step, its type written out, that refuses where no link is open. -/
def onlyInLink (k : S → List Fmt.RoundView → List Col → Option (S × Nat)) :
    S → List Fmt.RoundView → List Col → Option (S × Nat) :=
  fun s rs cols => if s.inLink then k s rs cols else none

/-! ## The state of the calls: which copy is live -/

/-- **The live state of the calls**: inside a link the link's own copy, else the walk's. (Its frame
rests in the head's front and in the finish: see S.frame.) Right at every border IF "here" is turned
where the functions enter.. and leaveLink below say. -/
def live (s : S) : ChainCheck :=
  match s.link? with
  | some L => L.check
  | none => s.check

/-- The frame that the calls turn: in the head's front and in the finish the frame fr, which moves
alone there; else the live state of the calls' own. -/
def frame (s : S) : ReqFrame :=
  match s.here with
  | .head a => if a.opened then a.L.check.frame else a.fr
  | .fin a => a.fr
  | _ => s.live.frame

/-- Writes the live copy, and that one alone. -/
def putLive (s : S) (c : ChainCheck) : S :=
  match s.link? with
  | some L => s.putLink { L with check := c }
  | none => { s with check := c }

/-- putLive, refusing at a marked state. putLive itself drops nothing: where a link is open it
writes the link's copy, else the walk's. -/
def putLive? (s : S) (c : ChainCheck) : Except String S := (s.putLive c).unmarked

end S

/-! ## The rows at the chain's end -/

/-- A claim of the test on the table, read back as a row on the table: undoes memberClaim. -/
def rowOfClaim (c : LinClaim) : TensorRow :=
  { g := c.g, psi := c.psi, masks := c.masks.toList.map fun m => (⟨m.oracle, m.index⟩, m.coeff),
    target := c.target }

/-- The rows on the table at the chain's end: the pile, in front of the batching; behind it the one
row, read off the claim. -/
def S.rows (s : S) : List TensorRow :=
  match s.here with
  | .mem a =>
    match a.lin with
    | some l => [rowOfClaim l.claim]
    | none => s.out.pending
  | _ => s.out.pending

/-! ## Who turns "here", and with which blanks -/

-- For the blanks alone, as in the skeleton; derived inside this namespace, so that a file that
-- imports both meets no name twice.
deriving instance Inhabited for OnBytes.Attention.Divide
deriving instance Inhabited for OnBytes.Attention.Attain
deriving instance Inhabited for OnBytes.Attention.Tables

/-- What a layers' link's own rounds return: a blank. The skeleton's text. NO FUNCTION OF
THIS FILE LAYS IT: kept for a lens to the skeleton's records alone. -/
def blankOwn : Layer.Own :=
  { v := { y := { h := default }, sc := default, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] },
    H := { fo := default, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := default, sPv := 0,
           omV := #[], tV := default },
    K := { rs := #[], sA0 := 0, sH1 := 0, sB0 := 0, sV := 0, fin := {}, rowS := {} },
    hd := default, hd2 := none, sVE := 0, wo := default, funs := #[] }

/-- What the head hears: a blank. The skeleton's text. No function of this file lays it:
kept for a lens to the skeleton's records; toy records in other files start from it. -/
def blankHeard : Head.Heard :=
  { win := #[], g1 := { shape := {}, leaves := {} }, Zl := #[], PV := #[], sW := 0,
    gp := #[], wpl := {}, sPv := 0, omV := #[], tV := {}, tN := {}, tH := {}, rs := #[],
    qN := 0, qH := 0 }

namespace S

/-- At a layers' link's FirstQuiet. L, F: as that step makes them. tl: THE PLAN's record of the
smallness test (`verify-on-bytes`'s hp.tl), its list of tables open. -/
def enterLay (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : S :=
  if s.atBetween then { s with here := .lay { L := L, F := F, tl := tl } }
  else s.mark "state-enter-lay"

/-- enterLay, refusing at once where it marks. -/
def enterLay? (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : Except String S :=
  (s.enterLay L F tl).unmarked

/-- At an attention link's FirstQuiet. L, F, tl: as that step makes them. -/
def enterAtt (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : S :=
  if s.atBetween then
    { s with here := .att { L := L, F := F, tl := tl, d := default, x := default } }
  else s.mark "state-enter-att"

/-- enterAtt, refusing at once where it marks. -/
def enterAtt? (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : Except String S :=
  (s.enterAtt L F tl).unmarked

/-- At the head's sFront. tl: the plan's record of the smallness test, its list of tables open. -/
def enterHead (s : S) (tl : HTailF2) : S :=
  if s.atBetween then
    { s with here := .head { fr := s.check.frame, kept := #[], ids := #[],
                             L := { check := s.check }, F := {}, tl := tl, Fm := {} } }
  else s.mark "state-enter-head"

/-- enterHead, refusing at once where it marks. -/
def enterHead? (s : S) (tl : HTailF2) : Except String S := (s.enterHead tl).unmarked

/-- At the head's sSwitchQuiet, in front of its puts: from here on L and F count as laid. The walk's
copy of the state of the calls, which was the live one so far, is carried into L: so S.live does not
step back. -/
def openHead (s : S) : S :=
  match s.here with
  | .head a =>
    if a.opened then s.mark "state-open-head"
    else { s with here := .head { a with opened := true, L := { a.L with check := s.check } } }
  | _ => s.mark "state-open-head"

/-- openHead, refusing at once where it marks. -/
def openHead? (s : S) : Except String S := s.openHead.unmarked

/-- At the finish's fFront. -/
def enterFin (s : S) : S :=
  if s.atBetween then
    { s with here := .fin { fr := s.check.frame, sw := default, row := default, L := default,
                            mask := none, st := default } }
  else s.mark "state-enter-fin"

/-- enterFin, refusing at once where it marks. -/
def enterFin? (s : S) : Except String S := s.enterFin.unmarked

/-- At the members' mFront: OUT OF THE FINISH ALONE: so S can tell a chain whose finish has run from
one where it has not. -/
def enterMem (s : S) : S :=
  match s.here with
  | .fin _ => { s with here := .mem { msg := #[], ids := #[], lin := none } }
  | _ => s.mark "state-enter-mem"

/-- enterMem, refusing at once where it marks. -/
def enterMem? (s : S) : Except String S := s.enterMem.unmarked

/-- At a link's DoorQuiet: the live copy is taken back; all that the link held is dropped. -/
def leaveLink (s : S) : S :=
  if s.inLink then { s with check := s.live, here := .between } else s.mark "state-leave-link"

/-- leaveLink, refusing at once where it marks. -/
def leaveLink? (s : S) : Except String S := s.leaveLink.unmarked

/-! ## The debt of rows, for a step that is no call of `verify-on-bytes` -/

/-- **No count waits**: nothing is owed, or the round closed last counts no rows:
`verify-on-bytes`'s Chan.settled (OnBytes/Iop/Ground.lean:602-605). "some 0" AND "none" ANSWER
ALIKE. The functions of this file lay none for it (owe, back); a step that lays what the closed
entry counts as it stands lays "some 0". ASK THIS, NEVER isNone OR THE PATTERN none. -/
def noneWaits (s : S) : Bool :=
  match s.rowsOwed with
  | none => true
  | some r => r == 0

/-- A round may be closed: no count waits. -/
def closeOk (s : S) : Bool := s.noneWaits

/-- Behind a close: what the closed round's entry counts is owed, if it counts any. WHERE ROWS ARE
OWED ALREADY `verify-on-bytes`'s close refuses (OnBytes/Iop/Ground.lean:825): here the state is
marked and the standing debt stays. -/
def owe (s : S) (rows : Nat) : S :=
  if s.noneWaits then { s with rowsOwed := if rows == 0 then none else some rows }
  else s.mark "state-rows-owed"

/-- owe, refusing at once where it marks ("state-rows-owed"). S.closed is the same as an Option, but
that it lets a marked state by. -/
def owe? (s : S) (rows : Nat) : Except String S := (s.owe rows).unmarked

/-- **A round is closed by a step that is no call**: refused where rows are owed; else what the
closed round's entry counts is owed. closeOk and owe in one, so that the first cannot be forgotten
(the third clause of OnBytes/Iop/Ground.lean:825, then :843-844). -/
def closed (s : S) (rows : Nat) : Option S :=
  if s.noneWaits then some (s.owe rows) else none

/-- The count is compared. Refused at another number, and where nothing is owed. -/
def pay (s : S) (rows : Nat) : Option S :=
  match s.rowsOwed with
  | some n => if n == rows then some { s with rowsOwed := none } else none
  | none => none

/-! ## The end -/

/-- What goes on to the third chain: none until W's number is laid. -/
def firstEnd? (s : S) : Option Proof.FirstEnd :=
  match s.here with
  | .mem a => a.lin.bind fun l => if l.w != noId then some ⟨s.st, s.book, l⟩ else none
  | _ => none

/-- What the fold's last test asks of the state: no mark; no count waits; the chain stands at its
end with W sent. Not asked: that every group is in a test: W's is not. -/
def fin (s : S) : Bool :=
  s.failed.isNone && s.noneWaits && ((s.firstEnd?.map fun e => e.lin.w != noId).getD false)

end S

/-! ## A context of `verify-on-bytes` around S -/

/-- What a context holds beside S and a stretch, and no step writes. -/
structure Par where
  /-- the number of the first tree that this chain sends -/
  firstTree : Nat
  /-- the answers to each out-of-domain sample -/
  samples : Nat

namespace S

/-- The context. es, rs: the stretch's entries and rounds; cols: the opened columns left. -/
def ctx (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (cols : List Col) : Ctx :=
  { ch := { dry := false, firstTree := P.firstTree, samples := P.samples, entries := es,
            left := rs, opened := cols, roots := s.roots,
            last := s.rowsOwed.map fun n => { name := "", rows := n }, askedRows := false },
    st := s.st, book := s.book, failed := s.failed }

/-- What is read back out of a context. -/
def back (s : S) (c : Ctx) : S :=
  { s with
    st := c.st, book := c.book, roots := c.ch.roots, failed := c.failed,
    rowsOwed := if c.ch.settled then none else c.ch.last.map (·.rows) }

/-- One call of a routine as a step on data: its value, the state, how many columns it took. -/
def call {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (cols : List Col)
    (b : Blk α) : Option (α × S × Nat) :=
  match b (s.ctx P es rs cols) with
  | .error _ => none
  | .ok (a, c) =>
    if c.ch.cur.isNone && c.ch.entries.isEmpty && c.ch.left.isEmpty &&
        decide (c.ch.opened.length ≤ cols.length) then
      some (a, s.back c, cols.length - c.ch.opened.length)
    else none

/-- A failure of `verify-on-bytes` as one string: its name; behind " @ " its place, if any. -/
def why (f : Failure) : String := if f.place.isEmpty then f.name else f.name ++ " @ " ++ f.place

/-- Which of call's own four tests on the context that a routine leaves is the first to fail. -/
def leftOver (c : Ctx) : String :=
  if !c.ch.cur.isNone then "state-call-open"
  else if !c.ch.entries.isEmpty then "state-call-entries"
  else if !c.ch.left.isEmpty then "state-call-rounds"
  else "state-call-columns"

/-- **call, with the reason kept**: where the routine fails, `verify-on-bytes`'s own word (why);
where call's own tests refuse, which of them (leftOver). It returns where call returns, and the same
(call_eq_callE). -/
def callE {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (cols : List Col)
    (b : Blk α) : Except String (α × S × Nat) :=
  match b (s.ctx P es rs cols) with
  | .error f => .error (why f)
  | .ok (a, c) =>
    if c.ch.cur.isNone && c.ch.entries.isEmpty && c.ch.left.isEmpty &&
        decide (c.ch.opened.length ≤ cols.length) then
      .ok (a, s.back c, cols.length - c.ch.opened.length)
    else .error (leftOver c)

/-- The chain's two numbers, off the first chain's parameters: a first chain takes over no tree. -/
def _root_.VerifiableInference.Desc.First.parP (first : Params.First) : Par :=
  { firstTree := 0, samples := first.given.plan.samples }

/-- **The four tests on the public parameters**: every code's message length is a power of two (each
run of `verify-on-bytes` asks that first; a state laid by hand would go past it; ctx, back, call and
fin rely on the start for it); the shape is lawful under the codes; its number of answers is the
plan's; the layout is lawful for the shape. THREE OF THE FOUR ARE `verify-on-bytes`'s OWN PLAIN
TESTS, CALLED BY NAME (Codes.lengthsOk, reqOk, reqLayoutOk): what each asks is not written in
this folder's own text. P.firstTree is read by no test. -/

def startOk (P : Par) (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    Bool :=
  codes.lengthsOk &&
    (OnBytes.reqOk codes shape && shape.answers == P.samples && reqLayoutOk codes shape layout)

/-- **Nothing has happened yet.** The fields are written out (the frame's rows: the empty record).
BARE: it asks none of the four tests. A WHOLE LITERAL of S, of the state of the calls, of the frame
and of the walk's result: a field that one of these gains with a default is laid at that default in
silence. -/

def firstRecord (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) : S :=
  { st := { codes := codes, oracles := #[], groups := #[] }
    book := { trees := #[], place := #[] }
    roots := 0
    rowsOwed := none
    failed := none
    check :=
      { frame :=
          { shape := shape, groups := reqGroups shape, next := .first, link := 0, moment := 0,
            group := noId, keptBefore := #[], atStart := #[], own := #[], plain := [], mask := none,
            rows := {} }
        rows := ⟨layout⟩
        sent := #[]
        inLink := false
        moments := 0 }
    out := { indexMasks := noId, pending := [], reply := none }
    here := .between
    req := #[] }

/-- **The first state, or nothing.** IN PLAIN TEXT: no function in it takes or makes a context of
`verify-on-bytes`. THE CALLER's DUTY: codes, shape, layout AND P come from the chain's parameter
bytes, which the strict reader hashes, and from nowhere else: no test here can see that. -/
def startP (P : Par) (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    Option S :=
  if startOk P codes shape layout then some (firstRecord codes shape layout) else none

/-- startP under a second name. -/
def start? (P : Par) (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    Option S := startP P codes shape layout

/-! ## The request, as far as it is public -/

/-- The number of tokens that the request's words hold: all words but the last two. -/
def reqT (s : S) : Nat := s.req.size - 2

/-- The request's tokens: what a layers' link reads of the instance (`verify-on-bytes`'s text:
OnBytes/Model/HeadLayout.lean:516, at T := reqT). -/
def tokv (s : S) : Array Nat := (s.req.extract 0 s.reqT).map (·.toNat)

/-- The first covered position. -/
def rowR (s : S) : Nat := (s.req.getD s.reqT 0).toNat

/-- The position after the last covered one. -/
def rowE (s : S) : Nat := (s.req.getD (s.reqT + 1) 0).toNat

/-- `verify-on-bytes`'s tests on the request that read no reply: T + 2 words; every token an entry
of the vocabulary; r < e ≤ T (OnBytes/Model/HeadLayout.lean:481, :485, :515, :519, :520). NOT HERE,
since they read the reply that the caller asks about: that it is one word, an entry of the
vocabulary, and 0 where e < T (:481, :485, :514). T, V: the plan's. Where no request is laid (the
default) it says no at every T. -/
def reqOk (T V : Nat) (s : S) : Bool :=
  s.req.size == T + 2 && s.tokv.all (fun v => decide (v < V)) &&
    !(decide (s.rowR ≥ s.rowE) || decide (s.rowE > T))

/-- Lays the request's words. BARE: no test. -/
def withReq (s : S) (req : Array UInt32) : S := { s with req := req }

/-- The first state with the request's words laid, where the tests on them that read no reply hold.
T, V: the plan's. -/
def startReqP (P : Par) (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout)
    (T V : Nat) (req : Array UInt32) : Option S :=
  (startP P codes shape layout).bind fun s =>
    if (s.withReq req).reqOk T V then some (s.withReq req) else none

/-- startReqP under a second name. -/
def startReq? (P : Par) (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout)
    (T V : Nat) (req : Array UInt32) : Option S := startReqP P codes shape layout T V req

/-- The covered positions at a reply y that the caller hands in: of the request's words and y. IN
THIS FILE's OWN TEXT: four tests, under `verify-on-bytes`'s names: y is an entry of the vocabulary;
the words are T + 2; every token is an entry of the vocabulary; r < e ≤ T. Then the four arrays and
the count. Tokens and positions are taken from the words alone, at the plan's T. -/
def coveredAt (T V y : Nat) (s : S) : Except String Head.Covered :=
  let tokv := (s.req.extract 0 T).map (·.toNat)
  let r := (s.req.getD T 0).toNat
  let e := (s.req.getD (T + 1) 0).toNat
  let on := fun t => decide (r ≤ t) && decide (t < e)
  if !decide (y < V) then .error "token-range"
  else if !(s.req.size == T + 2) then .error "token-length"
  else if !(tokv.all fun v => decide (v < V)) then .error "token-range"
  else if decide (r ≥ e) || decide (e > T) then .error "statement-range"
  else .ok {
    tokv := tokv
    hOn := (Array.range T).map on
    hWin := (Array.range T).map fun t =>
      if on t then (if t + 1 < T then tokv.getD (t + 1) 0 else y) else 0
    hOnC := (Array.range T).map fun t => on t && decide (t + 1 < T)
    hRC := ((List.range T).filter fun t => on t && decide (t + 1 < T)).length }

/-- The HEARD reply as a token's number: none until it is heard, and where what was heard is not a
natural number below the field's prime, as ofNat lays one. -/
def replyTok? (s : S) : Option Nat :=
  s.out.reply.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none

/-- **The covered positions: what the head's link reads of the instance: A FUNCTION, NO FIELD**: of
the request's words and THE HEARD REPLY: of what is public in the request and of what was heard,
never of the asked token. Refused until the reply is heard. `verify-on-bytes` makes them of the
asked reply, in front of the chain; on a file that S.finAsked lets by the two are one. OF THE HEARD
REPLY it asks that it is an entry of the vocabulary; "0 where e < T" it asks of nobody: that follows
at the end alone, from S.finAsked with duty (5) of the head. -/

def covered (T V : Nat) (s : S) : Except String Head.Covered :=
  match s.replyTok? with
  | some y => s.coveredAt T V y
  | none => .error "state-reply"

/-- fin, and what was heard is what was asked, AND WHERE THE LAST POSITION IS NOT COVERED (e < T, by
the request's words in S) WHAT WAS ASKED IS 0. asked: the reply that the caller asks about: it comes
in HERE and nowhere else. (`verify-on-bytes` compares at the members' front, marks and goes on, and
refuses at its end: OnBytes/Proof/File.lean:82: the same verdict. The third conjunct is its test in
front of the chain, OnBytes/Model/HeadLayout.lean:485: where e < T the heard reply is bound by no
equation: so that it cannot be forgotten it is asked here too; duty (5) stands.) Where no request is
laid the third conjunct holds. A helper for a description's last test, which reads asked out of the
instance. -/
def finAsked (asked : E) (s : S) : Bool :=
  s.fin && s.out.reply == some asked && (!decide (s.rowE < s.reqT) || asked == ofNat 0)

end S

end VerifiableInference.Desc.First

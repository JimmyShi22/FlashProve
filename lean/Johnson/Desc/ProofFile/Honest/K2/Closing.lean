-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Closing.lean: the honest side of the kind "the code switch" (K2):
A SEGMENT's GROUP's ROWS, MADE ANEW of the segments' own main rows, the challenges heard and the
carried stretches; and with them THE LETTER `closing` OF Honest/K2/Half.lean FILLED: what the fold
in front of a switch leaves. It defines part of the honest prover. Definitions with code; no
theorem.

Why it goes back to the first segment. A group's rows are its members'. From the second segment on
one member is the carrying message, whose main rows hold what the fold before left. So a group's
rows are made of what the fold of the segment before leaves, that of the group's rows before, and so
on back.

A segment's rows (`segmentGroupRows`). Its oracle messages, in the order of sending: in the first sending
the carrying message, the kept members' copies, the segment's own messages of moment 0, the closing
fold's fresh mask; then the later moments' own messages. Each is laid in full, of its main rows and
ITS OWN carried stretch (`messageRows`, Honest/K2/Sending.lean). What stands in the main rows:
Johnson/Desc/K2/Honest/Carrying.lean's `mainRows` at what the fold before left; at the first segment
the own messages' alone. All but the fresh mask are the group's members: the carrying message is not
kept, a copy is kept if its target says "kept again", an own message if a later segment reads it.
One step (`segmentLeft`): these rows, then Johnson/Desc/K2/Honest/FoldEnd.lean's `foldEnd` at the
fold's challenges.

  `SegmentPub`, `SegmentPub.messages`   what is public of a segment, as far as this is read; how
                  many oracle messages it has sent
  `GroupRows`, `segmentGroupRows`   a group's members, each in full, and the closing fold's fresh mask
  `frozenLeft`    what a fold leaves, reckoned once and kept in arrays
  `challengesAt`, `challengesOr0`   the elements that the challenges of given numbers drew: the
                  first refuses where one lacks; the second is total, and is what a step calls
  `groupFits`     a public test: a group's shapes fit a fold: the verifier's own two tests, called
  `segmentLeft`, `closingFrom`   one step; the steps from a segment on
  `closingOf`, `closingFor`   what the fold of the last of these segments leaves: for a switch; the
                  second holds the kept members that it left against the switch's own sizes
  `groupRowsOf`   the rows of the last of these segments' group: FOR WHOEVER CLOSES THAT GROUP: its
                  own fresh mask is not among the stretches then

TWO LETTERS. `table`: a fresh mask's table (Honest/K2/Sending.lean). `own`: THE MAIN ROWS OF A
SEGMENT's OWN MESSAGES outside the pads, at all moments: segment, the message's number in the
segment, row, place. The kind's lot lays the frame's one function there (`ownBy`,
Honest/K2/AtPlan.lean, which this library may not hold: `RowData`, Honest/RowData.lean, at the
message's address).

The stretches are taken in the order of Honest/K2/Half.lean's `frontOf`: segment by segment, in a
segment in the order of sending.

IT BINDS EVERY SENDER OF THE CHAIN. All sendings of all segments in front are laid anew here by
`messageRows`: the switches' and the others'. Whoever sends one of them must lay its coins in that
order and take that count, a fresh mask's 2 k + 1 among it: else this text refuses, or makes other
rows than were sent.

WHAT IS REFUSED, AND WHAT IS NOT. EVERY REFUSAL OF A STEP READS PUBLIC DATA ALONE: sizes, shapes,
counts (`challengesAt`, which no step calls, still refuses on what was heard). A LIST OF CHALLENGES
THAT IS TOO SHORT IS NO SUCH DATUM: there a step goes on with 0 in the stead of a
challenge that lacks or drew no element (`challengesOr0`), and what it yields means nothing: that
enough has been heard is a premise of whoever says what the rows are. WHERE THAT 0 CAN FLOW: into
the point at which `foldEnd` folds, so into what the fold leaves (the folded main row and the two
mask rows, messages and tails; not the kept members, which read no challenge); from there, by
Carrying.lean's `mainRows`, into THE ENTRIES OF A CARRYING MESSAGE's MAIN ROWS THAT ARE NO PAD's,
and so on through the later folds. IT REACHES NO COIN's PLACE: `messageRows`
(Honest/K2/Sending.lean) asks first whether a coin stands at a place: a tail, a pad's place, a mask
row's entry, a fresh mask's coefficient is the stretch's coin, whatever the data is.
REFUSED ARE: a fold whose numbers of challenges, or whose number of row variables, are not as many
as the group's layout has; own messages that are not marked one by one; a first sending without a
message; a switch without just one target for each kept member; a switch whose kept members, by its
own sizes, are not those that the fold in front left (shape for shape: between two segments, and by
`closingFor` at the switch's own place); a switch whose sizes do not fit (`Sizes.roomy`,
Honest/K2/Part.lean); a group whose shapes do not fit a fold (`groupFits`); whatever `messageRows`
refuses.

Limits. Nothing holds a `SegmentPub` against a plan. `SegmentPub.sizes` names the codes of the group
that the switch closes, and they are taken for the segment's own group's too: a request has one pair
of codes for all its groups (`ReqFrame.beginLink`, OnBytes/Iop/Req.lean). Each step reckons all that
its fold leaves, at once, whether or not it is read. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Sending
import Johnson.Desc.K2.Honest.FoldEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Left Sizes GroupMember foldEnd groupLayout mainRows zeroG)
open Johnson.Prover.Send (Rows)

/-- **What is public of a segment**, for whoever makes its group's rows anew. -/
structure SegmentPub where
  /-- the sizes of the switch that leads into the segment. At the first segment the codes and the
  two codes' numbers alone are read -/
  sizes : Sizes
  /-- the messages of each of its sendings, moment by moment, without what rides at the start. In
  the first: the carrying message and the copies (none at the first segment), the own messages of
  moment 0, the closing fold's fresh mask -/
  sent : List (Array OnBytes.OracleNotice)
  /-- for each own message, in the order of sending: whether a later segment reads it -/
  ownKept : List Bool
  /-- the closing fold's row variables -/
  foldVars : Nat
  /-- the numbers, among the chain's challenges, of the closing fold's, in the order of its rounds
  -/
  gamma : List Nat

/-- How many oracle messages the segment has sent. -/
def SegmentPub.messages (S : SegmentPub) : Nat := S.sent.foldl (fun n a => n + a.size) 0

/-- **A group's rows.** -/
structure GroupRows where
  /-- the members, in the order of sending -/
  members : List GroupMember
  /-- each member in full -/
  rows : List Rows
  /-- the closing fold's fresh mask in full; nothing where its stretch is not handed over -/
  fresh : Option Rows

/-- **A segment's group's rows.** prev: what the fold before left; nothing at the first segment.
prevKept: the shapes of the kept members that it left.
own: the segment's own messages' main rows, by the message's number in the segment. k: the carried
stretches. base: the number of the segment's first. withFresh: the fresh mask's stretch is among
them, at its place in the order of sending; else the later messages' stretches follow at once. -/
def segmentGroupRows (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape)
    (own : Nat → Nat → Nat → Cb.Gl.E) (k : Nat → Except String Stretch) (base : Nat)
    (withFresh : Bool) : Except String GroupRows := do
  let codes := S.sizes.codes
  let first := S.sent.headD #[]
  if first.isEmpty then throw "a segment's first sending holds no message"
  if prev.isSome && S.sizes.kept.length != S.sizes.target.kept.size then
    throw "a switch has not one target for each kept member"
  if prev.isSome && S.sizes.kept != prevKept then
    throw "a switch's kept members are not those that the fold in front left"
  if prev.isSome && !S.sizes.roomy then
    throw "the sizes do not fit a switch"
  let freshNo := first.size - 1
  let head := if prev.isSome then 1 + S.sizes.kept.length else 0
  let dataAt (n : Nat) : Nat → Nat → Cb.Gl.E :=
    match prev with
    | some W => mainRows S.sizes W own n
    | none => own n
  -- shape and main rows of the members, in the order of sending
  let inFirst := (first.toList.take freshNo).zipIdx.map fun x => (x.1.shape, dataAt x.2)
  let later := (S.sent.drop 1).foldl
    (fun (s : List (OnBytes.OracleShape × (Nat → Nat → Cb.Gl.E)) × Nat) a =>
      (s.1 ++ a.toList.zipIdx.map fun x => (x.1.shape, own (s.2 + x.2)), s.2 + a.size))
    ([], freshNo - head)
  let flags :=
    (if prev.isSome then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept
  if flags.length != inFirst.length + later.1.length then
    throw "a segment's own messages are not marked one by one"
  let skip := if withFresh then 1 else 0
  let rows₀ ← inFirst.zipIdx.mapM fun x =>
    (k (base + x.2)).bind (messageRows table codes x.1.1 none x.1.2)
  let fresh ←
    if withFresh then
      ((k (base + freshNo)).bind
        (messageRows table codes (first.getD freshNo default).shape (some S.foldVars)
          fun _ _ => zeroG)).map some
    else pure none
  let rows₁ ← later.1.zipIdx.mapM fun x =>
    (k (base + freshNo + skip + x.2)).bind (messageRows table codes x.1.1 none x.1.2)
  pure ⟨(((inFirst ++ later.1).map (·.1)).zip flags).map fun x => ⟨x.1, x.2⟩, rows₀ ++ rows₁, fresh⟩

/-- What a fold leaves, reckoned once and kept in arrays, so that a later step's reads do not go
back through all segments. c, z: the group's two codes. kept: the kept members' shapes. Beyond these
sizes: 0. -/
def frozenLeft (c z : OnBytes.Code) (kept : List OnBytes.OracleShape) (W : Left) : Left :=
  let main := (Array.range c.ell).map W.main
  let mainTail := (Array.range c.r).map W.mainTail
  let mask := (Array.range 2).map fun r => (Array.range z.ell).map (W.mask r)
  let maskTail := (Array.range 2).map fun r => (Array.range z.r).map (W.maskTail r)
  let rows := kept.toArray.zipIdx.map fun x =>
    (Array.range x.1.mainRows).map fun b =>
      ((Array.range c.ell).map ((W.kept x.2).main b), (Array.range c.r).map ((W.kept x.2).tail b))
  { main := (main.getD · zeroG), mainTail := (mainTail.getD · zeroG)
    mask := fun r i => (mask.getD r #[]).getD i zeroG
    maskTail := fun r q => (maskTail.getD r #[]).getD q zeroG
    kept := fun i =>
      ⟨fun b j => (((rows.getD i #[]).getD b (#[], #[])).1).getD j zeroG,
        fun b q => (((rows.getD i #[]).getD b (#[], #[])).2).getD q zeroG⟩ }

/-- The first elements that the challenges of these numbers drew. A refusal where a challenge lacks
or drew no element. -/
def challengesAt (heard : List Fmt.Drawn) (numbers : List Nat) : Except String (List Cb.Gl.E) :=
  numbers.mapM fun i =>
    match (heard.drop i).head?.bind (·.elems.head?) with
    | some x => .ok (OnBytes.Slice.toE x)
    | none => .error "a fold's challenge lacks"

/-- The same, TOTAL: 0 where a challenge lacks or drew no element. For a caller that must return at
every list of challenges: what it makes there means nothing. As many elements as numbers. -/
def challengesOr0 (heard : List Fmt.Drawn) (numbers : List Nat) : List Cb.Gl.E :=
  numbers.map fun i =>
    match (heard.drop i).head?.bind (·.elems.head?) with
    | some x => OnBytes.Slice.toE x
    | none => zeroG

/-- **A group's shapes fit a fold**: THE VERIFIER's OWN TWO TESTS, CALLED (`foldShapeFits`,
`foldMaskFits`, Johnson/Desc/Own/Fold.lean), at the statement of which `groupLayout`
(Johnson/Desc/K2/Honest/FoldEnd.lean) makes the layout, with the fresh mask laid behind the members.
What the honest text needs of them, so that `foldEnd` folds no row of zeros in a row's stead and
drops none in silence: each member's rows have the group's codes and lie inside the layout's two
tables; the fresh mask has no main row and 2 ^ h mask rows of the group's mask code. What they ask
beyond that: the two codes are in their lists, the mask code not longer than the main code and long
enough for the hiding polynomial; some member has a main row to fold; the fresh mask has no sample.
THAT THE TESTS AT THIS STAND-IN ARE THE TESTS AT A RUN's OWN STATEMENT IS NOT SHOWN. -/
def groupFits (codes : OnBytes.Codes) (code maskCode : Nat) (ms : List GroupMember)
    (fresh : OnBytes.OracleShape) : Bool :=
  let St : OnBytes.Statement :=
    { codes := codes
      oracles := ((ms.map fun (m : GroupMember) => ({ shape := m.shape } : OnBytes.Oracle)) ++
        [({ shape := fresh } : OnBytes.Oracle)]).toArray }
  let F : OnBytes.FoldShape :=
    { code := code, maskCode := maskCode, layout := groupLayout codes code maskCode ms }
  VerifiableInference.Desc.Own.foldShapeFits St F &&
    VerifiableInference.Desc.Own.foldMaskFits St F ms.length

/-- **What the fold that closes one segment leaves**, with the shapes of the kept members. As
`segmentGroupRows`; heard: the challenges heard.
"`R.rows.getD · zeroMessage` and `R.fresh.getD zeroMessage` are for totality alone: `segmentRows`
returns as many rows as members, and at withFresh := true a fresh mask; a message of zeros would
have 0 at every coin's place. No lemma says that the defaults are not reached." Besides: two
files that this library may not hold speak of what `segmentGroupRows` returns, not of the defaults:
`segmentRows_count` (Honest/K2/Law/GroupCount.lean): where `segmentGroupRows` returns, as many rows as
members · `segmentRows_mask` (Honest/K2/Law/RowsOfSegment.lean): at withFresh := true a fresh mask
is there. -/
def segmentLeft (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape)
    (own : Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    (k : Nat → Except String Stretch) (base : Nat) :
    Except String (Left × List OnBytes.OracleShape) := do
  let codes := S.sizes.codes
  let R ← segmentGroupRows table S prev prevKept own k base true
  let γ := challengesOr0 heard S.gamma
  let vars := (groupLayout codes S.sizes.code S.sizes.maskCode R.members).k
  if vars != S.foldVars || γ.length != vars then
    throw "a fold has not as many challenges as its group has row variables"
  if !groupFits codes S.sizes.code S.sizes.maskCode R.members
      (((S.sent.headD #[]).back?.map (·.shape)).getD default) then
    throw "a group's shapes do not fit a fold"
  let kept := (R.members.filter (·.kept)).map (·.shape)
  pure (frozenLeft (codes.base.getD S.sizes.code default)
    (codes.mask.getD S.sizes.maskCode default) kept
    (foldEnd codes S.sizes.code S.sizes.maskCode R.members (R.rows.getD · zeroMessage)
      (R.fresh.getD zeroMessage) γ), kept)

/-- The steps from a segment on: what the fold of the last leaves, with the number of the next
stretch; nothing where there is no segment. j: the first one's number. -/
def closingFrom (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) :
    List SegmentPub → (j base : Nat) → Option (Left × List OnBytes.OracleShape) →
      Except String (Option (Left × List OnBytes.OracleShape) × Nat)
  | [], _, base, prev => .ok (prev, base)
  | S :: rest, j, base, prev =>
    (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind
      fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)

/-- **What the fold of the last of these segments leaves.** segs: the segments in front of the
switch, from the first on. heard: the challenges in front of the switch. -/
def closingOf (table : FreshTable) (segs : List SegmentPub)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    (k : Nat → Except String Stretch) : Except String Left :=
  (closingFrom table own heard k segs 0 0 none).bind fun x =>
    match x.1 with
    | some W => .ok W.1
    | none => .error "no segment stands in front of the switch"

/-- **The same for the switch at a place**: next: the kept members' shapes by that switch's own
sizes. A refusal where they are not those that the fold left. -/
def closingFor (table : FreshTable) (segs : List SegmentPub) (next : List OnBytes.OracleShape)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    (k : Nat → Except String Stretch) : Except String Left :=
  (closingFrom table own heard k segs 0 0 none).bind fun x =>
    match x.1 with
    | some W =>
      if W.2 != next then .error "a switch's kept members are not those that the fold in front left"
      else .ok W.1
    | none => .error "no segment stands in front of the switch"

/-- **The rows of the group of the last of these segments**, for whoever closes it. The stretches:
those of all messages of the segments before, fresh masks among them; then those of the last
segment's messages WITHOUT its own fresh mask. -/
def groupRowsOf (table : FreshTable) (segs : List SegmentPub)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    (k : Nat → Except String Stretch) : Except String GroupRows :=
  match segs.getLast? with
  | none => .error "no segment is named"
  | some S =>
    (closingFrom table own heard k segs.dropLast 0 0 none).bind fun x =>
      segmentGroupRows table S (x.1.map (·.1)) ((x.1.map (·.2)).getD []) (own (segs.length - 1)) k x.2
        false

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.SegmentPub
#print axioms ProofFile.Honest.K2.SegmentPub.messages
#print axioms ProofFile.Honest.K2.GroupRows
#print axioms ProofFile.Honest.K2.segmentGroupRows
#print axioms ProofFile.Honest.K2.frozenLeft
#print axioms ProofFile.Honest.K2.challengesAt
#print axioms ProofFile.Honest.K2.challengesOr0
#print axioms ProofFile.Honest.K2.groupFits
#print axioms ProofFile.Honest.K2.segmentLeft
#print axioms ProofFile.Honest.K2.closingFrom
#print axioms ProofFile.Honest.K2.closingOf
#print axioms ProofFile.Honest.K2.closingFor
#print axioms ProofFile.Honest.K2.groupRowsOf

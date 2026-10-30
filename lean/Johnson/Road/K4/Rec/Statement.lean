-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/Statement.lean: THE STATEMENTS, AND NO PROOF: "AT AN UNMARKED STATEMENT INSIDE
THE TABLE OF JOINTS' PROMISE AT A BORDER, THE OPEN SEGMENT's PART OF THE RECORD READS AS THE PLAN
SAYS": frame, layout, list of arrays, book, bits, the ledger's arrays. Definitions alone
(`def … : Prop`). The proofs stand beside: Johnson/Road/K4/Rec/Proofs.lean.

WHO SPENDS THEM. Two readings of the committed cells must be shown to be one behind K4's block: the
table's (`dataQ`, Johnson/Desc/Sound/FormsQ.lean: through the record's own frame, layout, book and
statement) and the caller's (through the plan). The conditions under which they are one speak, in
one half, of the record's part. With these statements each such condition becomes a test on the
plan's letters.

THE FORM. `AtBorder N Mg Z links ps k b A`: b stands inside the promise at border k (`onQ`,
Johnson/Desc/Sound/BordersQ.lean), bears no mark, and A is the open segment's part of b's record
(`K9.segAt?`). `OpenAt Mg links ps k q`: the public item q is open at border k, at the meaning's
own filling of the door: A TEST ON THE PLAN once `Mg.more` is a term. Each statement has EQUATIONS
OF `Mg`'s FIELDS as premises, one to four: "the item's test IS its owner's text".

  | the statement | what it says of A | the items that must be open | the equations |
  | `LayoutIs` | the link's own layout, its frame's shape are the plan's | frame.liveIs m | eLive |
  | `ArraysAre` | the link's list of arrays is the plan's | linkFresh m | eFresh |
  | `SeatIs` | `seatAt own A.d.book o` is `seatP` | K12.seatsCarried | eSeats |
  | `RowBitsAre` | `A.d.st.rowBits o part` is `rowBitsP` | K12.msgShapes | eShapes |
  | `PlaceBitsAre` | `A.d.st.placeBits o part` is `placeBitsP` | K12.msgShapes | eShapes, eCodes |
  | `WhereIs` | the frame's `whereIs` is `whereIsP`; its link is m | frame.sentIs m | eSent |
  | `MaskIs` | `maskOracle` of the frame is `maskP` | frame.sentIs m, frame.liveIs m | two |
  | `MaskSeatIs` | `K9.maskSeat own A` is `maskSeatP` | these two, K12.seatsCarried | the three |
  | `ArrayInIs` | `K9.arrayIn own A t` is `arrayInP` | all of frame.liveIs m, linkFresh m,
      frame.sentIs m, K12.seatsCarried | the four |
  | `Moment1Is` | `K9.atMoment1 A c X` is `atMoment1P` | frame.sentIs m, frame.liveIs m | two |
  | `TreesAre` | the look of the ledger's arrays is the plan's | ledger.treesAre m | eTrees |
n, the number of messages, is `N.msgsAt ps[k]?` throughout: by the promise's clause on the book.

THE OWNERS' TEXTS. eSeats, eShapes: at the owners' own tests, imported. eSent, eTrees: at
Johnson/Desc/First/FillSent.lean's. eLive, eFresh: THE TEST's TEXT IS WRITTEN OUT HERE (the owner's
file, Johnson/Desc/First/Look/K3FillCode.lean, `liveIsC` and `linkFreshC`, is not beneath this one):
that the text is the owner's is held under K4Means (Rec/OfMeans.lean). eCodes: an implication, not
an equation: "in order" gives that the statement's codes are the plan's.

Limits. SENTENCES: NOTHING IS PROVED HERE. EVERY EQUATION IS A PREMISE: shown at no term here
(eSent's and eTrees' shape at pubAll: `pubAll_more_sentIs`, `pubAll_more_treesAre`,
Johnson/Desc/First/PubAllAt.lean).
frame.sentIs AND ledger.treesAre LIE IN pubAll, HAVE HAD NO RUN, AND IT IS NOT SHOWN BUT ON PREMISES
THAT BLOCKS MAKE OR KEEP THEM (made_sent); "K12.msgShapes" has run nowhere by its own head. Where no
unmarked record meets the promise all hold for nothing. K04_law, the law of K4's block itself, IS
NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.RecordPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers pubSets)
open VerifiableInference.Desc.First.FillSent (SentData TreeLook treeLook sentIsB treesAreB whereIsP
  maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP maskSeatP arrayInP
  atMoment1P)
open VerifiableInference.Desc.K9 (segAt? seatAt maskSeat arrayIn atMoment1)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.K12.Door (atFirstSeats atFirstShapes)
open VerifiableInference.Desc.Sound (Frame onQ)

/-- The open segment's part. -/
abbrev Part9 : Type := VerifiableInference.Desc.K9.Part

/-- The plan's list of (tree, part) and of the trees' shapes. -/
abbrev LaidP : Type := VerifiableInference.Desc.K12.Door.Laid

section
variable {P W : Type} {Fr : Frame}

/-- **An unmarked statement inside the promise at border k, with the open segment's part.** -/
structure AtBorder (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (b : S × Fr.E.Str) (A : Part9) : Prop where
  on : onQ N Mg links ps (fun s => (Z, s)) k b
  unmarked : b.1.failed = none
  part : segAt? b.1 = some A

/-- The public item q is open at border k. -/
def OpenAt (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Pub) : Prop :=
  q ∈ (pubSets Mg.more links ps)[k]?.getD []

/-! ## The equations of the meaning's fields, each by name -/

/-- eLive: what the item frame.liveIs says. -/
def ELive (Mg : Meaning P W) (shape : Params.ReqShape) (layout : Params.ReqLayout) : Prop :=
  ∀ (m : ℕ) (a : P × S), Mg.pub (.more (some m) "frame.liveIs") a =
    (decide (a.2.live.frame.shape = shape) && decide (a.2.live.rows.layout = layout))

/-- eFresh: what the item linkFresh says. -/
def EFresh (Mg : Meaning P W) (arrs : ℕ → Array (ℕ × String)) : Prop :=
  ∀ (m : ℕ) (a : P × S), Mg.pub (.linkFresh m) a =
    ((a.2.tl?.bind (·.heard)).isNone && a.2.link?.any fun L => L.arrayOf == arrs m)

/-- eSeats: what the item K12.seatsCarried says. -/
def ESeats (Mg : Meaning P W) (L : LaidP) : Prop :=
  ∀ a : P × S, Mg.pub (.more none "K12.seatsCarried") a = atFirstSeats L a.2

/-- eShapes: what the item K12.msgShapes says. -/
def EShapes (Mg : Meaning P W) (M : List OracleShape) : Prop :=
  ∀ a : P × S, Mg.pub (.more none "K12.msgShapes") a = atFirstShapes M a.2

/-- eCodes: "in order" gives that the statement's codes are the plan's. -/
def ECodes (Mg : Meaning P W) (cs : Codes) : Prop :=
  ∀ a : P × S, Mg.inOrder a = true → a.2.st.codes = cs

/-- eSent: what the item frame.sentIs says. -/
def ESent (Mg : Meaning P W) (d : SentData) : Prop :=
  ∀ (m : ℕ) (a : P × S), Mg.pub (.more (some m) "frame.sentIs") a = sentIsB d m a.2

/-- eTrees: what the item ledger.treesAre says. -/
def ETrees (Mg : Meaning P W) (d : SentData) : Prop :=
  ∀ (m : ℕ) (a : P × S), Mg.pub (.more (some m) "ledger.treesAre") a = treesAreB d m a.2

end

/-! ## The statements -/

/-- Under eLive, frame.liveIs m open: the link's own layout and its frame's shape. -/
def LayoutIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (shape : Params.ReqShape)
    (layout : Params.ReqLayout),
    ELive Mg shape layout → OpenAt Mg links ps k (.more (some m) "frame.liveIs") →
    AtBorder N Mg Z links ps k b A →
    A.L.check.rows.layout = layout ∧ A.L.check.frame.shape = shape

/-- Under eFresh, linkFresh m open: the link's list of arrays. -/
def ArraysAre : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (arrs : ℕ → Array (ℕ × String)),
    EFresh Mg arrs → OpenAt Mg links ps k (.linkFresh m) → AtBorder N Mg Z links ps k b A →
    A.L.arrayOf = arrs m

/-- Under eSeats, K12.seatsCarried open: a message's seat by the book. -/
def SeatIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (b : S × Fr.E.Str) (A : Part9) (L : LaidP),
    ESeats Mg L → OpenAt Mg links ps k (.more none "K12.seatsCarried") →
    AtBorder N Mg Z links ps k b A →
    ∀ (own : List (ℕ × ℕ)) (o : ℕ),
      seatAt own A.d.book o = seatP own L.places (N.msgsAt ps[k]?) o

/-- Under eShapes, K12.msgShapes open: a table's row bits. -/
def RowBitsAre : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (b : S × Fr.E.Str) (A : Part9) (M : List OracleShape),
    EShapes Mg M → OpenAt Mg links ps k (.more none "K12.msgShapes") →
    AtBorder N Mg Z links ps k b A →
    ∀ (o : ℕ) (part : OnBytes.Part), A.d.st.rowBits o part = rowBitsP M (N.msgsAt ps[k]?) o part

/-- Under eShapes and eCodes, K12.msgShapes open: a table's place bits. -/
def PlaceBitsAre : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (b : S × Fr.E.Str) (A : Part9) (M : List OracleShape) (cs : Codes),
    EShapes Mg M → ECodes Mg cs → OpenAt Mg links ps k (.more none "K12.msgShapes") →
    AtBorder N Mg Z links ps k b A →
    ∀ (o : ℕ) (part : OnBytes.Part),
      A.d.st.placeBits o part = placeBitsP cs M (N.msgsAt ps[k]?) o part

/-- Under eSent, frame.sentIs m open: where the frame finds a message; the frame's link. -/
def WhereIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData),
    ESent Mg d → OpenAt Mg links ps k (.more (some m) "frame.sentIs") →
    AtBorder N Mg Z links ps k b A →
    A.L.check.frame.link = m ∧
      ∀ born message : ℕ, A.L.check.frame.whereIs born message = whereIsP d m born message

/-- Under eSent and eLive, both items open: the message with the mask row. -/
def MaskIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData)
    (shape : Params.ReqShape) (layout : Params.ReqLayout),
    ESent Mg d → ELive Mg shape layout → OpenAt Mg links ps k (.more (some m) "frame.sentIs") →
    OpenAt Mg links ps k (.more (some m) "frame.liveIs") → AtBorder N Mg Z links ps k b A →
    maskOracle A.L.check.frame = maskP shape d m

/-- Under eSent, eLive and eSeats, the three items open: the mask row's seat. -/
def MaskSeatIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData)
    (shape : Params.ReqShape) (layout : Params.ReqLayout) (L : LaidP),
    ESent Mg d → ELive Mg shape layout → ESeats Mg L →
    OpenAt Mg links ps k (.more (some m) "frame.sentIs") →
    OpenAt Mg links ps k (.more (some m) "frame.liveIs") →
    OpenAt Mg links ps k (.more none "K12.seatsCarried") → AtBorder N Mg Z links ps k b A →
    ∀ own : List (ℕ × ℕ),
      maskSeat own A = maskSeatP shape d own L.places (N.msgsAt ps[k]?) m

/-- Under eSent, eLive, eFresh and eSeats, the four items open: "the array is there". -/
def ArrayInIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData)
    (shape : Params.ReqShape) (layout : Params.ReqLayout) (arrs : ℕ → Array (ℕ × String))
    (L : LaidP),
    ESent Mg d → ELive Mg shape layout → EFresh Mg arrs → ESeats Mg L →
    OpenAt Mg links ps k (.more (some m) "frame.sentIs") →
    OpenAt Mg links ps k (.more (some m) "frame.liveIs") → OpenAt Mg links ps k (.linkFresh m) →
    OpenAt Mg links ps k (.more none "K12.seatsCarried") → AtBorder N Mg Z links ps k b A →
    ∀ (own : List (ℕ × ℕ)) (t : ℕ),
      arrayIn own A t = arrayInP layout (arrs m) d own L.places (N.msgsAt ps[k]?) m t

/-- Under eSent and eLive, both items open: "the array is of the second sending". -/
def Moment1Is : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData)
    (shape : Params.ReqShape) (layout : Params.ReqLayout),
    ESent Mg d → ELive Mg shape layout → OpenAt Mg links ps k (.more (some m) "frame.sentIs") →
    OpenAt Mg links ps k (.more (some m) "frame.liveIs") → AtBorder N Mg Z links ps k b A →
    ∀ (c : ℕ × String) (X : Params.ReqArray), atMoment1 A c X = atMoment1P shape m c X

/-- Under eTrees, ledger.treesAre m open: the look of the ledger's arrays. -/
def TreesAre : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (d : SentData),
    ETrees Mg d → OpenAt Mg links ps k (.more (some m) "ledger.treesAre") →
    AtBorder N Mg Z links ps k b A → A.F.trees.toList.map treeLook = d.trees m

end OnBytes.Road.K4.Rec

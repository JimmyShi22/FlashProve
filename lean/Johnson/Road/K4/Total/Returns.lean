-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/Returns.lean: THE STATEMENT, AND NO PROOF: "BEHIND K4's HEARING ITS TWO RUNS
OF CLAIMS RETURN". Definitions alone: the law as a sentence (`RunsReturn`), every premise by name,
and the parts into which it is cut, each a sentence of its own. The proofs stand in the files beside
(Total/…), one a part.

WHY THE LAW IS OWED, AND WHO SPENDS IT. Every law on K4's runs (`formsFrontWith`, `formsBack`:
OnBytes/Desc/First/K4/Plain.lean) begins "where the run returns". K4's block's decision is its
hearing alone (Johnson/Desc/First/K4/Block.lean); the runs are called at the batching, five blocks
on. THE USER: the table of joints' public item formsInT m 3 "own", which K4's row must MAKE behind
its yes: its test asks the run itself at the border's record and is false where the run is silent.
FOR THAT TEST THE RETURN IS NEEDED, NOT ENOUGH: what each form names must be there too.

THE LAW (`RunsReturn`). hear engFl P hp g fo F t = some (o, G, u) · `Asks` · `Fit o G Fb` · Pr of
P's layout and reads: then `formsFrontWith rows Pr g o Fb` returns, at either form of the run;
`formsBack o Fb` returns; and `formsBack` returns at the ledger that "front" leaves too. AT EVERY
LEDGER Fb WITH `Fit`: so it serves a reader that calls each run at a border's record AND a law that
calls "back" from "front"'s ledger.

THE PREMISES, EACH WITH ITS PAYER.
  `Fit o G Fb` (on the ledger at which a run is called): arrays of the right sizes · later than the
    hearing's ledger G · the three windows (of the row products' token sumcheck, of the lookup's
    leaves' sumcheck, of the merge) there and free. PAYER: `FitBehind` at Fb := G; at a later
    border: whoever carries the promise past the blocks between (BY READING none of them lays a
    window; no theorem).
  `Asks`: sized: F has arrays of the right sizes (the item ledger) · leavesReady, leavesBelow: the
    lookup's leaves' sumcheck has its four marks, and its window lies below F's next free number
    (THE LOOKUP's law: what its hearing leaves: by reading, its record has three of the four
    marks and the window's place; "a variable" is no field of it yet) · skel, y₀, rd₀, member: THE
    PUBLIC HALF, see next.

THE PUBLIC HALF, AND THE MEMBER. Whether the listing `front` returns hangs on no
value that a prover sends or a verifier draws: it reads names and lengths: of the environment o.v
the layout, the tables' places and the reads' number of columns (`EnvSkel`: NOT the whole of o.v:
its field zk holds drawn points); whether the second token sumcheck's record is there; three lengths
of challenge vectors; the lookup's shape (`Skel`: six clauses). `FrontSkel` says so: at two records
of one skeleton `front` returns at both or at neither. SO THE LAW ASKS ONE RECORD o₀ OF o's SKELETON
AT WHICH `front` RETURNS (member). o₀ NEED BE NO RETURN OF A HEARING: any record of the skeleton
serves, a made-up one too. BY A RUN such records are there: at one honest proof of each of two sizes
both runs return behind K4's yes at every layers' place (2 | 12), and a control rings. No theorem
says that a member exists; `HearSkel` says that any two returns of the hearing at one plan
(whatever the requests' tokens), from lookups of one shape, have one skeleton: so one honest run's
record is a member for every transcript at its plan.

THREE PUBLIC RECORDS. K4's block hears at its own public record WITH THE REQUEST's TOKENS LAID IN,
and calls the run "front" at its own: two terms. The member is shown at a third (another request's).
`FrontPub`, `RunPub`: of the public record the listing and the run read the layout and the list of
reads alone: so the three may differ in all else.

THE PARTS. `ShownPart` · `ReadyVPart` · `ApartPart` · `FrontPub` · `RunPub` · `FrontSkel` (cut by
listing: `NormsSkel` · `RowsSkel` · `TermsSkel` · `GatedSkel` · `OneHotSkel` · `PlanesSkel` ·
`EmbedSkel`) · `BackPart` · `FitBehind` · `HearSkel`.

Limits. SENTENCES: NOTHING IS PROVED HERE. One direction is meant: that the runs return, not what a
form is worth. The member is a premise. K04_law, the law of K4's block itself, IS NOT PROVED.
Nothing on soundness.
-/
import OnBytes.Desc.First.K4.ClaimsLaws
import Johnson.Road.K4.Slots.HearFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard Env)
open OnBytes.PscRun (Sized Filled Later)

/-- The sumcheck's four marks, under which its own claim can be made: no claim made yet; begun; a
variable; as many challenges as variables. -/
def Ready (p : Psc) : Prop :=
  p.rowMade = false ∧ p.started = true ∧ p.vars.isEmpty = false ∧ p.r.size = p.vars.size

/-- The sumcheck's window is there and free in the ledger. -/
def WinFree (p : Psc) (F : Fork) : Prop :=
  ∀ i, i < p.walk.1.length → p.first + i < F.ns ∧ ¬ Filled F (p.first + i)

/-- **The ledger at which a run is called.** G: the ledger that the hearing left. -/
structure Fit (o : Own) (G Fb : Fork) : Prop where
  sized : Sized Fb
  later : Later G Fb
  winV : WinFree o.H.tV.p Fb
  winL : WinFree o.H.fo.leaves Fb
  winM : WinFree o.wo.toWsMerged.p Fb

/-- What of an environment a listing's return hangs on: the layout, the places of the families of
tables, the number of columns of the array of the reads. NOT THE WHOLE ENVIRONMENT: its field zk
holds the lookup's points, which are DRAWN: two transcripts have two. -/
structure EnvSkel (v v₀ : Env) : Prop where
  y : v.y = v₀.y
  tab : v.tab = v₀.tab
  K3 : v.K3 = v₀.K3

/-- **What of a record the listing's return hangs on.** -/
structure Skel (o o₀ : Own) : Prop where
  v : EnvSkel o.v o₀.v
  tT : o.H.tT.isSome = o₀.H.tT.isSome
  wpl : o.H.wpl.r.size = o₀.H.wpl.r.size
  hd : o.hd.r.size = o₀.hd.r.size
  hd2 : o.hd2.map (·.r.size) = o₀.hd2.map (·.r.size)
  shape : o.H.fo.shape = o₀.H.fo.shape

/-- **What is asked beside the hearing's return.** P: the public record at which the hearing ran.
P₀: the public record at which the member is shown: of one layout and one list of reads with P
(their tokens may differ). -/
structure Asks (rows : Bool) (P P₀ : Pub) (g : ℕ) (fo : Forest.Heard) (F : Fork) (o o₀ : Own) :
    Prop where
  sized : Sized F
  leavesReady : Ready fo.leaves
  leavesBelow : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next
  skel : Skel o o₀
  y₀ : P₀.y = P.y
  rd₀ : P₀.rd = P.rd
  member : ∃ a b, (front rows P₀ g o₀ a b).isSome = true

/-- **THE LAW.** THREE PUBLIC RECORDS: P: at which the hearing ran (K4's block lays the request's
tokens into its own) · Pr: at which the run "front" is called (the block's own) · P₀: the member's.
-/
def RunsReturn : Prop :=
  ∀ (rows : Bool) (P Pr P₀ : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G Fb : Fork)
    (t u : Tape) (o o₀ : Own), hear engFl P hp g fo F t = some (o, G, u) →
    Pr.y = P.y → Pr.rd = P.rd → Asks rows P P₀ g fo F o o₀ → Fit o G Fb →
    (∃ fs G₁, formsFrontWith rows Pr g o Fb = some (fs, G₁) ∧
      ∃ fb G₂, formsBack o G₁ = some (fb, G₂)) ∧
    ∃ fb Gb, formsBack o Fb = some (fb, Gb)

/-! ## The parts -/

/-- The end values of the row products' token sumcheck are shown at every later ledger with arrays
of the right sizes. -/
def ShownPart : Prop :=
  ∀ (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G Fb : Fork) (t u : Tape) (o : Own),
    Sized F → hear engFl P hp g fo F t = some (o, G, u) → Later G Fb → Sized Fb →
    ∀ i, i < 4 * P.y.NI → ∃ e, Fb.shown (o.H.tV.sEnd + i) = some e

/-- The row products' token sumcheck has its four marks. -/
def ReadyVPart : Prop :=
  ∀ (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G : Fork) (t u : Tape) (o : Own),
    hear engFl P hp g fo F t = some (o, G, u) → Ready o.H.tV.p

/-- The windows lie apart: the row products' from F's next free number on and in front of the
merge's. (With `Asks.leavesBelow`: the three are disjoint.) -/
def ApartPart : Prop :=
  ∀ (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G : Fork) (t u : Tape) (o : Own),
    Sized F → hear engFl P hp g fo F t = some (o, G, u) →
    o.H.fo = fo ∧ F.next ≤ o.H.tV.p.first ∧
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ o.wo.toWsMerged.p.first

/-- Each listing returns at two records of one skeleton, or at neither. -/
def NormsSkel : Prop := ∀ (P : Pub) (o o₀ : Own), Skel o o₀ →
  (normsForms P o.v o.H).isSome = (normsForms P o₀.v o₀.H).isSome
def RowsSkel : Prop := ∀ (o o₀ : Own), Skel o o₀ →
  (rowsForms o.v o.H).isSome = (rowsForms o₀.v o₀.H).isSome
def TermsSkel : Prop := ∀ (o o₀ : Own), Skel o o₀ →
  (termsForms o.v o.H).isSome = (termsForms o₀.v o₀.H).isSome
def GatedSkel : Prop := ∀ (P : Pub) (o o₀ : Own), Skel o o₀ →
  (gatedForms P o.v o.hd o.hd2).isSome = (gatedForms P o₀.v o₀.hd o₀.hd2).isSome
def OneHotSkel : Prop := ∀ (o o₀ : Own), Skel o o₀ →
  (oneHotForms o.v).isSome = (oneHotForms o₀.v).isSome
def PlanesSkel : Prop := ∀ (o o₀ : Own), Skel o o₀ →
  (planesParts o.v o.H.fo).isSome = (planesParts o₀.v o₀.H.fo).isSome
def EmbedSkel : Prop := ∀ (o o₀ : Own), Skel o o₀ →
  (embeddingForm o.v o.H o.sVE).isSome = (embeddingForm o₀.v o₀.H o₀.sVE).isSome

/-- Of the public record the listing and the run read the layout and the list of reads alone. -/
def FrontPub : Prop :=
  ∀ (rows : Bool) (P Pr : Pub) (g : ℕ) (o : Own) (a b : Aff), Pr.y = P.y → Pr.rd = P.rd →
    front rows Pr g o a b = front rows P g o a b
def RunPub : Prop :=
  ∀ (rows : Bool) (P Pr : Pub) (g : ℕ) (o : Own) (F : Fork), Pr.y = P.y → Pr.rd = P.rd →
    formsFrontWith rows Pr g o F = formsFrontWith rows P g o F

/-- The whole listing. -/
def FrontSkel : Prop :=
  ∀ (rows : Bool) (P : Pub) (g : ℕ) (o o₀ : Own) (a b a₀ b₀ : Aff), Skel o o₀ →
    (front rows P g o a b).isSome = (front rows P g o₀ a₀ b₀).isSome

/-- "back" returns wherever the merge's window is there and free. -/
def BackPart : Prop :=
  ∀ (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G Fb : Fork) (t u : Tape) (o : Own),
    hear engFl P hp g fo F t = some (o, G, u) → Sized Fb → WinFree o.wo.toWsMerged.p Fb →
    ∃ fs Gb, formsBack o Fb = some (fs, Gb)

/-- **The ledger that the hearing leaves has `Fit`**: from a sized ledger whose slots from its next
free number on are free, and in which the lookup's leaves' window, below that number, is there and
free. -/
def FitBehind : Prop :=
  ∀ (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) (F G : Fork) (t u : Tape) (o : Own),
    Sized F → (∀ j, F.next ≤ j → ¬ Filled F j) → WinFree fo.leaves F →
    fo.leaves.first + fo.leaves.walk.1.length ≤ F.next →
    hear engFl P hp g fo F t = some (o, G, u) → Fit o G G

/-- Two returns of the hearing at one plan, from lookups of one shape, have one skeleton. TWO PUBLIC
RECORDS P, P₀: K4's block hears at its public record WITH THE REQUEST's TOKENS LAID IN: two requests
have two: what must agree is the layout, the reads and the groups' lists. -/
def HearSkel : Prop :=
  ∀ (P P₀ : Pub) (hp : HPlan2) (g : ℕ) (fo fo₀ : Forest.Heard) (F G F₀ G₀ : Fork)
    (t u t₀ u₀ : Tape) (o o₀ : Own), P.y = P₀.y → P.rd = P₀.rd → P.tails = P₀.tails →
    fo.shape = fo₀.shape → hear engFl P hp g fo F t = some (o, G, u) →
    hear engFl P₀ hp g fo₀ F₀ t₀ = some (o₀, G₀, u₀) → Skel o o₀

end OnBytes.Desc.First.K4.Total

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Statements.lean: the honest side of the kind "lookup" (K3). The
statements of the lemmas that lead from its row of parts to "the verifier's hearing returns on the
rounds that the row plays, and every claim that it leaves is worth 0 on the hidden values".
Definitions with code, definitions of propositions. Nothing is proved in this file. None of the
statements is one of the library's goals: they are lemmas' statements about one kind's honest part.
Every statement on values is conditional on `Lawful`, which says that the summands which the row is
given sum as they should; nothing here says that any summand does.

Terms. Honest/K3/GLOSSARY.md, many of whose entries point to this file. The prover's text is
`lookRow` (Honest/K3/Row.lean) at the points of Honest/K3/Heard.lean. The verifier's text is `hearV`
and `planesV` (Johnson/Desc/First/Look/Via/Rounds.lean).

What is defined, by the file's sections.
  1. `Course`: one run of a lookup's stages, each played alone: the place, the summands, the coins
     by stage, the state in front, what is shown in front (a term of the frame's `Seen`: rounds,
     and the columns opened where they are handed), the challenges. `Course.rounds`: its rounds.
  2. `Course.call`, `r`, `ends`, `T`, `shown`, `poly`: what a stage's sumcheck is in that run.
  3. `Course.form`: the form that the verifier claims at a stage, on the numbers of slots. It
     follows `messagesV` (Rounds.lean) line for line. `Course.claimed`: what that form should be
     worth; it is written independently of `form`, on the true end values. `endTerm`: the end
     terms of the verifier.
  4. `Fit`, `MasksAre`, `Inv`, `Lawful`: the hypotheses. `Inv` is the one invariant, by stage.
  5. The statements, in the order in which one rests on the other:
     `DrawsWork`: the frame's test on challenges reads no work bit. (That the stages' entries are
       the verifier's is `entries_stages`, Honest/K3/RowLaw.lean.)
     `CourseSays`: all stages answer; no summand is read for that.
     `RowPlays`: the frame's `play` on `lookRow` yields the course's rounds.
     `FormWorth`: where the end values' slots hold the true end values, `form` is worth `claimed`.
     `QuietStep`, `StageStep`, `LeavesStep`: from the invariant in front of a stage to the invariant
       behind it; and, conditional on the stage's `SumsTo`, the row that is left is worth 0.
     `LookHeard`: `hearV` returns on the course's rounds, with the run's points.
     `PlanesReturn`: `planesV` returns later, where the leaves' own slots are still free.
     `LookLeft`: conditional on `Lawful`: all rows, the three claims on the planes and the keys'
       forms have their values.
     `AgreeSame`: summands that agree at the run, as read, give one course and one `Lawful`.
  Where each is proved. `DrawsWork`, `QuietStep`, `FormWorth`: Honest/K3/Law/Steps.lean.
     `CourseSays`, `RowPlays`: Honest/K3/Law/RowPlays.lean. `StageStep`, `LeavesStep`:
     Honest/K3/Law/StageStep.lean (conditional on `HB`), Honest/K3/Law/HBPaid.lean (without it,
     resting on the theorems of Honest/SumLaw/). `PlanesReturn`: Honest/K3/Law/PlanesReturn.lean.
     `LookHeard`, `LookLeft`: Honest/K3/Parts/LookLeftPaid.lean [not in this library]
     (`lookHeardPaid`, `lookLeftPaid`); at one
     part of keys alone: Honest/K3/Law/LookHeardOne.lean, Honest/K3/Law/LookLeftOf.lean.
     `AgreeSame`: as stated, in no file: the half on `Lawful` is `agreeLawful`
     (Honest/K3/Law/Agree.lean); the half on the rounds remains a statement.

Imported. The masked sumcheck's law is stated in Honest/SumLaw/Statement.lean (statements too); the
terms `alone`, `SumsTo`, `jobPoly`, `varsOf` are taken from Honest/SumLaw/Terms.lean.

Limits. The stages are played alone, at the summands' own input type; what `Part.lift` makes of a
part is not reached. Shown in: `alone_lift` (Honest/K3/Law/PlayLift.lean), of every part, where
"get" reads back what "set" writes: a lifted part, played alone, yields what the part yields at the
narrowed state; and `rowPlaysSeated` (Honest/K3/Law/RowSeated.lean), of the row as `Part.lift` seats
it (`proverSideOfLookupInChainAtOneOwner`), conditional on `Fit` and `entriesFit`. The letters planes (what the planes of the
counts' bits come to under a product form) and keys (what a part's keys come to at a point) are
parameters: how planes and keys are read is the caller's, as in the verifier's text. That `Lawful`
holds of any summands is not stated here. Stated in Honest/K3/Law/SpecLawful.lean (`LawfulSpec`) and
proved in Honest/K3/Law/SpecProof.lean (`lawfulSpec`): of the specification's summands, conditional
on `Fit R`, `Numbered R` and `SpecAt R N w`. Nothing is said of a list of challenges that the rounds
cannot sample. Every statement over a course ranges over every value of its field `seen`, the
columns opened among it; `StageStep` and `LeavesStep` bind a `Seen` of their own, at every value
too.
Instances of the hypotheses: Honest/K3/Law/Members.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.SumLaw.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE isZeroE)
open OnBytes.Model (Reading Aff Fork eqTab ofNat)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV entriesV entriesFit eqPairs)
open VerifiableInference.Desc.First.ProdV (stepDown)
open ProofFile.Honest.SumLaw (alone SumCoins firstRun endRun frontOf SumsTo jobPoly varsOf hidingCoin)

/-- An element of the program, read in the library's field. -/
abbrev rd (x : E) : GE := Reading.gl.val x

/-! ## 1 A course: the stages, each played alone -/

/-- A stage's call, points left as stand-ins; a call of nothing at a stage that sends nothing. -/
def shapeAt (a : At) (s : Stage) : Call := (s.call a.face).getD ⟨0, [], none⟩

/-- A stage's job, as `partOf` lays it (Honest/K3/Row.lean), at the
points of Honest/K3/Heard.lean. -/
abbrev jobAt {W : Type} (J : LookJobs W) (a : At) (s : Stage) : SumJob W Unit :=
  jobOf ⟨ptsOf, pointsAt⟩ J a s (shapeAt a s)

/-- What the part of a stage is handed of coins: its two stretches. It hangs on the stage's public
shape alone. -/
def StageCoins (a : At) (s : Stage) : Type :=
  Handed ⟨0, 0⟩ ((sumName a.place (indexOf a.face s), ⟨0, ownRun (shapeAt a s)⟩) ::
    endRuns (endName a.place (indexOf a.face s)) (shapeAt a s).ends) []

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- **One run of a lookup's stages.** -/
structure Course (W : Type) where
  /-- the lookup's public data at its place -/
  a : At
  /-- the summands -/
  J : LookJobs W
  /-- the ledger's next slot in front of the lookup: public data -/
  first : Nat
  /-- the coins, stage by stage; at a stage that sends nothing they are not read -/
  c : (s : Stage) → StageCoins a s
  /-- the state in front of the lookup -/
  t : State W Unit
  /-- what is shown in front of the lookup (the frame's `Seen`); no move of the row reads it -/
  seen : Seen
  /-- the challenges of the lookup's own rounds -/
  ds : List Fmt.Drawn

namespace Course
variable {W : Type} (R : Course W)

/-- The lookup's numbers. -/
abbrev f : LFace := R.a.face

/-- A stage's job. -/
abbrev job (s : Stage) : SumJob W Unit := jobAt R.J R.a s

/-- **A stage played alone**, from a state on: a sumcheck's part by `alone`; a stage that sends
nothing shows one round without an item. -/
def stage (s : Stage) (t : State W Unit) (seen : Seen) (ds : List Fmt.Drawn) :
    Option (List Fmt.RoundView) :=
  match s.call R.f with
  | some _ =>
    alone (sumPart (V := Unit) (sumName R.a.place (indexOf R.f s))
      (endName R.a.place (indexOf R.f s))
      (R.job s)) (R.c s) t seen ds
  | none =>
    match ds with
    | [d] => some [⟨[], d⟩]
    | _ => none

/-- Stages in a row: each takes its own number of challenges; the state hears them; what was shown
is laid behind what was seen. Nothing if a stage yields nothing or challenges are left over. -/
def run : List Stage → State W Unit → Seen → List Fmt.Drawn → Option (List Fmt.RoundView)
  | [], _, _, [] => some []
  | [], _, _, _ :: _ => none
  | s :: l, t, seen, ds =>
    (R.stage s t seen (ds.take (s.rounds R.f))).bind fun x =>
      (run l { t with heard := t.heard ++ ds.take (s.rounds R.f) } (seen.plus x)
        (ds.drop (s.rounds R.f))).map (x ++ ·)

/-- **The rounds of the course.** -/
def rounds : Option (List Fmt.RoundView) := R.run (stages R.f) R.t R.seen R.ds

/-! ## 2 A stage's sumcheck in the run -/

/-- The state in front of a stage. -/
def stateAt (s : Stage) : State W Unit :=
  { R.t with heard := R.t.heard ++ R.ds.take (firstRound R.f s) }

/-- What the stage's job is handed of it. A lookup's jobs read of it the challenges heard alone
(`jobOf`, Honest/K3/Row.lean): so what is shown in front of the lookup is laid here at every
stage; what is laid there makes no difference to any function of a stage's job. -/
def front (s : Stage) : Front Unit := frontOf (R.stateAt s) R.seen

/-- The stage's own challenges. -/
def draws (s : Stage) : List Fmt.Drawn := (R.ds.drop (firstRound R.f s)).take (s.rounds R.f)

/-- The stage's call as it stands in the run. -/
def call (s : Stage) : Call := (R.job s).callAt R.t.input (R.front s)

/-- The challenges of its variables, in the rounds' order, Y's last. -/
def r (s : Stage) : List E := varsOf (R.call s) (R.draws s)

/-- Y's challenge. -/
def beta (s : Stage) : E := (R.r s).getLastD zeroE

/-- All points of the run, of all challenges. -/
def pts : Pts := ptsOf R.f R.a.base (R.t.heard ++ R.ds)

/-- The leaves' sumcheck's challenges; the bits' sumcheck's variables' challenges. -/
def zb0 : Array E := leavesR R.f R.a.base (R.t.heard ++ R.ds)
def zb1 : Array E := bitsR R.f R.a.base (R.t.heard ++ R.ds)

/-- The stage's true end values, as its job gives them. -/
def ends (s : Stage) : List E :=
  (R.job s).ends R.t.input (R.front s) ((R.r s).take (R.job s).shape.vs.length)

/-- True end value number j of a stage. -/
def T (s : Stage) (j : Nat) : E := (R.ends s).getD j zeroE

/-- The end values' mask entries: the stage's second stretch. -/
def masks (s : Stage) : List E := endRun (J := R.job s) (R.c s)

/-- The end values as they are shown: each plus Y's challenge times its mask entry. -/
def shown (s : Stage) : List E :=
  addL (padTo (s.tail R.f) (R.ends s)) (scaleL (R.beta s) (padTo (s.tail R.f) (R.masks s)))

/-- The summand's polynomial of the round behind given challenges. -/
def poly (s : Stage) : List E → List E := jobPoly (R.job s) R.t.input (R.front s) (R.masks s)

/-- The public factor. -/
def factor : E := R.f.factor R.pts.theta R.pts.alpha

/-! ## 3 The verifier's forms, by stage -/

/-- The slot of a stage's first end value. -/
def endSlot (s : Stage) : Nat := R.first + firstSlot R.f s + s.own R.f

/-- The form behind a level: the verifier's own step down, on the level's two end slots. -/
def line (s : Stage) (xi : E) : Aff :=
  (stepDown { r := #[], sL := R.endSlot s, sR := R.endSlot s + 1, xi := xi,
              row := Aff.ofConst zeroE }).2

/-- The slot of plane j's root (`tieV`: the third end value of the first step; the second of each
later step; the last plane's is the last step's remaining factor). -/
def planeSlot (j : Nat) : Nat :=
  if j = 0 then R.endSlot (.tie 0) + 2
  else if j + 1 < R.f.planes then R.endSlot (.tie j) + 1
  else if R.f.planes = 2 then R.endSlot (.tie 0) + 1
  else R.endSlot (.tie (R.f.planes - 2))

/-- The one claim on the planes' roots (`messagesV`: cT). -/
def join : Aff :=
  (List.range (2 ^ R.f.mu)).foldl
    (fun (c : Aff) j =>
      if j < R.f.planes then
        Aff.addMul c (Aff.slot (R.planeSlot j)) ((eqTab R.pts.rhoT).getD j zeroE)
      else c + Aff.ofConst ((eqTab R.pts.rhoT).getD j zeroE)) (Aff.ofConst zeroE)

/-- The form of part i's root (`partsV`). -/
def root (i : Nat) : Aff :=
  if i + 1 < R.f.parts.length then Aff.slot (R.endSlot (.split i))
  else if R.f.parts.length ≤ 1 then Aff.slot (R.endSlot (.tie 0))
  else Aff.slot (R.endSlot (.split (R.f.parts.length - 2)) + 1)

/-- LINE's sample behind a key level; behind a level of the table side: the first coordinate of the
next point. -/
def xiK (i m : Nat) : E := (R.pts.keyPt i (m + 1)).getD 0 zeroE
def xiT (l : Nat) : E := (R.pts.tabPt (l + 1)).getD 0 zeroE

/-- The form in front of the table side's level number l; at l := d: in front of the leaves. -/
def tabForm : Nat → Aff
  | 0 => R.join
  | l + 1 => R.line (.tab l) (R.xiT l)

/-- **The form that the verifier claims at a stage.** At `.key i v`, v the number of part i's
levels: the form that its key tree leaves. At every other stage: the constant form 0. -/
def form : Stage → Aff
  | .tie 1 => Aff.slot (R.endSlot (.tie 0) + 1)
  | .tie (n + 2) => Aff.slot (R.endSlot (.tie (n + 1)))
  | .split 0 => Aff.slot (R.endSlot (.tie 0))
  | .split (i + 1) => Aff.slot (R.endSlot (.split i) + 1)
  | .key i 0 => R.root i
  | .key i (m + 1) => R.line (.key i m) (R.xiK i m)
  | .tab l => R.tabForm l
  | .leaves => R.tabForm R.f.d
  | _ => Aff.ofConst zeroE

/-- The line between a level's two true end values. -/
def lineV (s : Stage) (xi : E) : E :=
  addE (mulE (subE oneE xi) (R.T s 0)) (mulE xi (R.T s 1))

/-- Plane j's true root. -/
def planeV (j : Nat) : E :=
  if j = 0 then R.T (.tie 0) 2
  else if j + 1 < R.f.planes then R.T (.tie j) 1
  else if R.f.planes = 2 then R.T (.tie 0) 1
  else R.T (.tie (R.f.planes - 2)) 0

/-- The planes' true roots under the equality weights of JOIN's point; a plane that is not real
counts 1. -/
def joinV : E :=
  (List.range (2 ^ R.f.mu)).foldl
    (fun c j =>
      addE c (mulE ((eqTab R.pts.rhoT).getD j zeroE) (if j < R.f.planes then R.planeV j else oneE)))
    zeroE

/-- Part i's true root. -/
def rootV (i : Nat) : E :=
  if i + 1 < R.f.parts.length then R.T (.split i) 0
  else if R.f.parts.length ≤ 1 then R.T (.tie 0) 0
  else R.T (.split (R.f.parts.length - 2)) 1

/-- What the table side's form should be worth. -/
def tabV : Nat → E
  | 0 => R.joinV
  | l + 1 => R.lineV (.tab l) (R.xiT l)

/-- **What the form at a stage should be worth**: of the true end values of the stages in front. At
every other stage: 0. -/
def claimed : Stage → E
  | .tie 1 => R.T (.tie 0) 1
  | .tie (n + 2) => R.T (.tie (n + 1)) 0
  | .split 0 => R.T (.tie 0) 0
  | .split (i + 1) => R.T (.split i) 1
  | .key i 0 => R.rootV i
  | .key i (m + 1) => R.lineV (.key i m) (R.xiK i m)
  | .tab l => R.tabV l
  | .leaves => R.tabV R.f.d
  | _ => zeroE

end Course

/-- **The verifier's end terms**, by stage, on shown end values (`tieV`, `partsV`,
`First.ProdV.level`, `messagesV`). a: the public factor. -/
def endTerm (a : E) : Stage → List E → E
  | .tie 0, v =>
    subE (v.getD 0 zeroE) (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE)))
  | .tie (_ + 1), v => mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)
  | .bits, v => subE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 0 zeroE)
  | _, v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)

/-- The pairs of the third claim on the planes: the counts add up (`planesV`). -/
def countPairs (f : LFace) : List (E × E) :=
  ((List.range f.mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) ++ List.replicate f.d (oneE, oneE)

/-! ## 4 The hypotheses -/

variable {W : Type}

/-- An entry of the plan as a declared round, as the kind's sub-protocol lays it. -/
def declOf (e : Fmt.Entry) : Fmt.DeclaredRound := { entry := e }

/-- **The course stands at its place, and its challenges can be sampled**: the tests on the lookup's
numbers; as many challenges were heard in front as the place's public data says; the frame's own
test on the challenges, at the rounds that the verifier's text hears. -/
structure Fit (R : Course W) : Prop where
  ok : R.f.ok = true
  base : R.t.heard.length = R.a.base
  draws : drawsFit ((entriesV R.f).map declOf) R.ds = true

/-- **The mask entries under the lookup's slots are the coins that the stages spend**: under a
sumcheck's own slots those for its hiding polynomial; under its end values' slots its second
stretch. Both clauses read a list of coins with a default (`hidingCoin` reads
`(firstRun c).getD … zeroE`): under each clause's own bound the default is never taken, at every
course: `masksAre_entries` (Honest/K3/Law/MasksAreFenced.lean [not in this library]). -/
def MasksAre (R : Course W) (mask : Nat → GE) : Prop :=
  ∀ s ∈ stages R.f,
    (∀ i, i < s.own R.f →
      mask (R.first + firstSlot R.f s + i) = hidingCoin (J := R.job s) (R.c s) i) ∧
    (∀ j, j < s.tail R.f → mask (R.endSlot s + j) = rd ((R.masks s).getD j zeroE))

/-- How many hidden values the first n stages take. -/
def slotsIn (f : LFace) (n : Nat) : Nat := (((stages f).take n).map (Stage.slots f)).sum

/-- **The invariant, by stage**: what holds of the ledger F when the first n stages have been heard.
The arrays have their size; the count of slots stands behind these stages' slots; there is room for
the whole lookup, and from the count on all is free as far as the lookup reaches; the end values of
these stages are filled; and in the world of every later ledger, at mask entries that are the coins
spent, the hidden value under each of these end values' slots is the job's true end value. -/
structure Inv (R : Course W) (n : Nat) (F : Fork) : Prop where
  sized : Sized F
  next : F.next = R.first + slotsIn R.f n
  room : R.first + R.f.slots ≤ F.ns
  free : ∀ j, F.next ≤ j → j < R.first + R.f.slots → ¬ Filled F j
  filled : ∀ s ∈ (stages R.f).take n, ∀ j, j < s.tail R.f → Filled F (R.endSlot s + j)
  ends : ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later F H →
    MasksAre R mask → ∀ s ∈ (stages R.f).take n, ∀ j, j < s.tail R.f →
      (H.worldOf Reading.gl mask entry).slot (R.endSlot s + j) = rd (R.T s j)

/-- A stage's summand sums, round by round, from c to c' (Honest/SumLaw/Terms.lean). -/
def Sums (R : Course W) (s : Stage) (c c' : GE) : Prop :=
  SumsTo Reading.gl (R.call s).all (R.poly s) [] (R.r s) c c'

/-- **What is asked of the summands, at one run.** planes: what the planes of the counts' bits come
to under a product form that is given by its pairs. keys: what part i's keys come to at a point, the
highest variable first.
sums: at each stage with end values the summand sums from what the claimed form should be worth to
the verifier's end term on the shown end values. leaves: the leaves' summand sums to 1 plus the
public factor of a bit times the planes' value at the sumcheck's own point. bits: the bits'
sumcheck's true end value is the planes' value at its point. count: the counts add up. keyEnds: the
line between the true end values of a part's last key level is alpha less the keys' value at the key
tree's last point. -/
structure Lawful (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE) :
    Prop where
  sums : ∀ s ∈ stages R.f, 0 < s.tail R.f →
    Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s)))
  leaves : Sums R .leaves (rd (R.claimed .leaves))
    (1 + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) * planes (eqPairs (R.f.mu + R.f.d) R.zb0))
  bits : rd (R.T .bits 0) = planes (eqPairs (R.f.mu + R.f.d) R.zb1)
  count : planes (countPairs R.f) = rd (ofNat R.f.count)
  keyEnds : ∀ y ∈ R.f.parts.zipIdx,
    rd (R.claimed (.key y.2 y.1)) = rd R.pts.alpha - keys y.2 (R.pts.keyPt y.2 y.1)

/-- **What was heard is the run's**: the public factor, the numbers of slots, the forms that are
left open, and the number of rows. The points are not among its clauses: that they are those of
Honest/K3/Heard.lean wherever the hearing returns is stated in Honest/K3/HeardLaw.lean. -/
structure HeardIs (R : Course W) (g : HeardV) : Prop where
  a : g.a = R.factor
  sBit : g.sBit = R.endSlot .bits
  rows : g.rows.size = R.f.lins
  keys : g.keys.map (·.2) = R.f.parts.zipIdx.map fun x => R.form (.key x.2 x.1)
  start : g.leaves.start = R.form .leaves
  first : g.leaves.first = R.first + firstSlot R.f .leaves
  r : g.leaves.r = R.r .leaves

/-! ## 5 The statements -/

/-- The statement that the frame's test on challenges does not read an entry's work bits: at the
planner's entries it says what it says at the verifier's text's. Not proved here; a lemma's
statement, none of the library's goals. -/
def DrawsWork : Prop :=
  ∀ (f : LFace) (es : List Fmt.Entry) (ds : List Fmt.Drawn), entriesFit f es = true →
    drawsFit (es.map declOf) ds = drawsFit ((entriesV f).map declOf) ds

/-- The statement that all stages of a course answer. No summand's value matters for it. Not proved
here; a lemma's statement, none of the library's goals. -/
def CourseSays : Prop :=
  ∀ (W : Type) (R : Course W), Fit R → ∃ x, R.rounds = some x ∧ x.length = (entriesV R.f).length

/-- The coins of named stretches, as lists of the program's elements. -/
def csAllE : (l : List (String × Due)) → CsAll l → List (List E)
  | [], _ => []
  | _ :: l, c => coinsE c.1 :: csAllE l c.2

/-- What the parts of a row spend, part by part, stretch by stretch. -/
def rowSpent {V W X : Type} : (ps : List (Part V W X)) → RowCoins ps → List (List (List E))
  | [], _ => []
  | p :: ps, c => csAllE p.spends c.1.2.1 :: rowSpent ps c.2

/-- The row's coins are the course's: part by part, stretch by stretch. -/
def CoinsAre {V : Type} (R : Course W)
    (c : RowCoins (lookRow (V := V) ⟨ptsOf, pointsAt⟩ R.J R.a)) : Prop :=
  ∀ s ∈ stages R.f, (s.call R.f).isSome = true →
    (rowSpent _ c).getD (indexOf R.f s) [] =
      firstRun (J := R.job s) (R.c s) :: (if s.tail R.f = 0 then [] else [R.masks s])

/-- The statement that the frame's `play` on the row of parts, at the planner's entries, goes
through and yields the course's rounds; that it leaves the state with the challenges heard and
nothing else turned; and that every row's coins are some course's. Not proved here; a lemma's
statement, none of the library's goals. -/
def RowPlays : Prop :=
  ∀ (V W : Type) (R : Course W) (name : String) (v : Option V) (es : List Fmt.Entry)
    (loc : List Fmt.Drawn) (c : RowCoins (lookRow (V := V) ⟨ptsOf, pointsAt⟩ R.J R.a)),
    ∃ c' : (s : Stage) → StageCoins R.a s, CoinsAre { R with c := c' } c ∧
      (Fit R → entriesFit R.f es = true →
        ∃ y x, play (rowSteps name R.a.place v (lookRow ⟨ptsOf, pointsAt⟩ R.J R.a) 0
              (es.map fun e => (declOf e, ([] : List Oracle))) c) R.ds []
              ⟨R.t, loc, R.seen.rounds, R.seen.opened⟩ = .ok y ∧
          ({ R with c := c' } : Course W).rounds = some x ∧ roundsOf y.1 = x ∧
          y.2.st = { R.t with heard := R.t.heard ++ R.ds })

/-- The statement that, in a world in which the slots of the end values of the stages in front of a
stage hold the true end values, the form that the verifier claims at that stage is worth what it
should be. It is stated at every stage of the row, and at the forms that the key trees leave: such a
form's stage is none of the row's, `indexOf` is the row's length there, and the hypothesis speaks of
all stages. Not proved here; a lemma's statement, none of the library's goals. -/
def FormWorth : Prop :=
  ∀ (W : Type) (R : Course W) (Wd : OnBytes.Model.World GE) (s : Stage), R.f.ok = true →
    (s ∈ stages R.f ∨ ∃ y ∈ R.f.parts.zipIdx, s = .key y.2 y.1) →
    (∀ s' ∈ (stages R.f).take (indexOf R.f s), ∀ j, j < s'.tail R.f →
      Wd.slot (R.endSlot s' + j) = rd (R.T s' j)) →
    (R.form s).value Reading.gl Wd = rd (R.claimed s)

/-- The statement that a stage which sends nothing leaves the invariant as it is. Not proved here;
a lemma's statement, none of the library's goals. -/
def QuietStep : Prop :=
  ∀ (W : Type) (R : Course W) (n : Nat) (s : Stage) (F : Fork),
    (stages R.f)[n]? = some s → s.call R.f = none → Inv R n F → Inv R (n + 1) F

/-- The statement of the step at a stage with end values: from the invariant in front of the stage:
the masked sumcheck's own text, at the form that the verifier claims there, at the run's call and at
the verifier's end term, accepts the stage's rounds; it returns the run's challenges, Y's not 0,
and the stage's first end slot; the invariant holds behind the stage; and, conditional on the
stage's summand summing from what the form should be worth to the end term on the shown values, the
row that is left is worth 0 in the world of every later ledger. Not proved here; a lemma's
statement, none of the library's goals. -/
def StageStep : Prop :=
  ∀ (W : Type) (R : Course W) (n : Nat) (s : Stage) (F : Fork) (seen : Seen) (x : List Fmt.RoundView),
    Fit R → (stages R.f)[n]? = some s → 0 < s.tail R.f → Inv R n F →
    R.stage s (R.stateAt s) seen (R.draws s) = some x →
    ∃ h row G,
      MaskedSum.whole (R.form s) (R.call s) (fun _ v => endTerm R.factor s v) F x =
        some (h, row, G) ∧
      h.r = R.r s ∧ isZeroE (h.r.getLastD zeroE) = false ∧ h.sEnd = R.endSlot s ∧
      Inv R (n + 1) G ∧
      (Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s))) →
        ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
          MasksAre R mask → row.value Reading.gl (H.worldOf Reading.gl mask entry) = 0)

/-- The statement of the step at the leaves, whose sumcheck has no end value and whose row is made
late: from the invariant in front: the part's `hear` accepts the stage's rounds; the invariant holds
behind; the sumcheck's own slots are still free; and, conditional on the summand summing from what
the form should be worth to cf: a row that is made by `row` at 1 and no kept term, at any later
sized ledger, is worth eps (1 - cf) in the world of every ledger later still. Not proved here;
a lemma's statement, none of the library's goals. -/
def LeavesStep : Prop :=
  ∀ (W : Type) (R : Course W) (n : Nat) (F : Fork) (seen : Seen) (x : List Fmt.RoundView),
    Fit R → (stages R.f)[n]? = some .leaves → Inv R n F →
    R.stage .leaves (R.stateAt .leaves) seen (R.draws .leaves) = some x →
    ∃ h G,
      MaskedSum.hear (R.form .leaves) (R.call .leaves) F x = some (h, G) ∧
      h.r = R.r .leaves ∧ h.first = R.first + firstSlot R.f .leaves ∧ Inv R (n + 1) G ∧
      (∀ j, h.first ≤ j → j < h.first + Stage.own R.f .leaves → ¬ Filled G j) ∧
      ∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          Sized F' → Later G F' → MaskedSum.row h oneE {} F' = some (y, G') → Later G' H →
          MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd h.eps * (1 - cf)

/-- The statement that the verifier's hearing returns on the course's rounds, from a ledger at which
the invariant holds in front of the first stage; that what it heard is the run's; that the invariant
holds behind the last stage; and that the leaves' own slots are free there. No summand's value
matters for it. Not proved here; a lemma's statement, none of the library's goals. -/
def LookHeard : Prop :=
  ∀ (W : Type) (R : Course W) (F : Fork) (x : List Fmt.RoundView),
    Fit R → Inv R 0 F → R.rounds = some x →
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      ∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j

/-- The statement that the three claims on the planes are made, at every later ledger at which the
leaves' own slots are still free. Not proved here; a lemma's statement, none of the library's goals.
-/
def PlanesReturn : Prop :=
  ∀ (W : Type) (R : Course W) (F G F' : Fork) (x : List Fmt.RoundView) (g : HeardV),
    Fit R → Inv R 0 F → R.rounds = some x → hearV R.f F x = some (g, G) → Sized F' → Later G F' →
    (∀ j, R.first + firstSlot R.f .leaves ≤ j →
      j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled F' j) →
    ∃ cl G', planesV R.f g F' = some (cl, G') ∧ cl.length = 3

/-- The statement of what the lookup leaves, conditional on `Lawful`: in the world of every later
ledger, at mask entries that are the coins spent: every row that was heard is worth 0; the form that
part i's key tree leaves is worth alpha less the keys' value at the tree's last point; and each of
the three claims on the planes, made at any later ledger, holds: its form plus its scalar times the
planes' value under its pairs is 0. Not proved here; a lemma's statement, none of the library's
goals. -/
def LookLeft : Prop :=
  ∀ (W : Type) (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (F G : Fork) (x : List Fmt.RoundView) (g : HeardV),
    Fit R → Inv R 0 F → R.rounds = some x → hearV R.f F x = some (g, G) → Lawful R planes keys →
    (∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H → MasksAre R mask →
      (∀ y ∈ g.rows.toList, y.value Reading.gl (H.worldOf Reading.gl mask entry) = 0) ∧
      (∀ y ∈ R.f.parts.zipIdx, (R.form (.key y.2 y.1)).value Reading.gl
          (H.worldOf Reading.gl mask entry) =
        rd R.pts.alpha - keys y.2 (R.pts.keyPt y.2 y.1))) ∧
    (∀ (F' G' H : Fork) (cl : List PlaneClaim) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
      Sized F' → Later G F' → planesV R.f g F' = some (cl, G') → Later G' H → MasksAre R mask →
      ∀ y ∈ cl, y.lead.value Reading.gl (H.worldOf Reading.gl mask entry) +
        rd y.scalar * planes y.pairs = 0)

/-- **Another structure of summands agrees with the course's, at the run**: at every stage with a
call, at the course's input, at the points that the stage's job is given, at the run's own
challenges and mask entries: list by list as `sumPart` cuts or fills them, as read: the round
polynomial behind each beginning of the variables' challenges; the polynomial in Y and the end
values behind all of them. Nothing is asked at another point, at a point of another length, or of
the words themselves. -/
def AgreeAt (R : Course W) (B : LookJobs W) : Prop :=
  ∀ s ∈ stages R.f, ∀ k, s.call R.f = some k →
    (∀ n, n < k.vs.length →
      (padTo (k.vs.getD n (.plain 0)).d ((R.job s).round R.t.input (R.front s)
        ((R.r s).take n))).map
          rd =
        (padTo (k.vs.getD n (.plain 0)).d
          ((jobAt B R.a s).round R.t.input (R.front s) ((R.r s).take n))).map rd) ∧
    (∀ e, k.ends = some e →
      (padTo (e.dY + 1) ((R.job s).inY R.t.input (R.front s) ((R.r s).take k.vs.length)
          (R.masks s))).map rd =
        (padTo (e.dY + 1) ((jobAt B R.a s).inY R.t.input (R.front s) ((R.r s).take k.vs.length)
          (R.masks s))).map rd ∧
      (padTo e.n ((R.job s).ends R.t.input (R.front s) ((R.r s).take k.vs.length))).map rd =
        (padTo e.n ((jobAt B R.a s).ends R.t.input (R.front s) ((R.r s).take k.vs.length))).map rd)

/-- The statement that summands which agree at the run give the same rounds, and that one structure
is lawful at the run if the other is. Not proved here; a lemma's statement, none of
the library's goals.
-/
def AgreeSame : Prop :=
  ∀ (W : Type) (R : Course W) (B : LookJobs W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE),
    Fit R → AgreeAt R B →
    ({ R with J := B } : Course W).rounds = R.rounds ∧
      (Lawful { R with J := B } planes keys ↔ Lawful R planes keys)

end ProofFile.Honest.K3.Law

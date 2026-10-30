-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Row.lean: the honest side of the kind "lookup" (K3): its row of
parts, general in the lookup's numbers; the simulators' forms beside the parts; and the count of the
slots over which each part lays a mask entry. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md ("row", "stage", "part, stretch", "slot", "mask, mask row", "book,
coins", "half", "seat").

What it does. Honest/K3/Stages.lean lists a lookup's stages in the order of the verifier's rounds,
each with its public shape. Here each stage becomes a part of the frame (Honest/Frame.lean):
  a stage with a call: the masked sumcheck's part (`sumPart`, Honest/Sum.lean) at a job that is made
    of three letters: how the run's points are read off the challenges, the points of the stage's
    variables, and the stage's summand;
  a stage that sends nothing: one move, which sends nothing.
No round of a sumcheck, no point and no summand is written here.

What is defined.
  1 `Stage.name`, `Stage.entries`: a stage's rounds as entries of the plan, for the tests.
  2 `Stage.own`, `Stage.tail`, `Stage.slots`, `firstSlot`: how many slots a stage takes, in two
    stretches, and how many of the lookup's stand in front of it.
  3 `Reads`, `quiet`, `jobOf`, `sumName`, `endName`, `partOf`, `lookRow`, `proverSideOfLookupAtOneOwner`, `proverSideOfLookupInChainAtOneOwner`:
    the row.
  4 `quietSim`, `simOf`, `lookSims`, `lookPairs`: the forms of simulators beside the parts.
  5 `Stretch`, `stretches`, `Stretch.line`: every stretch of coins that the row spends, as data.

The slots. The verifier's ledger gives every scalar that a segment sends a number, its slot. A
masked sumcheck that begins at slot s takes, in this order (Johnson/Desc/Part/MaskedSum4.lean,
`hear`: `first`, `sEnd`): the slots s, s + 1, .. of its own scalars in front of the end values,
under which the coefficients of its hiding polynomial lie (`ownSlots`; a lookup's calls have no
lead); then the slots of its end values. The part spends two stretches of the segment's mask row in
the same order: "sum", then "ends" (`ownRun`, `endRuns`). A stage that sends nothing takes no slot.

Imported. Beneath this file lie Honest/Frame.lean,
Honest/Sum.lean, Honest/Side.lean (imported by a line of this
file's own) and
Honest/ForKinds.lean (`runName`, `maskRowRun`).

Limits. What the three letters hold is compared with nothing here. That the stages' rounds are the
verifier's and that the slots add up to the verifier's count is shown in Honest/K3/RowLaw.lean, that
the row is cut as the book cuts in Honest/K3/RowCut.lean, each at every face with two planes at
least. A stage
that does not stand in the row of its face gets the row's length as its number, and all rounds and
slots as those in front of it. The owner of every stretch is written here as the segment's mask row:
nothing in this file compares that with the maker of a book. Shown in part:
Honest/K3/Law/RowLends.lean and Honest/K3/Law/MasksBook.lean have theorems that are conditional on
tests with code on a given book (`bookFits`, `placeFits`; `startsFit`), which compare the book's
entries at the row's parts with the stretches. Whether a maker's book passes these tests is for an
evaluation at that book. The simulators are data: nothing is said of what they are good for.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part (MaskedSum.entries)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)

variable {V W Pb V₁ W₁ X₁ : Type}

/-! ## 1 A stage's rounds as entries of the plan -/

/-- The name of the one round of a stage that sends nothing, as the plan's entry has it; "" at a
sumcheck, whose rounds' names are the masked sumcheck's own. -/
def Stage.name : Stage → String
  | .shift => "LKP shift"
  | .alpha => "LKP"
  | .join => "JOIN"
  | .keyLine _ _ => "LINE"
  | .tabLine _ => "LINE"
  | .zero => "ZERO"
  | _ => ""

/-- **A stage's rounds as entries of the plan**, the work bits left 0: by the verifier's own makers,
at the stage's call or at its name and number of samples. -/
def Stage.entries (f : LFace) (s : Stage) : List Fmt.Entry :=
  match s.call f with
  | some k => MaskedSum.entries k
  | none => [VerifiableInference.Desc.K3.drawEntry s.name (s.draws f)]

/-! ## 2 The slots -/

/-- The first stretch: the sumcheck's own scalars in front of the end values. -/
def Stage.own (f : LFace) (s : Stage) : Nat := ((s.call f).map ownRun).getD 0

/-- The second stretch: the end values. -/
def Stage.tail (f : LFace) (s : Stage) : Nat :=
  (((s.call f).bind (·.ends)).map (·.n)).getD 0

/-- How many slots a stage takes. -/
def Stage.slots (f : LFace) (s : Stage) : Nat := s.own f + s.tail f

/-- **How many slots of the lookup stand in front of a stage.** -/
def firstSlot (f : LFace) (s : Stage) : Nat :=
  (((stages f).take (indexOf f s)).map (Stage.slots f)).sum

/-! ## 3 The row -/

/-- **How the run's points are read**: two letters of the row. -/
structure Reads where
  /-- of the lookup's numbers, of the number of the first chain's rounds in front of the place, and
  of the challenges heard so far -/
  pts : LFace → Nat → List Fmt.Drawn → Pts
  /-- the points of a stage's variables, in the order of the rounds -/
  pointsAt : LFace → Stage → Pts → List E

/-- **A stage that sends nothing**: one move. -/
def quiet : Part V W Unit :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩] }

/-- **A stage's job for the masked sumcheck.** Here k is the stage's call, points left as stand-ins.
Each function reads the run's points off the challenges in front of the part. -/
def jobOf (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (k : Call) : SumJob W Unit :=
  { shape := k
    points := fun _ fr => R.pointsAt a.face s (R.pts a.face a.base fr.heard)
    lead := fun _ _ => []
    round := fun w fr rs => (J.job s).round w (R.pts a.face a.base fr.heard) rs
    inY := fun w fr rs m => (J.job s).inY w (R.pts a.face a.base fr.heard) rs m
    ends := fun w fr rs => (J.job s).ends w (R.pts a.face a.base fr.heard) rs }

/-- The name of the first stretch that the part number i of the row at a place spends. -/
def sumName (p : Place) (i : Nat) : String := runName maskRowRun ⟨p, i⟩ "sum"

/-- The name of the second. -/
def endName (p : Place) (i : Nat) : String := runName maskRowRun ⟨p, i⟩ "ends"

/-- **The part of a stage.** Here i is its number in the row. -/
def partOf (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) : Part V W Unit :=
  match s.call a.face with
  | some k => sumPart (sumName a.place i) (endName a.place i) (jobOf R J a s k)
  | none => quiet

/-- **A lookup's row of parts**: a part for each stage, in order. -/
def lookRow (R : Reads) (J : LookJobs W) (a : At) : List (Part V W Unit) :=
  (stages a.face).zipIdx.map fun x => partOf R J a x.1 x.2

/-- **The half**: the row at its place, typed at the jobs' own input. -/
def proverSideOfLookupAtOneOwner (R : Reads) (J : LookJobs W) (a : At) : Placed V W Unit := ⟨a.place, lookRow R J a⟩

/-- **The half, seated in a chain's letters.** Here wit gives the jobs' input, of what the chain's
halves are handed. No stop reads anything; what the chain's parts hand on stays as it is. -/
def proverSideOfLookupInChainAtOneOwner (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) : Placed V₁ W₁ X₁ :=
  ⟨a.place, (lookRow (V := Unit) R J a).map
    (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)⟩

/-! ## 4 The forms of simulators beside the parts -/

/-- Beside a stage that sends nothing: no coin; one round, in which nothing is shown. It reads
nothing that it is handed. -/
def quietSim (a : Addr) : Sim Pb :=
  { addr := a, takes := ⟨0, 0⟩, tell := fun _ _ _ _ _ => some [⟨[], []⟩] }

/-- Beside the part of a stage. Here i is its number in the row. -/
def simOf (a : At) (s : Stage) (i : Nat) : Sim Pb :=
  match s.call a.face with
  | some k => sumSim ⟨a.place, i⟩ k
  | none => quietSim ⟨a.place, i⟩

/-- One for each part of the row, in order. -/
def lookSims (a : At) : List (Sim Pb) := (stages a.face).zipIdx.map fun x => simOf a x.1 x.2

/-- The seated row, each part with the form beside it. -/
def lookPairs (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    List (Part V₁ W₁ X₁ × Sim Pb) :=
  (proverSideOfLookupInChainAtOneOwner R J wit a).parts.zip (lookSims a)

/-! ## 5 The stretches of coins that the row spends -/

/-- **A stretch of coins that a part of the row spends.** -/
structure Stretch where
  stage : Stage
  /-- the part's number in the row -/
  part : Nat
  /-- the stretch's name, as the part states it -/
  name : String
  /-- whose message its coins are -/
  owner : String
  /-- the number, in the segment's own count of scalars, of the first scalar that it is laid over -/
  first : Nat
  /-- how many entries, all of the extension field -/
  count : Nat
  deriving Repr

/-- **All stretches of a lookup's row**, in the order in which the parts state them. Here first is
the number, in the segment's count, of the first scalar that the lookup sends (the ledger's next
slot in front of it). A stretch of no entry is not listed: the leaves' call, which has no end value,
has its first stretch alone. -/
def stretches (a : At) (first : Nat) : List Stretch :=
  ((stages a.face).zipIdx.foldl
    (fun (y : List Stretch × Nat) x =>
      (y.1 ++
        (if x.1.own a.face == 0 then [] else
          [⟨x.1, x.2, sumName a.place x.2, maskRowRun, y.2, x.1.own a.face⟩]) ++
        (if x.1.tail a.face == 0 then [] else
          [⟨x.1, x.2, endName a.place x.2, maskRowRun, y.2 + x.1.own a.face, x.1.tail a.face⟩]),
       y.2 + x.1.slots a.face))
    ([], first)).1

/-- A stretch in words. -/
def Stretch.line (t : Stretch) : String :=
  s!"part {t.part} ({reprStr t.stage}): spent | {t.owner} | entries {t.first} .. " ++
    s!"{t.first + t.count - 1} | {t.count} | \"{t.name}\""

end ProofFile.Honest.K3

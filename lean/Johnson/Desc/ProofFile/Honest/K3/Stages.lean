-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Stages.lean: the honest side of the kind "lookup" (K3): the types
against which its files are written. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md, whose entries on stage, points, ask, job and face point to this file.

What is defined. The verifier's text is Johnson/Desc/First/Look/Via/Rounds.lean: `messagesV f` hears
a lookup's rounds, for arbitrary numbers `f` of the lookup (the structure `Face` of
Johnson/Desc/First/Look/K3LookupGeneral.lean; here `LFace`, since Honest/Frame.lean has a `Face` of its
own); `entriesV f` lists the same rounds as entries of the plan. The honest side follows that text
line for line. It is cut as the book cuts a row (Honest/BookOf.lean): a masked sumcheck is one part;
every other round is a part by itself.
  1 `Stage`, `stages`: the parts of a lookup's row, in order, by name.
  2 `Stage.call` (with `levelCall`), `Stage.draws`, `Stage.rounds`, `indexOf`, `firstRound`: a
    stage's public shape: the verifier's own calls, by name; the numbers of rounds.
  3 `Pts`: what the stages read of the challenges in front.
  4 `Hidden`, `Ask`: what the stages read of the prover's input.
  5 `StageJob`, `LookJobs`, `LookJobs.asked`: a stage's summand, as functions with code: a letter of
    the row.
  6 `At`: a lookup's public data at its place.

Imported. Files directly under Honest/.

Limits. Nothing here is compared with the verifier's text. Honest/K3/RowLaw.lean shows that the
stages' rounds are the verifier's, at two planes at least (`entries_stages`).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.First.Look.Via.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)

/-- The lookup's numbers, as the verifier's text has them. -/
abbrev LFace : Type := VerifiableInference.Desc.K3.Face

/-! ## 1 The stages -/

/-- **A part of a lookup's row, by name.** -/
inductive Stage where
  /-- "LKP shift": nothing sent; the shift theta is sampled -/
  | shift
  /-- "LKP": nothing sent; alpha is sampled -/
  | alpha
  /-- the tie's step s, from 0: a masked sumcheck without a variable -/
  | tie (s : Nat)
  /-- the parts' step i, from 0: a masked sumcheck without a variable -/
  | split (i : Nat)
  /-- "JOIN": nothing sent; mu elements are sampled -/
  | join
  /-- part i's key tree: the level with m variables: its masked sumcheck -/
  | key (i m : Nat)
  /-- "LINE" behind that level -/
  | keyLine (i m : Nat)
  /-- the table side's level number l, from 0: mu + l variables: its masked sumcheck -/
  | tab (l : Nat)
  /-- "LINE" behind that level -/
  | tabLine (l : Nat)
  /-- the leaves' masked sumcheck: no end value -/
  | leaves
  /-- "ZERO": nothing sent; mu + d elements are sampled -/
  | zero
  /-- the bits' masked sumcheck -/
  | bits
  deriving DecidableEq, Repr

/-- **The stages of a lookup, in the order of the rounds** (`entriesV`,
Johnson/Desc/First/Look/Via/Rounds.lean). -/
def stages (f : LFace) : List Stage :=
  (if f.shifted then [Stage.shift] else []) ++ [Stage.alpha] ++
    (List.range (f.planes - 1)).map Stage.tie ++
    (List.range (f.parts.length - 1)).map Stage.split ++
    [Stage.join] ++
    f.parts.zipIdx.flatMap (fun x =>
      (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]) ++
    (List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l]) ++
    [Stage.leaves, Stage.zero, Stage.bits]

/-! ## 2 A stage's public shape -/

/-- The call of a product level with m variables, as `First.ProdV.level` makes it, of the verifier's
own `levelVars` and `levelEnds`; at the empty point every variable's point is the stand-in 0, and a
shape reads no order. -/
def levelCall (m : Nat) : Call :=
  { lead := 0, vs := VerifiableInference.Desc.First.ProdV.levelVars m #[] (List.range m)
    ends := some VerifiableInference.Desc.First.ProdV.levelEnds }

/-- **A stage's call of the masked sumcheck**, points left as stand-ins: each is the call at which
`entriesV` makes that piece's entries. Nothing at a stage that sends nothing. -/
def Stage.call (f : LFace) : Stage → Option Call
  | .tie 0 => some (VerifiableInference.Desc.K3.noVar 3 3)
  | .tie (_ + 1) => some (VerifiableInference.Desc.K3.noVar 3 2)
  | .split _ => some (VerifiableInference.Desc.K3.noVar 2 2)
  | .key _ m => some (levelCall m)
  | .tab l => some (levelCall (f.mu + l))
  | .leaves => some { lead := 0, vs := VerifiableInference.Desc.K3.leafVars f #[], ends := none }
  | .bits => some (VerifiableInference.Desc.K3.bitsCall (List.replicate (f.mu + f.d) zeroE))
  | _ => none

/-- How many elements the one round of a stage that sends nothing samples; 0 at a sumcheck. -/
def Stage.draws (f : LFace) : Stage → Nat
  | .shift => 1
  | .alpha => 1
  | .join => f.mu
  | .keyLine _ _ => 1
  | .tabLine _ => 1
  | .zero => f.mu + f.d
  | _ => 0

/-- How many rounds a stage takes. -/
def Stage.rounds (f : LFace) (s : Stage) : Nat :=
  match s.call f with
  | some k => VerifiableInference.Desc.K3.roundsOf k
  | none => 1

/-- A stage's number in the row, from 0; the row's length where it does not stand there. -/
def indexOf (f : LFace) (s : Stage) : Nat := (stages f).idxOf s

/-- How many rounds of the lookup stand in front of a stage. -/
def firstRound (f : LFace) (s : Stage) : Nat :=
  (((stages f).take (indexOf f s)).map (Stage.rounds f)).sum

/-! ## 3 What is read of the challenges -/

/-- **What the stages read of the challenges in front**, in the verifier's own forms
(`messagesV`; `First.ProdV.layBack`, `stepDown`). A field whose challenges are not yet sampled holds
zeros. That no stage's summand reads it then is meant of the fillings; it is not shown here. -/
structure Pts where
  /-- the shift; 0 where there is none -/
  theta : E
  alpha : E
  /-- the samples of "JOIN", read in reverse: the table side's first point -/
  rhoT : Array E
  /-- part i, m: the point in front of its key tree's level with m variables: m coordinates, the
  highest bit first; at m := the part's number of levels: the tree's last point -/
  keyPt : Nat → Nat → Array E
  /-- l: the point in front of the table side's level number l: mu + l coordinates; at l := d: the
  leaves' point -/
  tabPt : Nat → Array E
  /-- the samples of "ZERO", read in reverse: the bits' point -/
  zeroPt : Array E
  /-- all challenges in front of the part, as they were heard, other places' too: for a caller whose
  keys hang on a challenge that was sampled in front of the lookup (the digits) -/
  heard : List Fmt.Drawn

/-! ## 4 What is read of the input -/

/-- **What a lookup's stages read of the prover's input**: the small structure at which its parts
are typed (`Part.lift`'s "wit" makes it of the input). -/
structure Hidden where
  /-- of the shift: part i's key at place x, below 2 ^ parts[i]; padding places hold their public
  key -/
  key : (theta : E) → (i x : Nat) → E
  /-- the row first, the plane second: of the count of the table's row u, below 2 ^ d, the bit of
  plane j, below planes. What an honest input meets beyond the type (a bit is 0 or 1; the counts fit
  the keys; at a proof file's shape a row that belongs to no call has all bits 0) is not stated
  here: see `LookIn.Meets` (Honest/K3/WitLaw.lean) -/
  bit : (u j : Nat) → E

/-- **The small structure at which every lookup's row is seated**: of the challenges heard in front
of the part. On a link's calls keys and bits hang on no challenge, and the function is constant; on
the digits of its smallness test the keys are digits of combinations under a sampled matrix, and the
function reads that sample, by its number. -/
abbrev Ask : Type := List Fmt.Drawn → Hidden

/-! ## 5 A stage's summand -/

/-- **What `SumJob` asks of one stage**, at the run's points (Honest/Sum.lean: `round`, `inY`,
`ends`; the lookup's calls have no lead). All lists hold the program's elements. -/
structure StageJob (W : Type) where
  /-- the summand's round polynomial in the next variable, all coefficients, lowest first: of the
  challenges of the variables in front -/
  round : W → Pts → List E → List E
  /-- the like in Y: of all variables' challenges, and of the end values' mask entries -/
  inY : W → Pts → List E → List E → List E
  /-- the true end values: of all variables' challenges -/
  ends : W → Pts → List E → List E

/-- **The summands of all stages**: a letter of the row. There are two fillings: the specification's
(Honest/K3/JobsSpec.lean: `specJobs`; at a shape `specJobsF`) and one that folds tables
(Honest/K3/JobsFast.lean: `fastJobs`). Honest/K3/LotRow.lean seats either at a site: `specFill`,
`fastFill`. At a stage that sends nothing the entry is not read. The row with a kept state
(Honest/K3/RowKeep.lean) gives a stage its summand in another way, not through this structure. -/
structure LookJobs (W : Type) where
  job : Stage → StageJob W

/-- Summands that are written at `Hidden`, as summands at `Ask`: each function makes the structure
of the challenges in front (`Pts.heard`) and goes on. -/
def LookJobs.asked (J : LookJobs Hidden) : LookJobs Ask :=
  ⟨fun s =>
    { round := fun w p rs => (J.job s).round (w p.heard) p rs
      inY := fun w p rs m => (J.job s).inY (w p.heard) p rs m
      ends := fun w p rs => (J.job s).ends (w p.heard) p rs }⟩

/-! ## 6 A lookup at its place -/

/-- **A lookup's public data at its place.** -/
structure At where
  place : Place
  face : LFace
  /-- how many rounds of the first chain stand in front of the place (`roundsInFront`) -/
  base : Nat

end ProofFile.Honest.K3

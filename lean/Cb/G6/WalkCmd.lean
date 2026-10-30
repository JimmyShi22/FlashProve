-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/WalkCmd.lean: two commands that walk the constants reached from a statement and report whether
a name of an honest prover is among them.

Definitions of commands. They are for tests: a statement on soundness should have no premise whose
type reaches an honest prover.

The walk. From a start set of constants it goes, to any depth, to every constant that is named in a
constant's type, in the value of a definition or of a constant of the kind `opaqueInfo`, and in the
constructors of an inductive type (so in the types of a structure's fields). Of a theorem the
statement alone is walked, not the proof. It stops at constants of Lean's, Std's and Mathlib's own
modules and those of their companions (`tw_foreign`). It takes at most `twSteps` steps; if these do
not suffice the command ends in an error.

The start sets. `#tw_walk c`: the constant c itself. `#tw_premises c`: the constants named in the
types of c's binders alone (every bound variable and hypothesis of the statement, not its
conclusion). With the word "clean" it is an error if the statement shows no binder, or if its
conclusion, behind the binders, is not `Reduction.Know` or `KnowAt` written out. So a theorem stated
as "t : Spec.t" is refused, not passed. Nothing is unfolded.

When it rings. At a constant one of whose name's components is on the list `twRing`, or holds a part
on the list `twParts`. In a walk from premises' types also at `twRingPrem`, the exact relation of a
joint (`IOR.Rels.rel`), by a second walk, and at the constants that take a joint apart
(`IOR.Rels.rec`, `casesOn`, `recOn`). That walk leaves out, of a definition whose result is a joint
and whose value is the record written out, the field `rel` alone; its `relR`, `on` and `core` are
walked. So a premise "A.rel x y w", or a definition that hides one, rings; a builder of joints whose
own `relR`, `on` or `core` reads the exact relation rings too; a binder that only names a lawful
joint does not. What the first walk reaches of `twRingPrem` and the second does not is noted in the
message.

The words. A line without a word only prints: only lines whose message shows [clean] or [rings] have
tested anything. "clean": an error if it rings. "rings": an error if it does not ring (a control). A
ring is a question, not yet a fault: the lists are wide on purpose. Good, inP, Sim, Mu, Acc are also
lawful names elsewhere in the library, and Strat is also the type of a cheating prover.

Limits: `#tw_premises` never looks at the places of the conclusion, and `#tw_walk` only notes `rel`
there: a theorem whose condition on statements is "fun a => ∃ w, A.rel a.1 a.2 w" passes under both
commands with the word "clean". The walk does not test whether a premise reads the messages, a
witness or a transcript: a premise on the messages' counts bears no listed word. It goes by names: a
notion of an honest side under a name that bears no listed word is not seen. What enters through a
proof is not walked (a proof cannot make a premise). Universe levels and instance arguments are
walked as any other term.

-/
import Lean
import Ior.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole.Walk
open Lean Elab Command

/-- Components of names at which the walk rings: the types of honest sides; the library's bundles
and records that take an honest side in their type; the honest sides' own names in the masked
sumcheck and the lookup. -/
def twRing : List String :=
  ["Honest", "Strat", "Sender", "MaskData",
   "GoodAt", "GoodB", "GoodM", "Good", "HonAt", "ShortH", "ShortHC", "Acc", "Sim", "SimT", "HVZK",
   "hon", "honC", "honE", "honQ", "honMid", "honOut", "pStrat", "shortHon", "shortHonC",
   "shortStrat", "shortStratC", "sStrat", "sStrat0",
   "IsMult", "hbit", "hmult", "Mu", "MuOK", "MuOn", "ValidMu", "inP", "midP"]

/-- Rings in a premise's type alone: the exact relation of a joint (`IOR.Rels.rel`). A joint is one
record with both relations. Whoever names a joint that is built from another (`PscPar.baseRels`,
`Sig.over`) reaches the projection `rel` through that definition's value, the library's own
`sigLift_know` too. So in a walk from a whole constant it is noted, not rung. -/
def twRingPrem : List String := ["rel"]

/-- The roots of the modules at whose constants the walk stops. -/
def tw_foreign : List Name :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph,
   `LeanSearchClient, `Cli]

/-- Is the constant of this library? -/
def own (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => !tw_foreign.contains (env.header.moduleNames[i.toNat]!).getRoot
  | none => true

/-- The constants that a constant names: in its type, its value if it is a definition, its
constructors if it is an inductive type. -/
def usedOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => t ++ d.value.getUsedConstants
  | .opaqueInfo o => t ++ o.value.getUsedConstants
  | .inductInfo i => t ++ i.ctors.toArray
  | _ => t

/-- The head of what a type ends in, behind its binders. -/
def resultHead : Expr → Expr
  | .forallE _ _ b _ => resultHead b
  | .letE _ _ _ b _ => resultHead b
  | .mdata _ e => resultHead e
  | e => e.getAppFn

/-- A builder of joints: a definition whose result is a joint (`IOR.Rels`), as `PscPar.baseRels` and
`Sig.over`. A joint is one record with both relations, so such a definition's value names the
projection `rel` of the joint from which it builds, whoever uses it. -/
def isJoint (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => (resultHead ci.type).isConstOf `Iop.IOR.Rels
  | _ => false

/-- Of the value of a builder of joints all but the field `rel`, if the value is the record written
out behind its binders; none if it is not. To take the type alone would let a builder's own `relR`,
`on` or `core` read the exact relation unseen. -/
def jointRest : Expr → Option (Array Name)
  | .lam _ t b _ => (jointRest b).map (t.getUsedConstants ++ ·)
  | .mdata _ e => jointRest e
  | e =>
    if e.getAppFn.isConstOf ``Iop.IOR.Rels.mk && e.getAppNumArgs == 8 then
      let a := e.getAppArgs   -- K X E W rel relR on core
      some ((a.extract 0 4 ++ a.extract 5 8).foldl (fun r x => r ++ x.getUsedConstants) #[])
    else none

/-- The constants that a builder of joints names, without its field `rel`. -/
def thinUsed (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo d => ci.type.getUsedConstants ++ (jointRest d.value).getD d.value.getUsedConstants
  | _ => usedOf ci

/-- The number of steps that a walk may take. -/
def twSteps : Nat := 100000000

/-- The walk, for at most the given number of steps. With `thin`, of a builder of joints whose value
is the record written out the field `rel` is not walked; all else is. The second part of the result
says whether the steps sufficed. -/
def reach (env : Environment) (thin : Bool) : Nat → List Name → NameSet → NameSet × Bool
  | _, [], seen => (seen, true)
  | 0, _ :: _, seen => (seen, false)
  | k + 1, n :: r, seen =>
    if seen.contains n || !own env n then reach env thin k r seen
    else match env.find? n with
      | none => reach env thin k r seen
      | some ci =>
        let next := if thin && isJoint ci then thinUsed ci else usedOf ci
        reach env thin k (next.toList ++ r) (seen.insert n)

/-- Beside the list: parts of a component at which the walk rings (so at HonestV, BatchHonestProver, honN
and their like). -/
def twParts : List String := ["Hon", "hon", "Prover", "prover", "Strat"]

/-- Does s hold p? -/
def hasPart (s p : String) : Bool := (s.splitOn p).length > 1

/-- Is a component of the name on the list? -/
def ringsBy (l : List String) (n : Name) : Bool := n.components.any fun c => l.contains c.toString
/-- Does the walk ring at the name? -/
def ringsMain (n : Name) : Bool :=
  ringsBy twRing n || n.components.any fun c => twParts.any (hasPart c.toString)

/-- The constants named in the binders' types (a `let` counts with its value), and the number of
binders. -/
def binderConsts : Expr → Array Name × Nat
  | .forallE _ t b _ => let r := binderConsts b; (t.getUsedConstants ++ r.1, r.2 + 1)
  | .letE _ t v b _ =>
    let r := binderConsts b; (t.getUsedConstants ++ v.getUsedConstants ++ r.1, r.2 + 1)
  | .mdata _ e => binderConsts e
  | _ => (#[], 0)

/-- The conclusions that `#tw_premises c clean` takes: `Reduction.Know` or `KnowAt` written out
behind the binders. A statement whose head is a definition shows no binder, and a premise could
stand inside another conclusion: both are errors, not passes. Nothing is unfolded: unfolding would
run on into `Know` itself. -/
def goodHead (e : Expr) : Bool :=
  match (resultHead e).constName? with
  | some n => n == `Iop.Reduction.Know || n == `TWhole.KnowAt
  | none => false

/-- Walks, and reports by the word given. -/
def report (what : String) (c : Name) (start : List Name) (mode : String) (prem : Bool) :
    CommandElabM Unit := do
  let env ← getEnv
  let (seen, ok₁) := reach env false twSteps start {}
  let (thin, ok₂) := reach env true twSteps start {}
  unless ok₁ && ok₂ do
    throwError s!"WALK-STEPS: the walk from {c} did not end within {twSteps} steps: nothing is said"
  let hit1 := seen.toList.filter ringsMain
  -- the exact relation can also be reached by taking a joint apart (match, casesOn, rec)
  let apart : List Name := [``Iop.IOR.Rels.rec, ``Iop.IOR.Rels.casesOn, ``Iop.IOR.Rels.recOn]
  let hit2 :=
    if prem then thin.toList.filter (fun n => ringsBy twRingPrem n || apart.contains n) else []
  let hit := (hit1 ++ hit2).toArray.qsort Name.lt
  let note :=
    ((seen.toList.filter (ringsBy twRingPrem)).filter fun n => !hit2.contains n).toArray.qsort
      Name.lt
  let msg := s!"TW-WALK [{mode}] {what} {c}: {seen.size} constants reached (Lean's, Mathlib's " ++
    s!"and their companions' own not counted); RINGS: {hit.toList}; NOTED: {note.toList}"
  unless ["", "clean", "rings"].contains mode do throwError s!"TW-WALK: unknown word «{mode}»"
  if mode == "clean" && !hit.isEmpty then throwError msg
  if mode == "rings" && hit.isEmpty then throwError (msg ++ " : A CONTROL THAT MUST RING DID NOT")
  logInfo msg

syntax (name := twWalk) "#tw_walk " ident (&" clean" <|> &" rings")? : command
syntax (name := twPrem) "#tw_premises " ident (&" clean" <|> &" rings")? : command

/-- The first atom of a piece of syntax, down to the given depth. -/
def firstAtom : Nat → Syntax → Option String
  | _, .atom _ v => some v
  | k + 1, .node _ _ args => args.findSome? (firstAtom k)
  | _, _ => none

/-- The word behind the constant: "clean", "rings" or none. -/
def modeOf (stx : Syntax) : String := ((firstAtom 8 stx[2]).getD "").replace " " ""

@[command_elab twWalk] def elabWalk : CommandElab := fun stx => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  report "(the constant)" c [c] (modeOf stx) false

@[command_elab twPrem] def elabPrem : CommandElab := fun stx => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some ci := (← getEnv).find? c | throwError "unknown constant"
  let (cs, n) := binderConsts ci.type
  if modeOf stx == "clean" then
    if n == 0 then
      throwError s!"TW-WALK: {c} shows NO BINDER: nothing would be tested: state the theorem " ++
        "with its binders written out"
    unless goodHead ci.type do
      throwError s!"TW-WALK: the conclusion of {c} is not Reduction.Know | KnowAt written out " ++
        "behind its binders: state it so"
  report s!"(the types of the {n} binders of)" c cs.toList (modeOf stx) true

end TWhole.Walk

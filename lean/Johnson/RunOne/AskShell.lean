-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskShell.lean: what the files of lean/Ask/ that run the verifier along lists
(verifyWholeL, OnBytes/Maker/ListedWhole.lean) of a whole file share: the stages behind the parser
as plain values, each test behind a thunk; their print, one flushed line a stage on the error
stream; and their answers as plain data. Definitions; they have code. General in the kit C.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

What it is for. A file of lean/Ask/ is compiled by nobody and can be imported by nobody. So what
they share stands here, in the library, where "lake build" holds it; `In`, `Behind`, `Front`,
`Judge`, `partsOf` and `tellOf` serve one entry in this library, Johnson/RunOne/AskKey.lean; beside
it its two files of laws name them (AskShellLaws.lean, AskKeyLaws.lean). Nothing here reads a file
from disk; nothing here is evaluated.

Main names:
  `In`: what the stages are handed: the letters of the verifier along lists (verifyWholeL,
    OnBytes/Maker/ListedWhole.lean) at a whole file, the family of oracle answers at which it is
    run, and a test on oracle queries.
  `Behind`, `behindOf`: the chain's run; then, behind thunks, the twenty-three named tests
    (OnBytes/Maker/ListedSteps.lean) and the verifier's own two halves (strictBBL, afterBOL).
  `Behind.parts`: the tests with their answers, "written" and the verdict, as plain data.
  `Behind.tell`: these values, each printed as soon as it is made.
  `Front`: what a file's own entry makes in front of the verifier: a refusal of the parsed record's
    reader or of the typing; the tests on the claim; the stages' input.
  `Judge`: the name of what judges, the law that ties it to the compiled verifier, and its run.
  `partsOf`, `tellOf`: a whole run as plain data, and with its print.
  `runOk`: the runner: the tree's value at the family, the names of the oracles asked (for the
    print; no law speaks of them), and whether the test has passed every query asked. A coin is
    taken as 0 and leaves no name.
Limits: definitions alone. That the verdict is the value of verifyWholeL, and "written && verdict"
its guarded run's: Johnson/RunOne/AskShellLaws.lean. That all twenty-three tests say yes just where
the two halves do: wholeSteps_yes (OnBytes/Maker/ListedStepsLaws.lean). Nothing on time or memory.
Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedSteps
import OnBytes.Maker.SilentParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Compile hiding ON
open OnBytes.Maker _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## Lines -/

/-- The clock of the last line. -/
abbrev Clock : Type := IO.Ref Nat

/-- One line on the error stream, flushed, with the milliseconds since the line before. Why that
stream: Lean keeps what a command writes on standard output until the command has ended; what it
writes on the error stream goes out at once where the option stderrAsMessages is false. -/
def say (c : Clock) (s : String) : IO Unit := do
  let t1 ← IO.monoMsNow
  IO.eprintln s!"{s} [{t1 - (← c.get)} ms]"
  (← IO.getStderr).flush
  c.set (← IO.monoMsNow)

def yn (b : Bool) : String := if b then "yes" else "NO"

/-- One test: its line, as soon as it is made. -/
def test (c : Clock) (x : String × Thunk Bool) : IO (String × Bool) := do
  let b := x.2.get
  say c s!"{x.1}: {yn b}"
  pure (x.1, b)

/-- Tests in a row, up to the first that says no. -/
def upToNo : List (String × Thunk Bool) → List (String × Bool)
  | [] => []
  | x :: l => if x.2.get then (x.1, true) :: upToNo l else [(x.1, false)]

/-- The number of all leaves in lists of leaves. -/
def leavesIn (l : Leaves) : Nat :=
  (l.map fun x => (x.1.map List.length).sum + (x.2.map List.length).sum).sum

/-- The oracle's name, for the print. -/
def onName : OracleName → String
  | .leaf => "leaf"
  | .node => "node"
  | .rleaf => "rleaf"
  | .rnode => "rnode"
  | .fb .test => "fb.test"
  | .fb .link => "fb.link"
  | .fb .onl => "fb.onl"
  | .g .test => "g.test"
  | .g .link => "g.link"
  | .g .onl => "g.onl"
  | .ann => "ann"
  | .other => "other"
  | .fbw _ _ => "fbw"

/-- The mark of a query that the test has turned away. -/
def awayMark : String := "TURNED AWAY: "

/-- How many queries of a log stand under each name. -/
def byName (log : Array String) : List (String × Nat) :=
  log.toList.eraseDups.map fun n => (n, (log.filter fun x => x == n).size)

/-- A runner of trees of oracle queries: every coin 0; g: the family of answers; ok: a test on
queries. It returns the tree's value, the names of the oracles asked, in order, and whether the test
has passed every query that was asked. -/
def runOk {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : Nat} {α : Type}
    (ok : (o : OracleName) → domOf 256 L o → Bool) (g : Rom.Fam (typedOracleFamily 256 K L)) :
    OComp (typedOracleFamily 256 K L) α → Array String → Bool → α × Array String × Bool
  | .pure a, acc, b => (a, acc, b)
  | .sample _ k, acc, b => runOk ok g (k 0) acc b
  | .query o q k, acc, b =>
    runOk ok g (k (g o q)) (acc.push (if ok o q then onName o else awayMark ++ onName o))
      (b && ok o q)

/-! ## The stages behind the parser -/

/-- The stages as values: the chain has been run; the rest stands behind thunks. -/
structure Behind where
  /-- some numbers, for the print -/
  numbers : String
  /-- the chain returns a value -/
  returned : Bool
  chainLog : Array String
  /-- the test on queries has passed every query of the chain -/
  chainOk : Bool
  /-- the leaves of the file's own trees and the positions of the stored table that are read -/
  read : Nat × Nat
  steps : Steps
  strict : Thunk Bool
  after : Thunk (Bool × Array String × Bool)

section Stages
variable {Xi X : Type} (C : _root_.Run.PQ.CK) (D : WholeD) (tF₀ : FrontMsg (List OnBytes.E))
  (tJ₀ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
  (silent : Xi → FrontMsg (List OnBytes.E) →
    _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (rn₀ : Xi → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool) (Kn : Nat)
  (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k) (L : BatchProtocolWithLeafBody Unit X) (t : _root_.Compile.Tag)

/-- The rounds of the file's protocol. -/
abbrev ShAt := (chainsOf C D tF₀ tJ₀ ByteArray.empty).sh

/-- The file's protocol. -/
abbrev QAt := (wholeDesc C D tF₀ tJ₀ ByteArray.empty silent rn₀).batch

/-- The chain's value. -/
abbrev ChainVal := Option (Rho (ShAt C D tF₀ tJ₀) × RootsOfChain 256 (ShAt C D tF₀ tJ₀) × Phase 256)

/-- What the stages are handed: the letters of the verifier along lists; g: the family of oracle
answers at which it is run; ok: the test on queries. -/
structure In where
  embP : PlainPart (ShAt C D tF₀ tJ₀) (chainsOf C D tF₀ tJ₀ ByteArray.empty).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)
  xo : Option X
  g : Rom.Fam (typedOracleFamily 256 (Kn + 1) L)
  ok : (o : OracleName) → domOf 256 L o → Bool
  eS : (p : OPos (ShAt C D tF₀ tJ₀)) → OSym (ShAt C D tF₀ tJ₀) p → Body L
  eE : _root_.Run.PQ.SgX → Body L
  sMT : Nat
  sFS : Nat
  dR : Nat
  cms : List (Dig 256)
  x : Xi
  π : OneProtocolProof 256 (QAt C D tF₀ tJ₀ silent rn₀)
  /-- every leaf of the file's own trees at which an opening stands in π: to be made by the caller,
  on the verifier's side, of the same record as π, never from a parser's word; nothing here tests it
  (the Limits of OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean) -/
  own : Leaves
  /-- the same for the stored table's positions -/
  listed : List (oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Pos

/-- The chain as a tree of queries, as the verifier along lists calls it. -/
def chainTree (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) : TypedOracleComputation 256 (Kn + 1) L (ChainVal C D tF₀ tJ₀) :=
  recomputeChain t A.cms A.xo A.π.salt A.π.rtreq (ShAt C D tF₀ tJ₀)
    (chainsOf C D tF₀ tJ₀ ByteArray.empty).ann
    (wiresOf C Kn chal D tF₀ tJ₀ ByteArray.empty).sh A.embP 0 .first A.π.roots
    A.π.plains

/-- The leaves of the file's own trees that are read, at the chain's draws. -/
abbrev rdAt (ρ : Rho (ShAt C D tF₀ tJ₀)) : Leaves := rdWhole C D tF₀ tJ₀ ByteArray.empty ρ

/-- The positions of the stored table that are read. -/
abbrev rdEAt (ρ : Rho (ShAt C D tF₀ tJ₀)) : List (oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Pos :=
  rdEWhole C D tF₀ tJ₀ ByteArray.empty ρ

/-- The verifier's first half behind the chain: the strict format. -/
def strictAt (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) (rd : Leaves)
    (rdE : List (oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Pos) (rts : RootsOfChain 256 (ShAt C D tF₀ tJ₀))
    (ph : Phase 256) : Bool :=
  strictBBL (K := Kn + 1) A.sMT A.sFS (QAt C D tF₀ tJ₀ silent rn₀)
    (wiresOf C Kn chal D tF₀ tJ₀ ByteArray.empty).sh (wlOne D.a) A.dR A.π A.own
    A.listed rd rdE rts ph

/-- Its second half, as a tree of queries. -/
def afterAt (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) (rd : Leaves)
    (rdE : List (oneExternalString (2 ^ D.a) _root_.Run.PQ.SgX).Pos) (ρ : Rho (ShAt C D tF₀ tJ₀))
    (rts : RootsOfChain 256 (ShAt C D tF₀ tJ₀)) (ph : Phase 256) : TypedOracleComputation 256 (Kn + 1) L Bool :=
  afterBOL (L := L) (QAt C D tF₀ tJ₀ silent rn₀)
    (wiresOf C Kn chal D tF₀ tJ₀ ByteArray.empty).sh (wlOne D.a) (nOpenW D)
    (maxDepthW D) A.eS A.eE A.dR A.cms A.x A.π rd rdE ρ rts ph

/-- The stages behind a run r7 of the chain. -/
def behindAt (A : In C D tF₀ tJ₀ silent rn₀ Kn L t)
    (r7 : ChainVal C D tF₀ tJ₀ × Array String × Bool) : Behind :=
  let numbers := s!"bits of an opening's salt {A.sMT}; bits of the chain's salt {A.sFS}; depth " ++
    s!"of the binding tree {A.dR}; digests handed to the chain {A.cms.length}; openings allowed " ++
    s!"{nOpenW D}; depth allowed {maxDepthW D}"
  match r7.1 with
  | none =>
    { numbers := numbers, returned := false, chainLog := r7.2.1, chainOk := r7.2.2,
      read := (0, 0), steps := [], strict := Thunk.mk fun _ => false,
      after := Thunk.mk fun _ => (false, #[], true) }
  | some (ρ, rts, ph) =>
    let rd := rdAt C D tF₀ tJ₀ ρ
    let rdE := rdEAt C D tF₀ tJ₀ ρ
    { numbers := numbers, returned := true, chainLog := r7.2.1, chainOk := r7.2.2
      read := (leavesIn rd, rdE.length)
      steps := wholeSteps (L := L) C Kn chal D tF₀ tJ₀ ByteArray.empty silent
        rn₀ A.sMT A.sFS A.eS A.eE A.dR A.cms A.x A.π A.own A.listed A.g ρ rts ph
      strict := Thunk.mk fun _ => strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A rd rdE rts ph
      after := Thunk.mk fun _ =>
        runOk A.ok A.g (afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A rd rdE ρ rts ph) #[] true }

/-- **The verifier along lists in stages**: the chain is run; the twenty-three named tests and the
verifier's own two halves behind the chain stand behind thunks. -/
def behindOf (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) : Behind :=
  behindAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A
    (runOk A.ok A.g (chainTree C D tF₀ tJ₀ silent rn₀ Kn chal L t A) #[] true)

end Stages

/-- The chain's line. -/
def chainLine : String := "chain: it ran to its end"

/-- "written": the test on queries has passed every query that the verifier asks: those of the
chain, and, where its first half behind the chain says yes, those of its second half (where the
first half says no the verifier asks no more). -/
def Behind.written (B : Behind) : Bool := B.chainOk && (!B.strict.get || B.after.get.2.2)

/-- The line of "written". -/
def writtenLine : String := "written: every oracle query that was asked has its hash call"

/-- The verdict: the chain returns, and the verifier's own two halves behind it say yes. -/
def Behind.verdict (B : Behind) : Bool := B.returned && B.strict.get && B.after.get.1

/-- **The tests with their answers, "written" and the verdict.** -/
def Behind.parts (B : Behind) : List (String × Bool) × Bool × Bool :=
  ((chainLine, B.returned) :: (B.steps.map fun x => (x.1, x.2.get)) ++ [(writtenLine, B.written)],
    B.written, B.verdict)

/-- **These values, each printed as soon as it is made.** At the values that behindOf makes it
returns what Behind.parts returns: by reading; no theorem. -/
def Behind.tell (clk : Clock) (B : Behind) : IO (List (String × Bool) × Bool × Bool) := do
  say clk s!"{chainLine}: {yn B.returned}"
  say clk s!"numbers: {B.numbers}"
  say clk s!"chain: oracle queries (oracle, number): {byName B.chainLog}"
  say clk s!"chain: every oracle query has a hash call in the format: {yn B.chainOk}"
  let mut lines : List (String × Bool) := [(chainLine, B.returned)]
  if B.returned then
    say clk (s!"to be read: leaves of the file's own trees {B.read.1}; positions of the stored " ++
      s!"table {B.read.2}")
    for s in B.steps do
      lines := lines ++ [← test clk s]
    say clk s!"decides the verdict, part 1 of 2 (strictBBL): {yn B.strict.get}"
    if B.strict.get then
      say clk s!"decides the verdict, part 2 of 2 (afterBOL): {yn B.after.get.1}"
    else
      say clk "decides the verdict, part 2 of 2 (afterBOL): not run: part 1 says NO"
    say clk ("the 23 named tests together say what parts 1 and 2 say: " ++
      yn (B.steps.yes == (B.strict.get && B.after.get.1)))
    if B.strict.get then
      say clk s!"behind the chain: oracle queries (oracle, number): {byName B.after.get.2.1}"
      say clk (s!"behind the chain: every oracle query has a hash call in the format: " ++
        s!"{yn B.after.get.2.2}")
  say clk s!"{writtenLine}: {yn B.written}"
  pure (lines ++ [(writtenLine, B.written)], B.written, B.verdict)

/-! ## A whole run -/

/-- What a file's own entry makes in front of the verifier. early: who refused before any test (the
parsed record's reader, the typing, ..), and its words. notes: lines of numbers, for the print.
lines: the tests in front of the verifier, in order, up to the first that says no. guard: the last
of them, where it is reached: the one test that stands in the judge's law beside "written" and the
verdict. input: the stages' input, where all of them say yes. -/
structure Front (In : Type) where
  early : Option (String × String) := none
  notes : List String := []
  lines : List (String × Bool) := []
  guard : Option Bool := none
  input : Option In := none

/-- What judges: its name and the law that ties it to the compiled verifier, both printed, and its
run in stages. -/
structure Judge (In : Type) where
  name : String
  law : String
  /-- the name of the answer's last part: guard, "written" and the verdict together -/
  last : String
  run : In → Behind

/-- How a run ended. stopped: it ended before any test, who ended it and why. lines: every test with
its answer, in the order of the print. -/
structure Ended where
  stopped : Option (String × String) := none
  lines : List (String × Bool) := []
  /-- every test in front of the verifier has said yes -/
  front : Bool := false
  guard : Option Bool := none
  written : Option Bool := none
  verdict : Bool := false

/-- Guard, "written" and the verdict together: the left side of the judge's law. none: the run has
not reached the guard, or the guard says yes and the verifier was not run. -/
def Ended.together (e : Ended) : Option Bool :=
  match e.guard with
  | none => none
  | some false => some false
  | some true => e.written.map fun w => w && e.verdict

/-- "written" and the verdict together. none: the verifier was not run. -/
def Ended.last (e : Ended) : Option Bool := e.written.map fun w => w && e.verdict

/-- The answer of a run: it did not stop; every test in front of the verifier has said yes, the
guard among them; and "written" and the verdict say yes. -/
def Ended.answer (e : Ended) : Bool :=
  e.last == some true && e.stopped.isNone && e.front && e.guard == some true

/-- The names of the tests that said no, up to the colon. -/
def Ended.noes (e : Ended) : List String :=
  (e.lines.filter fun x => !x.2).map fun x => (x.1.splitOn ":").headD x.1

/-- The first test that said no. The line "after 5" is the nine lines "accept" together and stands
before them: it is named only where none of these says no. -/
def Ended.firstNo (e : Ended) : Option String :=
  (OnBytes.Maker.firstNo (e.lines.filter fun x => !x.1.startsWith "after 5")).orElse fun _ =>
    OnBytes.Maker.firstNo e.lines

/-- **A whole run as plain data.** -/
def partsOf {In : Type} (J : Judge In) (F : Front In) : Ended :=
  match F.early, F.input with
  | some e, _ => { stopped := some e, lines := F.lines }
  | none, none => { lines := F.lines, front := F.lines.all fun x => x.2, guard := F.guard }
  | none, some A =>
    let r := (J.run A).parts
    { lines := F.lines ++ r.1, front := F.lines.all fun x => x.2, guard := F.guard,
      written := some r.2.1, verdict := r.2.2 }

/-- The line that stands under every yes. -/
def notAVerification : String :=
  "THIS YES IS NOT A VERIFICATION. It says only that this one run passed its tests. The Lean " ++
  "library does not prove the soundness of the protocol that was run. " ++
  "The protocol's own checks were written by hand after the C++ verifier. More " ++
  "limits: the comment at the top of the file in lean/Ask/ that was run."

/-- **A whole run with its print.** At a judge whose run is behindOf it returns what partsOf
returns: by a reading of the two texts; no theorem. -/
def tellOf {In : Type} (clk : Clock) (J : Judge In) (F : Front In) : IO Ended := do
  for s in F.notes do say clk s
  for x in F.lines do say clk s!"{x.1}: {yn x.2}"
  let front := F.lines.all fun x => x.2
  let e : Ended ←
    match F.early, F.input with
    | some e, _ => pure ({ stopped := some e, lines := F.lines } : Ended)
    | none, none => pure ({ lines := F.lines, front := front, guard := F.guard } : Ended)
    | none, some A => do
      say clk s!"verifier run: {J.name}"
      say clk s!"theorem cited, not checked by this run: {J.law}"
      say clk "--- no term is called beside the steps: the answer is the steps' own"
      let r ← (J.run A).tell clk
      let e0 : Ended := { lines := F.lines ++ r.1, front := front, guard := F.guard,
                          written := some r.2.1, verdict := r.2.2 }
      say clk s!"THE FIRST NO: {e0.firstNo.getD "none"}"
      say clk (s!"written (every oracle query had its hash call): {yn r.2.1}; verdict (the " ++
        s!"verifier accepts): {yn r.2.2}")
      say clk ("both together (no value where an oracle query has no hash call): " ++
        (if r.2.1 then yn r.2.2 else "no value"))
      say clk s!"{J.last}: {(e0.together.map yn).getD "not reached"}"
      pure e0
  match e.stopped with
  | some s => say clk s!"IT STOPPED BEFORE AN ANSWER: {s.1}: {s.2}"
  | none =>
    if e.written.isNone then say clk s!"THE FIRST NO: {e.firstNo.getD "none"}"
    say clk s!"ANSWER (every test before the verifier, written and verdict): {yn e.answer}"
    if e.answer then say clk notAVerification
  pure e

/-- A variable of the environment, or what stands for it. -/
def envOr (name dflt : String) : IO String := do
  pure ((← IO.getEnv name).getD dflt)

/-- A text without the blanks at its two ends. -/
def trimmed (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile
    Char.isWhitespace).reverse

end Johnson.RunOne.Ask

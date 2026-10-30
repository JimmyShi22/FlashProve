-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryProg.lean: the program for the entry file, one of a proof's three files: an
untrusted parser, then the closed check of OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean (the check with
all parameters fixed: a closed term) in a form written to be run, then the test of the commitment
ID. The hash function on bytes is an argument O; the program that is meant to run is `entryMain`, at
`Fmt.oracle` (Lean's BLAKE2b).

States. Definitions only. `idOfG`, `partAt`: the terms of the theorems (EntryProgLaws.lean).
`runAt`, `idRunO`, `cRun`, `oBO`: the forms that run. `stateAt` (trusted), `parseE` (untrusted),
`entryMainO O`, `entryMain`.
Under. No hypothesis.
Does not show.
  1. What the commitment ID's string holds: this file calls that definition by name.
  2. Anything of `parseE`: it is untrusted, and it hashes by a fixed hash, not by O.
  3. That the forms that run finish in practical time: no theorem says so; only a run can show it.
  4. Any test of `a.further` beyond the check itself: its root and an ID-like hash are printed only.
  5. That the salt `a.out.run` is the hash the format's verifier computes: size and non-zero only.
  6. Anything on soundness.
  7. Anything on the other two of a proof's three files.
  8. That the files are accepted: a yes speaks of the value that the parser returned, not of them.
  9. That `idOfG` at the realised oracle is the format's `Fmt.publishedID`.
 10. That any checker, public string or bound of the library covers the hash call for the ID.
 11. Use at another O: the parser still hashes by the fixed hash and will refuse nearly everything.
 12. That the program ever returns 0: only a run can show that, and this file records none.
 13. By a theorem, that the trusted side holds no hash but O.
 14. The warning "not a verification" (lower profile, fewer bits) of verify-on-bytes: never printed.
 15. That `stageO`'s label agrees with `runAt`: it serves messages only; no theorem connects them.
 16. No bits are asked; parameters are fixed.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.Claim
import OnBytes.TypedOracleCompiler.Slice.EntryRunBytes
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictRun
import OnBytes.ChecksWithHashAsArgument.M.Key.Table

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.EntryPageSafe (gOf)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of seedEntry seedOfDrawnC)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ scAt)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)

/-- The commitment ID through g, of a table t: the port's asking form, at the
hash that g induces and at g's own digest of the three public files; in hex. -/
def idOfG (sh : OnBytes.Params.IndexShape) (cfg : Cfg) (t : OnBytes.Params.TableName) (g : Fam (rom 256)) :
    String :=
  Fmt.hex (OnBytes.TwoPort.M.Key.commitmentId (m := Id) (Fmt.HO (_root_.Run.oB (g ()))) sh
    (dgOf cfg (own₀ (pubS₀ cfg) g)) t)

/-- For a run: the digest of the three public files through O: hashed once; 32 bytes. -/
def cRun (cfg : Cfg) (O : ByteArray → ByteArray) : ByteArray :=
  _root_.Run.digToBytes (_root_.Run.digS (O (TypedOracleCompiler.Run.EntryPageSafe.toBytesT (scAt cfg))))

/-- For a run: the function on bytes that `gOf O` induces: O is called once. -/
def oBO (O : ByteArray → ByteArray) (b : ByteArray) : ByteArray :=
  _root_.Run.digToBytes
    (_root_.Run.digS (O (TypedOracleCompiler.Run.EntryPageSafe.toBytesT (_root_.Run.bytesToBits b))))

/-- For a run: `idOfG`'s text at a digest c that is laid already. -/
def idRunO (sh : OnBytes.Params.IndexShape) (c : ByteArray) (t : OnBytes.Params.TableName)
    (O : ByteArray → ByteArray) : String :=
  Fmt.hex (OnBytes.TwoPort.M.Key.commitmentId (m := Id) (Fmt.HO (oBO O)) sh c t)

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- `entryPartO`'s text with the stage's word in the place of the truth value: "P" (the pins), "A"
(the typing), "S" (the seeds' comparison), "V" (the lax verifier of Link), else "YES". Words alone.
-/
def stagePartO (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE)
    (O : ByteArray → ByteArray) : String :=
  if pinsFit (entryXD G c) G.q.link.table then
    match assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => "A"
    | some π =>
      if cmpEL (entryXD G c) (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)
          (seedOfDrawnC G.q.link.table.cubeBits G.q.link.table.answers)
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] 0
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2 then
        if laxEL (entryXD G c) _ (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
          (ownES (entryXD G c) (hok c hc))
          (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (fun _ => TSE (entryXD G c) (seedEntry G.q.link.table.cubeBits G.q.link.table.answers))
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a) π then "YES" else "V"
      else "S"
  else "P"

end TypedOracleCompiler.Slice

namespace OnBytes.ShellOf.EntryProg

open OnBytes.ShellOf.Claimed
open OnBytes.Tie (AskedE EntryGround)
open TypedOracleCompiler.Slice (prepE entryXD idOfG cRun idRunO stagePartO askedFit runEntryFull
  runEntrySmall)
open OnBytes.Slice.Shapes (Cfg)
open Rom

/-- The three public files as the check takes them. -/
def cfgOf (c : OnBytes.Params.StdCfg) : Cfg := ⟨c.pol, c.lay, c.KL⟩

/-- THE VERIFIER OF WHICH THE THEOREM SPEAKS, the hash function an argument: a check V of the entry
file on plain data says yes at the claim's three public files, and the commitment ID that g gives of
these files and of the value's first table is the claim's. -/
def partAt (V : Cfg → AskedE → Fam (rom 256) → Bool) (sh : OnBytes.Params.IndexShape) (g : Fam (rom 256))
    (cl : Claim) (a : AskedE) : Bool :=
  V (cfgOf cl.cfg) a g && (idOfG sh (cfgOf cl.cfg) a.first g == cl.id)

/-- WHAT RUNS, a hash function on bytes an argument: a form for a run R of the check; the ID's
comparison at the digest laid once. -/
def runAt (R : Cfg → AskedE → (ByteArray → ByteArray) → Bool) (sh : OnBytes.Params.IndexShape)
    (O : ByteArray → ByteArray) (cl : Claim) (a : AskedE) : Bool :=
  R (cfgOf cl.cfg) a O && (idRunO sh (cRun (cfgOf cl.cfg) O) a.first O == cl.id)

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- Which stage says no: "FIT" (the tests on the parsed value), `stagePartO`'s word, "ID". Words
alone. -/
def stageO (O : ByteArray → ByteArray) (cl : Claim) (a : AskedE) : String :=
  if askedFit G.q.link.table a then
    let w := stagePartO G hok (cRun (cfgOf cl.cfg) O) (_root_.Run.size_digToBytes _)
      (_root_.Run.digS (O (TypedOracleCompiler.Run.EntryPageSafe.toBytesT
        (OnBytes.Slice.s0Of (G.bytesAt (cRun (cfgOf cl.cfg) O)))))) a O
    if w == "YES" then
      if idRunO G.q.link.table (cRun (cfgOf cl.cfg) O) a.first O == cl.id then "YES" else "ID"
    else w
  else "FIT"

end

/-- Trusted. Of the claim alone. "std": `Params.stdEntry z` refuses the three public files. -/
def stateAt (z : OnBytes.Params.StdSize) (cl : Claim) : Except String Claim :=
  if OnBytes.Params.stdEntry z cl.cfg then .ok cl else .error "std"

/-- Untrusted. -/
def parseE (G : EntryGround) (z : OnBytes.Params.StdSize) : Parser := fun cl key ent =>
  (prepE G z false cl.cfg.pol cl.cfg.lay cl.cfg.KL key ent).map (·.a)

def wordE : String :=
  "YES: OF THE VALUE THAT THE PARSER MADE OF THE KEY FILE AND THE ENTRY FILE, under the user's " ++
    "commitment ID and public files: no key file's chain, no proof file, no request, no reply " ++
    "was checked"

def usageE : String :=
  "usage: small|full <commitment ID: 64 hex digits> <config folder> <key file> <entry file>"

/-- What a yes gives out beside itself: the ID; the further table's root as it was judged (the bytes
of the typed digest); the ID's text at the further table, so that root and answers are both in one
word. -/
def givesO (sh : OnBytes.Params.IndexShape) (O : ByteArray → ByteArray) (cl : Claim) (a : AskedE) :
    List String :=
  ["the commitment ID, from the user, is the word that the hash gives of the public files " ++
     "and the first table: " ++ cl.id,
   "given out, and held against nothing in this call: the further table's root: " ++
     _root_.Fmt.hex (_root_.Run.digToBytes (_root_.Run.bytesToDig a.further.root)),
   "given out, and held against nothing in this call: the word that the hash gives, by the " ++
     "ID's text, of the public files and the further table (root and answers): " ++
     idRunO sh (cRun (cfgOf cl.cfg) O) a.further O]

/-- The kit at a size, a verifier with its words, and a parser. -/
def kitAt (z : OnBytes.Params.StdSize) (verify : Claim → AskedE → Bool) (stage : Claim → AskedE → String)
    (gives : Claim → AskedE → List String) (p : Parser) : Kit where
  X := Claim
  state := stateAt z
  parse := p
  verify := verify
  stage := stage
  gives := gives
  word := wordE
  usage := usageE

def kitFull (O : ByteArray → ByteArray) : Kit :=
  kitAt OnBytes.Params.stdFull (runAt runEntryFull Tie.recordGround.q.link.table O)
    (stageO Tie.recordGround TypedOracleCompiler.Slice.record_ok O)
    (givesO Tie.recordGround.q.link.table O) (parseE Tie.recordGround OnBytes.Params.stdFull)

def kitSmall (O : ByteArray → ByteArray) : Kit :=
  kitAt OnBytes.Params.stdSmall (runAt runEntrySmall Tie.smallRecordGround.q.link.table O)
    (stageO Tie.smallRecordGround TypedOracleCompiler.Slice.small_record_ok O)
    (givesO Tie.smallRecordGround.q.link.table O) (parseE Tie.smallRecordGround OnBytes.Params.stdSmall)

/-- THE PROGRAM, with the hash function on bytes an argument. A first word that names no size: the
call without arguments, which ends with the code 11. -/
def entryMainO (O : ByteArray → ByteArray) : List String → IO UInt32
  | "full" :: r => mainOf (bodyOf (kitFull O)) r
  | "small" :: r => mainOf (bodyOf (kitSmall O)) r
  | _ => mainOf (bodyOf (kitSmall O)) []

/-- THE PROGRAM: at the format's oracle on bytes, made of Lean's BLAKE2b (`Fmt.oracle`). The trusted
side (`stateAt`, `runAt`) is written to take its hash here and nowhere else; no theorem says it. The
untrusted parser has the port's own. -/
def entryMain : List String → IO UInt32 := entryMainO _root_.Fmt.oracle

end OnBytes.ShellOf.EntryProg

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/EntryProg.lean: THE PROGRAM FOR THE ENTRY FILE's PART: an untrusted parser, then the
closed check of an entry file on plain data (`verifyEntryFull` | `verifyEntrySmall`,
OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) in a form for a run, and the test of the commitment ID, with
the hash function on bytes an argument O; the program that is meant to run is the one at the
format's oracle made of Lean's BLAKE2b (`Fmt.oracle`). Definitions alone; the laws are in
OnBytes/ShellOf/EntryProgLaws.lean.

  The call: small|full <commitment ID: 64 hex digits> <config folder> <key file> <entry file>
  THE TERMS OF WHICH THE THEOREM SPEAKS (a function g on bit strings an argument):
  `idOfG sh cfg t g`: the port's asking form of the commitment ID (`TwoPort.M.Key.commitmentId`,
    OnBytes/ChecksWithHashAsArgument/M/Key/Table.lean: the twin of `Key.commitmentId` with the hash a letter; tied to
    it at the port's own hash by `commitmentId_port`, OnBytes/ChecksWithHashAsArgument/M/AtPort/Files.lean), CALLED
    BY NAME, at the hash that g induces, at g's own digest of the three public files, the shape sh
    and a table t; in hex. This file spells no string of the ID: what the ID's string holds is that
    definition's matter.
  `partAt V sh g cl a`: a check V at the claim's three files says yes, and `idOfG` at the value's
    first table is the claim's ID.
  WHAT RUNS (a function O on bytes an argument):
  `runAt R sh O cl a`: a form for a run R of the check (`runEntryFull` | `runEntrySmall`), and the
    ID's comparison in a form for a run: `idRunO`: `idOfG`'s text over `oBO O`, which hashes once a
    call, at `cRun cfg O`, the digest of the three public files, hashed once a call of `cRun`, as
    bytes.
  `stateAt z`: trusted: of the claim alone: `Params.stdEntry z`: the first 32 lines of the parameter
    file are z's, and what is hashed for the digest is within the hash's bound. The statement is the
    claim itself.
  `parseE G z`: untrusted: the library's strict converter as it lies (`prepE`), which hashes by the
    port's own fixed hash; of what it returns the plain value a alone is taken: its digest and its
    parameters are dropped.
  `entryMainO O`: the program with the hash an argument. `entryMain`: at `Fmt.oracle`.

Why the ID has a form for a run. A digest is a function from 256 places to bits; where a term keeps
"the hash of s" as such a function, compiled code may hash s anew at every bit read. Here each hash
is laid once as bytes, in a function whose value is bytes (so does `verifyEntryO` for its two
digests). That this is what makes a run come home is a matter of a run, not of a theorem.

Who lays what: the table in OnBytes/ShellOf/Claim.lean's head. What that table says `verify` owes:
a.first is tested by the ID's comparison (root and answers enter the ID's string); the seeds by the
comparison inside the check; a.further by nothing outside the run: two words of it are given out for
the caller to hold against the proof file's: the root that was judged, and the ID's text at the
further table (root and answers). OF a.out.run, WHICH IS THE SALT IN THE CHAIN's FIRST QUERY AND IN
EVERY LEAF OF THE CHAIN's OWN TREES (not in the stored tables' leaves, the seeds' chains, the two
digests or the ID's call), `askedFit` ASKS 32 BYTES THAT ARE NOT ALL ZERO (`Fmt.runOk`) AND NO MORE:
the format's verifier also computes that value (its call 172, on the parameters' digest and 32
random bytes): that is not done here.

What is not claimed. Nothing on soundness. One file of three. A yes is a yes of the value a, not of
the files. NO LAW HERE TIES `idOfG` AT THE REALISED ORACLE TO THE FORMAT's `Fmt.publishedID`: it
would ask that what is hashed is within the hash's bound on lengths. The ID's call is in no checker,
public string or bound of the library. At an O other than `Fmt.oracle` the wired parser still cuts
by the fixed hash, so `entryMainO O` will refuse nearly everything there. That either arm ever
returns 0 is a fact of a run: this file records none. That the trusted side holds no hash but O is
no theorem. The endings that verify-on-bytes makes behind its tests ("not a verification": a lower
profile, fewer bits asked) are not made here: the body's `short` never speaks. `stageO` is words
alone: it runs the tests once more; no law says that its word is not "YES" where `runAt` says no.

`askedFit` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) tests of the roots only that those of `first`
and `further` have 32 bytes, and by its text it does not test that each opening's shape is the
description's, or that the run's value is computed from the random bytes. Here the hash is a letter;
the ground's typed parameters stand in the planner's place; no bits are asked; the check is the
closed term of OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean.
Ask/EntryProgram.lean runs `entryMain` through `entryCheck` (EntryCheck.lean); Ask/EntryParsed.lean
runs `runAt` behind another parser (EntryParsed.lean).
-/

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskKey.lean: the entry of the files of lean/Ask/ that run the compiled verifier of
the key file's protocol, at the small size, on a key file as an outside parser has laid it out.
Definitions; they have code; one equation by unfolding (pageAt_key). Nothing is evaluated here.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Whose each input is. From the user: the three public parameter files and the commitment ID. From the
prover, through a parser that is trusted for nothing: the parsed key file. From the library: the
numbers of the small size (the table's shape, the salt's bytes, the stored table's depth); "plan 4"
holds the first two against the plan, "plan 1" the third. From whoever starts the run: ASK_K, the
number of blocks of a chain's answer less two; "plan 6" holds it against what the rounds need. Made
here from the user's files and the table that the parsed key file names: the plan, the protocol's
description and the record (its seeds are drawn here). Made here from the rest of the parsed key
file: the proof string, and the two lists of places where that string can hold openings. The
format's hash O is an argument of every call that these definitions themselves make; `run` uses
Fmt.oracle. The planner beneath also computes digests of public data by a fixed function.

Main names:
  `Ground`, `groundOf`: what is made of the user's three files alone.
  `keyFront`: from a parsed key file: the tests on the plan and on the claim, the typing, the lists,
    the test of the slot's salt; then the stages' input (Johnson/RunOne/AskShell.lean).
  `judge`: the verifier along lists in stages; its law is keyAnswer_eq
    (Johnson/RunOne/AskKeyLaws.lean).
  `keyParts`: a whole run as plain data. `keyTell`: the same with its print.
  `verifyKeyAskSmall`: THE WHOLE ANSWER as one term: every test in front, and `keyLast`, the guarded
    verdict of the compiled verifier (verifyGuard) at the string that is laid of the parsed key
    file. `verifyKeyAskSmallParts`: its parts by name. `verifyKeyAskRun`: the form that runs. That
    the three agree: Johnson/RunOne/AskKeyLaws.lean.
  `run`: reads the variables and the files, runs the unchanged file, then one run for each change of
    the parsed record that it is handed; it throws where the unchanged file gets no yes.
Limits: an evaluation of these is no theorem. The carrier of the typed oracles is hollowTX
(Johnson/RunOne/Hollow.lean), that of no theorem; the coding of typed queries into hash calls is
pageRun's (Johnson/RunOne/OraclePages.lean), with part of its fields writing nothing. The seeds'
queries are not asked: the record is made here. The run values of the key file's first and third
chain are taken as the parsed key file gives them (see keyTests). Nothing on soundness: in the
library's theorems the soundness of the key file's description is a named hypothesis, and the
description's own checks are written by hand after the C++ verifier.
The program does not import this file.


-/
import Johnson.RunOne.AskShell
import Johnson.RunOne.Hollow
import Johnson.RunOne.OraclePages
import Johnson.RunOne.FamT
import Johnson.RunOne.DrawT
import Johnson.RunOne.OnceD
import OnBytes.Maker.ListedCarrierTop
import OnBytes.Maker.Page.GuardVerify
import OnBytes.Maker.Page.GuardFast
import OnBytes.Maker.CarrierTyping
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify
import OnBytes.ChecksWithHashAsArgument.M.Key.Table
import OnBytes.Maker.SilentParts
import OnBytes.Maker.Wire
import OnBytes.Tie.EntryAsked
import OnBytes.Tie.EntryAtCfg
import OnBytes.K.ArmLetters
import OnBytes.Tie.EntryGrounds
import OnBytes.Flat.FilesAt
import OnBytes.Flat.LeafBodies
import OnBytes.Flat.RecordCode
import OnBytes.Flat.WireBlocks
import OnBytes.TypedOracleCompiler.StringsAt
import OnBytes.Slice.SmallRecSz
import Johnson.Flat.WireAt
import Johnson.Flat.SmallAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.Key
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open OnBytes.Flat OnBytes.RunA OnBytes.Slice OnBytes.Proof OnBytes.TwoPort
open OnBytes.Tie Hiop Johnson.RunOne OnBytes.Maker _root_.Run
open OnBytes
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The bytes of a file's salt. -/
def sbSmall : Nat := smallRecordGround.q.given.plan.salt

/-- The record: its seeds are drawn here, over the hash O, from the table's root, the digest cfg and
six numbers of the table's shape (`nameUnder`, OnBytes/Tie/EntryAskM.lean). -/
def recSmall (O : ByteArray → ByteArray) (cfg : ByteArray) (t : Params.TableName) :
    Option RecSmall :=
  (seedsUnder (fun f name bits count =>
      Slice.recordSeedsW (m := Id) (Fmt.HO O) f name bits count)
    (linkAtCfg smallRecordGround.q cfg) t).map
    (K.recOne smallRecordGround.q.link.table.v smallRecordGround.q.link.table.cubeBits
      smallRecordGround.q.link.table.answers t)

/-- What is made of the user's three public files alone. The data D of the description's rounds are
made once and handed on as a value. -/
structure Ground where
  p : Model.Verify.Planned
  key : Params.KeyChains
  proof : Params.ProofChains
  D : WholeD
  tF : FrontMsg (List OnBytes.E)
  tJ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray
  rn : RecSmall → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool
  /-- the tests on the plan: they read the user's three files alone -/
  tests : List (String × Bool)

/-- The plan over the hash O, and the key file's description at it. The five tests: the makers' own
on the rounds of which the description is made (where they say no, the description has no round);
the two that the verifier program makes on the public values before it reads a key file
(Key.check, OnBytes/Key/File.lean; one clause of the second: the binding tree has one leaf); and
that the numbers of the small size which these definitions take from the library (the table's shape,
the salt's bytes) are the plan's, and the plan's digest of the public files the first chain's; and
that the acceptance policy is exact match (the key file's verifier does not read the policy: the
test stands here so that both asking files refuse the same public files). -/
def groundOf (O : ByteArray → ByteArray) (pol lay KL : ByteArray) : Except String Ground :=
  match ((M.Model.Verify.planned (m := Id) (Fmt.HO O) pol KL (some lay)).run :
      Except String Model.Verify.Planned) with
  | .error e => .error e
  | .ok p =>
    let G := bigReqSmall p
    let dry := dryKey G.k (OnBytes.Slice.keyOf (fun β : NZ => β.val) G.rec₀)
    .ok { p := p, key := G.k, proof := G.c
          D := WholeD.of srS.P.T.a (dataAt srS.P.T.a dry)
          tF := front₀ G.rec₀, tJ := join₀ G.rec₀, rn := runKSmall G
          tests :=
            [("plan 1: the rounds of which the description is made pass the makers' tests",
                okAt srS.P.T.a dry),
              ("plan 2: the plan names the field in which these definitions compute",
                !(G.k.oneTime.given.plan.field != .two)),
              ("plan 3: the public values of the key file's first chain fit together",
                Key.admitted G.k.oneTime),
              ("plan 4: the plan's table shape, salt length and digest of the public files are " ++
                "those at which these definitions stand",
                decide (G.k.oneTime.lin.fold.index = smallRecordGround.q.link.table) &&
                  decide (G.k.oneTime.given.plan.salt = sbSmall) &&
                  decide (p.cfg = G.k.oneTime.given.cfg)),
              ("plan 5: the acceptance policy in the public parameter files is exact match",
                Model.exactMatch p.X.P.h.clipC p.X.P.h.theta p.X.P.h.cap p.X.P.h.digSh
                  p.X.P.h.tabS)] }

/-- The name of the answer's first part. -/
def planLine : String := "plan 0: a plan can be made from the public parameter files"

/-- The name of its last part. -/
def lastLine : String :=
  "verifier: the guarded verdict of the compiled verifier at the proof in the parsed key file"

section At
variable (C : _root_.Run.PQ.CK) (Z : Ground) (Kn : Nat)
  (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k)

/-- The carrier of the typed oracles: it holds what the verifier reads of one, and no more. -/
abbrev LAt : BatchProtocolWithLeafBody Unit Unit := hollowTX Unit (QAt C Z.D Z.tF Z.tJ silK Z.rn) (0, [])

/-- The stages' input at a key file. -/
abbrev InK : Type := In C Z.D Z.tF Z.tJ silK Z.rn Kn (LAt C Z) .test

/-- The coding of typed queries into the format's hash calls: the key file's rows; a proof file's
rows read nothing back, so their messages are empty (under the key file's tag none of them is
asked); leaves are read off their bodies. -/
def pageAt (O : ByteArray → ByteArray) : Page.PageJ (LAt C Z) (Kn + 1) :=
  pageRun Z.key.oneTime.given.cfg Z.key.oneTime.binding.saltBytes
    (keyPage (L := LAt C Z) (t := .test) C Z.D Z.tF Z.tJ ByteArray.empty some O Z.key)
    (proofPage (L := LAt C Z) (t := .onl) C Z.D Z.tF Z.tJ ByteArray.empty
      (fun _ => none) O Z.proof fun _ => (ByteArray.empty, ByteArray.empty))
    (Page.leafOf (L := LAt C Z) id)

/-- The page's data of the key file, by unfolding. -/
theorem pageAt_key (O : ByteArray → ByteArray) :
    (pageAt C Z Kn O).key =
      Page.fillJ (L := LAt C Z) (t := .test) C Z.D Z.tF Z.tJ ByteArray.empty some
        (Page.silentKey (Fmt.HO O) Z.key Unit) := rfl

/-- What the calls of a chain query share, computed once a query, along the data (onceD,
Johnson/RunOne/OnceD.lean). For speed alone: famT is gJ at every such record. -/
def runAt (O : ByteArray → ByteArray) : RunJ (pageAt C Z Kn O) where
  key := Lite.onceD (L := LAt C Z) (t := .test) C Z.D Z.tF Z.tJ ByteArray.empty some
    (Page.silentKey (Fmt.HO O) Z.key Unit)
  proof := onceJ (pageAt C Z Kn O).proof
  hk := fun q => by
    rw [pageAt_key]
    exact Lite.onceD_eq (L := LAt C Z) (t := .test) C Z.D Z.tF Z.tJ ByteArray.empty some
      (Page.silentKey (Fmt.HO O) Z.key Unit) q
  hp := fun _ => rfl

/-- What the stages are handed at a key file. The family: famT (Johnson/RunOne/FamT.lean), which is
gJ (OnBytes/Maker/Page/Frame.lean) by famT_eq. The test on queries: okJF
(OnBytes/Maker/Page/GuardFast.lean), which is okJ (OnBytes/Maker/Page/Guard.lean) by okJF_eq
(OnBytes/Maker/Page/GuardFastLaws.lean). -/
def inAt (O : ByteArray → ByteArray) (cm : Dig 256) (c : RecSmall)
    (π : OneProtocolProof 256 (QAt C Z.D Z.tF Z.tJ silK Z.rn)) (own : Leaves)
    (listed : List (oneExternalString (2 ^ Z.D.a) _root_.Run.PQ.SgX).Pos) : InK C Z Kn :=
  let P := pageAt C Z Kn O
  { embP := id
    xo := none
    g := famT P (runAt C Z Kn O) O
    ok := Page.okJF P
    eS := SCode.emb _ (scWhole sbSmall C Z.D Z.tF Z.tJ ByteArray.empty)
    eE := (TypedOracleCompiler.Run.PQ.bodyS Z.D.a sbSmall).embE
    sMT := 256 + 8 * sbSmall
    sFS := 8 * 32
    dR := Z.key.oneTime.binding.logLeaves
    cms := cm :: codeA c.2
    x := c
    π := π
    own := own
    listed := listed }

/-- The judge. -/
def judge : Judge (InK C Z Kn) where
  name := "the steps of verifyWholeL, one by one"
  law := "verifyKeyAskRun_eq (Johnson/RunOne/AskKeyLaws.lean): what this run answers, as plain " ++
    "data, is the term verifyKeyAskSmall; keyAnswer_eq: guard, written and verdict together are " ++
    "verifyGuard, the guarded verdict of the compiled verifier verifyBS, at this very proof"
  last := lastLine
  run := behindOf C Z.D Z.tF Z.tJ silK Z.rn Kn chal (LAt C Z) .test

/-- The table that a parsed key file names. -/
def tableOf (k : Carrier.File) : Params.TableName := ⟨k.root, k.answers.map OnBytes.E.ofTriple⟩

/-- **The tests in front of the verifier**, on the plan and on the claim, each behind a thunk. id:
the user's commitment ID, as text. Claim 2 holds five lengths inside the term (without them claims 5
and 6 would say less than their names at a record that Carrier.read has not returned); the reader's
other tests (among them: words below p, rising numbers, the digests in paths) stand in Carrier.read
alone. On claims 5 and 6: in the format a chain's run value is a hash (call 172, Fmt/Rules4.lean) of
the digest of the chain's parameter bytes and 32 more bytes: the binding tree's root at the shared
chain, random bytes of the key file at the two others. The parsed key file holds the three values
and not the random bytes: so the shared chain's is computed again here, and the two others are taken
as the parsed file gives them. -/
def keyTests (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) :
    List (String × Thunk Bool) :=
  (Z.tests.map fun x => (x.1, Thunk.mk fun _ => x.2)) ++
    [("plan 6: ASK_K allows as many blocks as the rounds need",
        Thunk.mk fun _ => decide (blocksT .two (Z.D.ds₁ ++ (Z.D.ds₂ ++ Z.D.ds₃)) ≤ Kn)),
      ("plan 7: none of the description's three chains is empty",
        Thunk.mk fun _ => !Z.D.ds₁.isEmpty && !Z.D.ds₂.isEmpty && !Z.D.ds₃.isEmpty),
      ("claim 1: the table has the admitted form",
        Thunk.mk fun _ => Key.tableOk Z.p.chains.tableShape Z.p.cfg (tableOf k)),
      ("claim 2: the table's root, the binding root and the three run values have 32 bytes each",
        Thunk.mk fun _ => decide ((tableOf k).root.size = 32) && decide (k.bindRoot.size = 32) &&
          decide (k.run1.size = 32) && decide (k.run2.size = 32) && decide (k.run3.size = 32)),
      ("claim 3: the table's commitment ID, computed here, is the user's",
        Thunk.mk fun _ => Model.Verify.idAsked id == some (Fmt.hex
          (M.Key.commitmentId (m := Id) (Fmt.HO O) Z.p.chains.tableShape Z.p.cfg (tableOf k) :
            ByteArray))),
      ("claim 4: the number of slots is the plan's",
        Thunk.mk fun _ => decide (k.places = 2 ^ Z.key.oneTime.binding.logLeaves)),
      ("claim 5: the shared chain's run value, computed here from the binding root, is the " ++
          "parsed file's",
        Thunk.mk fun _ => decide (k.run2 = Fmt.HO O 172 0 Params.labelShared Fmt.zero32
          (Fmt.HO O 169 0 1 Fmt.zero32 Z.key.shared.given.bytes ++ k.bindRoot))),
      ("claim 6: none of the three run values is 32 zero bytes",
        Thunk.mk fun _ => Fmt.runOk k.run1 && Fmt.runOk k.run2 && Fmt.runOk k.run3)]

/-- These tests in a row, up to the first that says no. -/
def claimOf (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) : List (String × Bool) :=
  upToNo (keyTests Z Kn O id k)

/-- All of them say yes. -/
def keyTestsOk (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) : Bool :=
  (claimOf Z Kn O id k).all fun x => x.2

/-- The record, drawn here, and the proof string that is laid of the parsed key file; or who
refuses, and its words. -/
def keyTyped (O : ByteArray → ByteArray) (k : Carrier.File) :
    Except (String × String) (RecSmall × OneProtocolProof 256 (QAt C Z.D Z.tF Z.tJ silK Z.rn)) :=
  match recSmall O Z.p.cfg (tableOf k) with
  | none => .error ("RECORD", "the seeds of the table's record cannot be drawn; check the three " ++
      "files under config/")
  | some c =>
    match Carrier.File.toBPrfAt C Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn k
        Z.key.oneTime.given.cfg Z.key.oneTime.binding
        (OnBytes.Maker.frontOf (tableOf k).answers k.copy) ⟨(tableOf k).answers, k.run2⟩
        k.run3 with
    | none => .error ("PROOF FORM",
        "the parsed key file does not have the form of a proof of this protocol")
    | some π => .ok (c, π)

/-- The test of the slot's salt (rsaltFit, OnBytes/Maker/Page/GuardVerify.lean). At a string of
File.toBPrfAt it says yes already by File.slotFits; it is kept because verifyGuard has it. -/
def guardOf (π : OneProtocolProof 256 (QAt C Z.D Z.tF Z.tJ silK Z.rn)) : Bool :=
  Page.rsaltFit Z.key.oneTime.binding.saltBytes Z.key.oneTime.binding.logLeaves π

/-- Its line. -/
def guardLine : String :=
  "guard: the salt of the slot's leaf has the length that the format sets and ends in the " ++
    "leaf's number"

/-- The stages' input at a parsed key file, its record and its string. -/
def inOf (O : ByteArray → ByteArray) (k : Carrier.File) (c : RecSmall)
    (π : OneProtocolProof 256 (QAt C Z.D Z.tF Z.tJ silK Z.rn)) : InK C Z Kn :=
  inAt C Z Kn O (bytesToDig (tableOf k).root) c π (ownOfCarrier Z.D k) (listedOfCarrier Z.D.a k)

/-- Lines of numbers, for the print. -/
def notesOf (k : Carrier.File) : List String :=
  [s!"parsed file: rounds {k.rounds1.length} | {k.rounds2.length} | {k.rounds3.length}; trees " ++
    s!"with rows {k.trees.length}; rows of the stored table {k.stored.length}"]

/-- **In front of the verifier**: the tests on the plan and the claim; the record; the proof string;
the test of the slot's salt; then the stages' input. -/
def keyFront (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) : Front (InK C Z Kn) :=
  if keyTestsOk Z Kn O id k then
    match keyTyped C Z O k with
    | .error e => { early := some e, notes := notesOf k, lines := claimOf Z Kn O id k }
    | .ok x =>
      { notes := notesOf k
        lines := claimOf Z Kn O id k ++ [(guardLine, guardOf C Z x.2)]
        guard := some (guardOf C Z x.2)
        input := if guardOf C Z x.2 then some (inOf C Z Kn O k x.1 x.2) else none }
  else { notes := notesOf k, lines := claimOf Z Kn O id k }

/-- **A whole run as plain data.** -/
def keyParts (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) : Ended :=
  partsOf (judge C Z Kn chal) (keyFront C Z Kn O id k)

/-- **A whole run with its print.** -/
def keyTell (clk : Clock) (O : ByteArray → ByteArray) (id : String) (k : Carrier.File) : IO Ended :=
  tellOf clk (judge C Z Kn chal) (keyFront C Z Kn O id k)

/-- **The last part of the answer, as a term to prove things of**: the guarded verdict of the
compiled verifier (verifyGuard, OnBytes/Maker/Page/GuardVerify.lean) at the key file's wire record
and the very string that is laid of the parsed key file; no where no record is drawn or no string is
laid. It is no term to run: its family hands an answer on as a function of its bits. -/
def keyLast (O : ByteArray → ByteArray) (k : Carrier.File) : Bool :=
  match keyTyped C Z O k with
  | .error _ => false
  | .ok x =>
    Page.verifyGuard (pageAt C Z Kn O) O (256 + 8 * sbSmall) (8 * 32) .test
      (QAt C Z.D Z.tF Z.tJ silK Z.rn)
      (wqWhole C Kn chal Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn)
      (SCode.emb _ (scWhole sbSmall C Z.D Z.tF Z.tJ ByteArray.empty)) id
      (fun _ => none) (TypedOracleCompiler.Run.PQ.bodyS Z.D.a sbSmall).embE
      Z.key.oneTime.binding.logLeaves (bytesToDig (tableOf k).root :: codeA x.1.2) x.1 x.2

/-- **The same part in the form that runs**: the test of the slot's salt, "written" and the verdict
of the stages. -/
def keyLastRun (O : ByteArray → ByteArray) (k : Carrier.File) : Bool :=
  match keyTyped C Z O k with
  | .error _ => false
  | .ok x =>
    guardOf C Z x.2 && (((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).written &&
      ((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).verdict)

end At

/-- What the user hands over: the three public parameter files and the commitment ID, as text. -/
structure User where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  id : String

section Kit
variable (C : _root_.Run.PQ.CK) (Kn : Nat) (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k)

/-- The parts of the whole answer at a kit C, by name: the plan is made; every test on the plan and
on the claim; the guarded verdict. -/
def verifyKeyAskPartsAt (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) :
    List (String × Bool) :=
  match groundOf H U.pol U.lay U.KL with
  | .error _ => [(planLine, false)]
  | .ok Z =>
    (planLine, true) :: ((keyTests Z Kn H U.id k).map fun x => (x.1, x.2.get)) ++
      [(lastLine, keyLast C Z Kn chal H k)]

/-- The whole answer at a kit C. All that hangs on the kit is made inside. -/
def verifyKeyAskAt (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) : Bool :=
  match groundOf H U.pol U.lay U.KL with
  | .error _ => false
  | .ok Z => ((keyTests Z Kn H U.id k).all fun x => x.2.get) && keyLast C Z Kn chal H k

/-- The whole answer at a kit C in the form that runs: what a run of the stages answers. -/
def verifyKeyAskRunAt (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) : Bool :=
  match groundOf H U.pol U.lay U.KL with
  | .error _ => false
  | .ok Z => (keyParts C Z Kn chal H U.id k).answer

end Kit

/-- **The parts of the whole answer**, by name. Kn: the number of blocks of a chain's answer less
two. H: the format's hash. -/
def verifyKeyAskSmallParts (Kn : Nat) (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) :
    List (String × Bool) :=
  verifyKeyAskPartsAt (ckP .two) Kn (chalP .two Kn) H U k

/-- **THE WHOLE ANSWER**: from the user's files, the parsed key file and the hash: every test in
front, and the guarded verdict of the compiled verifier at the string that is laid of the parsed key
file; at the kit of the library's descriptions. A term to prove things of; what runs is
verifyKeyAskRun. -/
def verifyKeyAskSmall (Kn : Nat) (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) : Bool :=
  verifyKeyAskAt (ckP .two) Kn (chalP .two Kn) H U k

/-- **The whole answer in the form that runs**: the stages, at the kit made for a run (ckPT,
Johnson/RunOne/DrawT.lean), which is the descriptions' kit by ckPT_eq. -/
def verifyKeyAskRun (Kn : Nat) (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) : Bool :=
  verifyKeyAskRunAt (ckPT .two) Kn (chalP .two Kn) H U k

/-- **The entry.** The variables: ASK_EXAMPLE: the folder of a stored example
(../examples/accepted-proof if it is not set); ASK_PARSED: the parsed key file; ASK_K: the number
of blocks of a chain's answer less two (what the rounds need if it is not set). turns: after the
unchanged file, one run for each: what is changed; the name, up to the colon, of the test that is
expected to say NO, or of the stop before an answer (none: a yes is expected); and the change of the
parsed record, made in memory. It throws where the unchanged file gets no yes, or a changed one does
not end as expected. -/
def run (turns : List (String × Option String × (Carrier.File → Carrier.File))) : IO Unit := do
  let clk : Clock ← IO.mkRef (← IO.monoMsNow)
  let O : ByteArray → ByteArray := Fmt.oracle
  let dir ← envOr "ASK_EXAMPLE" "../examples/accepted-proof"
  let some parsed ← IO.getEnv "ASK_PARSED"
    | throw (IO.userError ("set ASK_PARSED to the path of the parsed key file; make that file " ++
        "with tools/parser/parse_files.sh (Ask/README.md)"))
  let rd (n : String) : IO ByteArray := IO.FS.readBinFile (dir ++ "/" ++ n)
  let pol ← rd "config/policy.txt"
  let lay ← rd "config/layout.txt"
  let KL ← rd "config/KL.bin"
  let id := trimmed (← IO.FS.readFile (dir ++ "/ID.txt"))
  let bytes ← IO.FS.readBinFile parsed
  say clk (s!"read: {dir}: policy {pol.size} | layout {lay.size} | KL {KL.size} bytes; the " ++
    s!"commitment ID {id.length} characters; {parsed}: {bytes.size} bytes")
  match groundOf O pol lay KL with
  | .error e => throw (IO.userError
      s!"plan: it cannot be made ({e}); check the three files under {dir}/config")
  | .ok Z =>
  say clk s!"{planLine}: yes"
  let need := blocksT .two (Z.D.ds₁ ++ (Z.D.ds₂ ++ Z.D.ds₃))
  let asked := (← IO.getEnv "ASK_K").bind String.toNat?
  let Kn := asked.getD need
  say clk (s!"plan: made from the public parameter files; rounds in the three chains: " ++
    s!"{Z.D.ds₁.length} | {Z.D.ds₂.length} | {Z.D.ds₃.length}; blocks needed: {need}; " ++
    (if asked.isSome then s!"ASK_K = {Kn}" else s!"ASK_K is not set to a number: {need} taken"))
  match Carrier.read Carrier.magicKey bytes with
  | .error e => throw (IO.userError
      s!"parsed file: it cannot be decoded ({e}); make it again with tools/parser/")
  | .ok k =>
  IO.eprintln "=== THE FILE UNCHANGED"
  let e ← keyTell (ckPT .two) Z Kn (chalP .two Kn) clk O id k
  unless e.answer do throw (IO.userError "the unchanged file did not get a yes")
  let mut all := true
  let mut n := 1
  for x in turns do
    IO.eprintln (s!"=== CONTROL {n}: {x.1}. EXPECTED: " ++
      (match x.2.1 with
        | some w => s!"NO, at \"{w}\""
        | none => "yes"))
    let e ← keyTell (ckPT .two) Z Kn (chalP .two Kn) clk O id (x.2.2 k)
    let ok := match x.2.1 with
      | some w => !e.answer && (e.noes.contains w || e.stopped.map (fun s => s.1) == some w)
      | none => e.answer
    say clk (s!"CONTROL {n}: answer {yn e.answer}; said no: {e.noes}; " ++
      (if ok then "AS EXPECTED" else "NOT AS EXPECTED"))
    all := all && ok
    n := n + 1
  unless all do throw (IO.userError "a control did not end as expected")

end Johnson.RunOne.Ask.Key

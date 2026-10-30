-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/TestRecordToyStrict.lean: the second compiler's strict verifier of the link, run on
the programs' own toy entry file: definitions, and the honest file.
What is run, plainly. The programs (the C++ implementation that comes with this Lean code) wrote a
toy key file and a toy entry file, at tables with a record (OnBytes/Entry/RecordToyFiles.lean:
made-up toy data). "endingAt" takes the entry file's bytes through these stages, and returns "yes"
or the name of the first stage that says no: parameters, rounds: the link's parameters are read from
the programs' parameter bytes; the rounds are the dry run's; the description D is made of the two
(descOf: entryXD's text, OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean, at these parameters in the place of a
ground's); digest, limits: the digest in the parameters has 32 bytes; D's base is within the
construction's limits (PQ.ok); converter: an untrusted converter from the file's bytes to a value:
strict (convE: the port's Entry.read) or lenient (convLax, OnBytes/TypedOracleCompiler/Slice/EntryConv.lean: it cuts
the file and recomputes the chain, tests no work, walks no path, compares no root), under the first
table's root and answers as Key.readTable reads them off the programs' key file; fit, pins:
askedFit, pinsFit (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean, EntryRunMain.lean); seeds: both records'
seeds, asked of the typed oracles, are the converter's (cmpEL); typing: tabsOf, assembleT
(Johnson/RunOne/StrictLinkB.lean); chain, then the fourteen named lines "strict 1" to "after 5"
(stagesB, same file; the lines' text: OnBytes/Maker/ListedSteps.lean). The chain tests no work.
"after 3": the openings lead to their roots. "after 5" is the protocol's whole acceptance: the
rounds' work (passSL), that each stored table has its number of draws (everyOpeningHasItsDraws), that the stored
symbols stand at these draws (symbolsCarryTheirPositions), and the decision.
The typed oracle queries are answered by the family famOfO at the format's hash (Fmt.oracle: BLAKE2b
on the format's strings). By stagesB_yes (Johnson/RunOne/StrictLinkBLaws.lean), at every
description, decision, family and string that assembleT lays: the chain returns and the fourteen
lines all say yes just where TypedOracleCompiler.Compile.Batch.verifyOneProtocol at the tag link says yes.
The two switches. lenient: which converter. noDecision: the decision is replaced by one that always
says yes. That is another protocol, and what then runs is ITS compiled verifier: no verifier of this
library, a control: what it accepts has every hash, work, point of form and path right.
The decision is decRun (OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean): the port's own (Tie.entryDecR), by
which Entry.check judges too, at the two keys written of the instance.
What is checked when the file compiles. The description has 19 rounds and stored trees of depth 14,
as the programs' parameter bytes say. The honest file ends in "yes" behind both converters (the list
of lines has fourteen members). With the two records' seeds exchanged in the converter's value the
run ends at "seeds". So a drift between the typed protocol, its wiring or the spelling of its
queries and what the programs hash and send, if it makes this file's run fail, turns a guard red; a
drift toward accepting more does not show on the honest file. The altered copies, the false entries,
splices and another record of the first table: TestRecordToyStrictCopies.lean,
TestRecordToyStrictFalseA.lean, TestRecordToyStrictFalseB.lean, TestRecordToyStrictSplice.lean.
What is not claimed. It is not innerCompiledVerifier's link (verifyLinkProof, Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean): another
carrier, list of outer roots, number of blocks and instance, xin none, the input's p and m
(StrictLinkBLaws.lean's head); by StrictLinkB.lean's head it shares the compiler, the protocol's
make and, by the carrying armStringFull, the string. No guard of these files shows the compiled
verifier refusing for a round's work. The key file is not verified: its head is read. Evaluations by
Lean's evaluator, which leave no declaration; no theorem speaks of a run. Nothing on soundness,
completeness or hiding.
-/
import Johnson.RunOne.StrictLinkB
import OnBytes.Entry.TestRecordToy

set_option autoImplicit false

namespace Johnson.RunOne.RecordToyStrict
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE bodyS)
open _root_.Run.PQ (View SgX)
open _root_.Run (bytesToBits bytesToDig rootsB)
open TypedOracleCompiler.Run.EntryPageSafe (toBytesT)
open OnBytes.Tie (AskedE)
open OnBytes.Slice (s0Of seedEntry seedOfDrawnC)
open TypedOracleCompiler.Slice
open OnBytes.Maker (Steps)
open Johnson.RunOne.StrictB
open OnBytes OnBytes.Entry.RecordToy

/-- The description of the link's chain, of the programs' parameter bytes and the dry run. -/
def descOf (q : Params.Link) (rs : Params.Rounds) : XD :=
  ⟨(Params.entrySpecOf q rs ByteArray.empty).base,
    fun r0 r1 => Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩, rs.map (·.2)⟩

/-- How the run ends: "yes", or the name of the first stage that says no; and how many named lines
stood behind the chain. bend: a change of the converter's value, for a control. -/
def endingAt (bend : AskedE → AskedE) (lenient noDecision : Bool) (first : Params.TableName)
    (ent : ByteArray) : String × Nat :=
  let O : ByteArray → ByteArray := _root_.Fmt.oracle
  match Params.Link.read entryParameters with
  | none => ("parameters", 0)
  | some q =>
    match Params.entryRoundsAny q with
    | none => ("rounds", 0)
    | some rs =>
      let D := descOf q rs
      let c := q.given.cfg
      if hc : c.size = 32 then
        if hok : TypedOracleCompiler.Run.PQ.ok D.base = true then
          let pd := _root_.Run.digS (O (toBytesT (s0Of q.given.bytes)))
          let lg := q.link.table.cubeBits
          let s := q.link.table.answers
          match (if lenient then convLax q first ent else convE q first ent) with
          | none => ("converter", 0)
          | some a₀ =>
            let a := bend a₀
            if !askedFit q.link.table a then ("fit", 0)
            else if !pinsFit D q.link.table then ("pins", 0)
            else
              let dec : XE AnsT lg s → View → Bool :=
                if noDecision then fun _ _ => true else decRun q q.link.table.v lg s
              let F := EntryRunTop.famOfO D hc (d1Run lg s) q.link.table pd O
              let cms := [bytesToDig a.first.root, bytesToDig a.further.root]
              let x := xOfAskedC lg s a
              if !cmpEL D (earlyTwo (d1Run lg s)) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2
              then ("seeds", 0)
              else
                match tabsOf D a.out with
                | none => ("typing", 0)
                | some tt =>
                  match assembleT D dec a.out tt.1 tt.2 with
                  | none => ("typing", 0)
                  | some π =>
                    match stagesB D dec (bodyS D.a D.base.plan.salt) (ownES D hok)
                        (earlyTwo (d1Run lg s)) (fun _ => TSE D (seedEntry lg s)) F cms x π tt.1
                        tt.2 with
                    | none => ("chain", 0)
                    | some st =>
                      match st.find? fun y => !y.2.get with
                      | some y => ((y.1.splitOn ":").headD y.1, st.length)
                      | none => ("yes", st.length)
        else ("limits", 0)
      else ("digest", 0)

/-- The run under the first table that stands in the programs' key file. -/
def voice (lenient noDecision : Bool) (ent : ByteArray) : Option String :=
  firstTable.map fun t => (endingAt id lenient noDecision t ent).1

/-- The description at the toy. -/
def toyDesc : Option XD :=
  (Params.Link.read entryParameters).bind fun q => (Params.entryRoundsAny q).map (descOf q)

end Johnson.RunOne.RecordToyStrict

open Johnson.RunOne.RecordToyStrict OnBytes.Entry.RecordToy

-- The plan in the programs' parameter bytes has twenty entries, of which RECORD is no round; the
-- tables' code has length 2 ^ 14.
#guard toyDesc.map (fun D => (D.ds.length, D.a)) == some (19, 14)
-- the honest entry file: yes
#guard firstTable.map (fun t => endingAt id false false t entryFile) == some ("yes", 14)
#guard firstTable.map (fun t => endingAt id true false t entryFile) == some ("yes", 14)
-- control: the two records' seeds exchanged in the converter's value
#guard firstTable.map (fun t => (endingAt (fun a => { a with l0 := a.l1, l1 := a.l0 }) false false t
  entryFile).1) == some "seeds"

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WholeViewAtFiles.lean: the statements of E2E/WholeView.lean and E2E/WholeViewTables.lean at the
three protocols from which `VerifierAndGoals.verify` is compiled, index cut to the matrices in range, WITHOUT
the premise on reads: it is E2E/ReadsAtFiles.lean's theorem. One call each; nothing new is proved
here. (The statement on tables at the uncut object, with OOD seeds named by the environment:
E2E/TablesAtOwnObject.lean.)

What is shown, at three public files Z in scope (`InScope Z`); the forms `…_named`: at the library's
two named sets of public files, with no premise on Z.
  `tables_atFiles`, `tables_atFiles_named`: at the placeholder provers, which send fixed messages:
    THE OOD SAMPLES AND ALL OPENED COLUMNS OF ALL TABLES THAT ENCODE THE INDEX, OVER ANY COPIES,
    LINKS AND BATCHES WITHIN THE BUDGET, DO NOT DEPEND ON THE INDEX: for every two matrices in
    range, all bounds that fit 44,040,191 | 62 | 62 | 62 | 64 table by table, and every environment
    within them, the law of the environment's output is the same. It says nothing of any message of
    the protocol.
  `filesWritten`, `reads_filesWritten`, `tables_cut_written`: the same statement at the library's
    three protocols of the full size at its written rounds' data (`Johnson.G.writtenKFull`,
    `writtenPFull`; the link's data are closed terms), at ANY table of scales and policy and ANY
    three decisions: no public file occurs. In scope, where the test on the public files accepts,
    `filesAt Z` has these data (E2E/ReadsAtFiles.lean: `key_data`, `proof_data`).
  `whole_atFiles`: for ANY provers that meet `ProversFit`: the library's `HVZKWholeR`.

WHAT THE STATEMENTS ON TABLES ARE ABOUT, AND WHAT NOT.
- "Committed tables": the tables that encode THE INDEX: the first table and its copies. Not the
  oracles that a prover commits to in a run.
- AT THE PLACEHOLDER PROVERS: every message of the three protocols is a fixed value. So nothing is
  said of any message of the protocol, alone OR JOINTLY with the tables (the messages of the
  protocol's own provers read the same pads and encoding randomness). It is not a statement of zero
  knowledge.
- Of the three protocols this is read, and no more: the rounds' shapes (with them the types of
  messages and of the verifier's randomness), the map from the verifier's randomness to the
  positions that it reads, and four counts of these positions. THE THREE DECISIONS, THE GATES AND
  THE PROOF OF WORK ARE READ BY NOTHING. Whether a verifier accepts a run that is shown is not said.
- ONE OOD SEED A TABLE. Here the host samples it uniformly from the configuration's type of OOD
  seeds (by that type its factor is never 0), afresh for each table together with that table's pads
  and encoding randomness: so independently of ALL that is hidden (every table's pads and encoding
  randomness, the provers' coins) and of all that has been shown. In the format the seed is a hash
  value of the table's root, the public files' digest and the shape: it hangs on the table. That the
  two orders give near laws is for the compile step to show, and is stated nowhere here.
- One table's randomness is used under one set of public files alone. The same rows and pads under
  other public files would get another seed, and of two OOD samples on one table's pads this file
  says nothing.
- THE BUDGET IS A TABLE's WHOLE LIFE, AND nothing in Lean keeps count of it.
- Bare columns and OOD answers: no root, no salt, no authentication path, no commitment ID.
- Nothing on any program.
- What the statements speak of (the encoder, the OOD answers, the pads, the encoding randomness) is
  read by NO verifier, and, by reading alone, the honest committer of the IOP as written
  in Lean is a placeholder. It is the protocol's as a field of the IOP as written in Lean; by the
  decoder's clause (from an honest table and its OOD sample the index decoder returns the index);
  and by agreeing with the format's pages, by reading alone, against no program's file.
- NO SLACK, IN THIS SENSE. At 44,040,192 columns the interface's CLAUSE on the encoder, a premise on
  which these statements rest, fails: at every Z, at the object with all matrices, at the object cut
  to the range and at `objOwn Z` (E2E/TableHidesGuard.lean; E2E/TableHidesGuardAtFiles.lean:
  `not_hidE_filesAt`, `not_hidE_objAt`; E2E/ObjectGuardsSeeded.lean: `not_hidE_own`). At ONE OOD
  seed and two matrices in range, at EVERY set of 44,040,192 positions (`every_set_filesAt`,
  `every_set_objAt`), the law of OOD answers and columns is not the same. That seed is a corner of
  its type: by the encoder's text the OOD answers there are made of the pads alone and read no cell
  of a matrix. Of a seed that reads the matrix, and of a uniform seed, nothing is shown: it is typed
  for the clause's form with all OOD seeds alone. The two matrices may hold the same weights. By how
  much the two laws differ is not said. THAT THE RESULT ITSELF FAILS THERE IS TYPED BY NO
  ENVIRONMENT: none beyond the budget is written. By a count of coins: a row of a table has
  44,040,191 elements of encoding randomness and a pad of 3, and at the edge of the budget it shows
  as many symbols and one OOD answer of 3 coordinates. So no coin of a table is left to cover what a
  message of the protocol's own provers tells of that table: that must be covered by the run's own
  coins.

WHAT IS STRONGER THAN THE LIBRARY's NAME FOR THE PROPERTY SUGGESTS, and narrower: of the tables
alone, with placeholder provers. For the tables it is not "honest-verifier": the environment also
asks for single symbols at positions of its own choice, step by step; it is unbounded; and the two
laws are EQUAL.

ON THE PUBLIC FILES. `InScope Z` is the one premise on Z; at the library's two named sets of public
files (`VerifierAndGoals.NamedFiles`: the stored full-size example's, and the same with another policy) it is
the library's theorem (`VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean), so there no
premise on Z is left. The test that the IOP's own gate runs on the files (`protocolDataWellFormed`) is no premise:
where it rejects, the key file's and the proof file's verifiers have no rounds' data and read no
column, and the statements hold the more easily. That it accepts is shown in the side library: at
these two named sets of files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
theorem ties any of these to a file on a disk. Where it rejects, all three decisions reject
everything. That at the named files a run of the key file's protocol or a batch shows a column is
stated by no one theorem of this folder; its two halves are: at the written data, and at Z in scope
where that test accepts, every such run's verifier reads one (E2E/ReadsNotEmptyAtObject.lean); at
the named files that test accepts (AtFullSide/E2E/AtWrittenFiles.lean). After hashing, what a
produced proof opens at the named files is stated by `keyHolds_zFull`, `sessionHolds_zFull` and the
same at the second set (AtFullSide/E2E/AtWrittenFiles.lean). That the link's verifier reads a column
of each of its two tables: E2E/StringsHoldLink.lean. The OOD samples and the single symbols that the
environment asks for are shown at every Z.

ON "THE VERIFIER's OWN". That `filesAt Z` and the placeholder provers are the three protocols and
the provers of the IOP as written in Lean, where all goals but two read it (`VerifierAndGoals.atSecondHashFunction`), and
that their object is the object of the input at which `VerifierAndGoals.verify` calls the compiled verifier,
are theorems: E2E/DescriptionTie.lean.

WHAT THE TIE BUYS, AND WHAT NOT. The compiled verifier reads the object through its verifier's side
alone (`HolographicProtocol.v`, Hiop/RecSide.lean; `innerCompiledVerifier_eq`, Johnson/Top/InnerCompiledVerifierSide.lean): word length,
symbols, the types of OOD seeds and answers, the three protocols, the number of requests in a batch,
and the two maps on instances (`early`, `late`). THE ENCODER, THE PADS, THE ENCODING RANDOMNESS AND
THE MAP TO THE OOD ANSWERS ARE NOT READ BY IT: re-indexing along any map f lays the encoder's
composition with f in the encoder's field, a constant map among them, and the compiled verifier is
the same function, key and proof being passed through their verifier's side (E2E/SameVerifier.lean).
What makes them the protocol's is: that they are fields of the IOP as written in Lean; the decoder's
clause at the matrices in range (from an honest table and its OOD sample the index decoder returns
the index); and a reading of the format's pages that is not machine-checked. Not the verifier.

The library has a like statement at an abstract configuration. This one is at the configuration of
the verifier's own IOP, with the format's own encoder and sample map.

Limits beside these. All limits of the two files' heads stand, above all: the premise on provers in
`whole_atFiles` asks no acceptance; no prover that is accepted is shown to meet it; `objAt Z P` is
another term than the object in the verifier's types (the index type; the provers). What
E2E/ReadsAtFiles.lean and the files beneath it rest on travels with it.

`filesWritten` fixes three protocols, and `tables_atFiles`, `tables_atFiles_named` and
`tables_cut_written` may be read as results about a goal. That goal is not among this library's
goals.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.

Terms: for "the protocol's own provers" see E2E/HidingTerms.lean.


-/
import E2E.WholeViewTables
import E2E.ReadsAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull claimsLedgerOnAt codingCells)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize numsRef)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope)
open scoped ENNReal

/-- **The OOD samples and all opened columns of all tables that encode the index (the first table
and its copies), over any copies, links and batches within the budget, do not depend on the index**:
at the placeholder provers, at every Z in scope, for every two matrices in range. NOTHING IS SAID OF
THE PROTOCOL's MESSAGES, alone or jointly with the tables: at these provers they are fixed, and no
decision of a verifier is read. One OOD seed a table, sampled by the host uniformly and
independently of all that is hidden. The budget is a table's whole life; nothing in Lean keeps count
of it. -/
theorem tables_atFiles (Z : PublicFiles) (scope : InScope Z = true) (B : BoundsR)
    (fits : B.Fits 44040191 62 62 62 64) (i i' : Ix) (α : Type)
    (E : (objAt Z (filesAt Z).fixedMessageProvers).Rec → EnvR (objAt Z (filesAt Z).fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) 0 UsedR.zero) :
    (realHostR (objAt Z (filesAt Z).fixedMessageProvers) i).view E =
      (realHostR (objAt Z (filesAt Z).fixedMessageProvers) i').view E :=
  tables_same_view (filesAt Z) (AtPublicFiles.Reads.reads_objAt_scope Z scope _) B fits i i' α E adm

/-- The same at the library's two named sets of public files: no premise on Z is left. -/
theorem tables_atFiles_named (Z : PublicFiles) (named : VerifierAndGoals.NamedFiles Z) (B : BoundsR)
    (fits : B.Fits 44040191 62 62 62 64) (i i' : Ix) (α : Type)
    (E : (objAt Z (filesAt Z).fixedMessageProvers).Rec → EnvR (objAt Z (filesAt Z).fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) 0 UsedR.zero) :
    (realHostR (objAt Z (filesAt Z).fixedMessageProvers) i).view E =
      (realHostR (objAt Z (filesAt Z).fixedMessageProvers) i').view E :=
  tables_same_view (filesAt Z) (AtPublicFiles.Reads.reads_objAt_named Z named _) B fits i i' α E adm

/-- **For any provers that fit**: the library's `HVZKWholeR` at the three protocols from which the
verifier is compiled, index cut to the range. IT ASKS NO ACCEPTANCE OF P: read the Limits of
E2E/WholeView.lean's head before citing it. -/
theorem whole_atFiles (Z : PublicFiles) (scope : InScope Z = true) (P : (filesAt Z).Provers)
    (Ryes : Ix → XF → Prop) (zT zL zO : ℝ≥0∞) (fit : ProversFit (filesAt Z) P Ryes zT zL zO) :
    ∃ Sm : SimsR (objAt Z P), ∀ B : BoundsR, B.Fits 44040191 62 62 62 64 → ∀ i₀ : Ix,
      HVZKWholeR (objAt Z P) Ryes B (simWholeR (objAt Z P) Sm i₀) (B.err zT zL zO) :=
  whole_of_fit (filesAt Z) P Ryes (AtPublicFiles.Reads.reads_objAt_scope Z scope P) fit

/-! ## At the written rounds' data: no public file -/

section Written
variable {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull) (depthReq : ℕ) (early : X → X)
  (salt : ℕ)

/-- The library's three protocols of the full size at its written rounds' data; all else free. -/
def filesWritten : Files (ConfAt pp req) :=
  threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
    (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) Johnson.G.writtenKFull
    Johnson.G.writtenPFull runK runP PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early
    salt

/-- `ReadsR` there, for all provers: E2E/ReadsAtWritten.lean's `reads_atWritten`, said of
`filesWritten`. -/
theorem reads_filesWritten
    (P : (filesWritten pp req runK runP dec rK rP depthReq early salt).Provers) :
    ((filesWritten pp req runK runP dec rK rP depthReq early salt).withProvers P).ReadsR 44040191 62 62 62
      64 :=
  AtPublicFiles.Reads.reads_atWritten X pp req runK runP dec rK rP depthReq early salt P

/-- **The form with OOD seeds sampled by the host, index cut to the matrices in range, at the
written data, with no premise on any public file.** -/
theorem tables_cut_written (B : BoundsR) (fits : B.Fits 44040191 62 62 62 64) (i i' : Ix)
    (α : Type)
    (E : (cutObj (filesWritten pp req runK runP dec rK rP depthReq early salt)
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers).Rec →
      EnvR (cutObj (filesWritten pp req runK runP dec rK rP depthReq early salt)
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) 0 UsedR.zero) :
    (realHostR (cutObj (filesWritten pp req runK runP dec rK rP depthReq early salt)
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers) i).view E =
      (realHostR (cutObj (filesWritten pp req runK runP dec rK rP depthReq early salt)
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers) i').view E :=
  tables_same_view (filesWritten pp req runK runP dec rK rP depthReq early salt)
    (reads_cut (I := FullSizeMatrix) (X := X) inRange
      (reads_filesWritten pp req runK runP dec rK rP depthReq early salt _)) B fits i i' α E adm

end Written

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.tables_atFiles
#print axioms AtPublicFiles.AtFiles.tables_atFiles_named
#print axioms AtPublicFiles.AtFiles.whole_atFiles
#print axioms AtPublicFiles.AtFiles.reads_filesWritten
#print axioms AtPublicFiles.AtFiles.tables_cut_written

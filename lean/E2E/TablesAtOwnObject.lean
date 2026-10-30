-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TablesAtOwnObject.lean: the statement on the index's committed tables AT THE VERY OBJECT IN THE
TYPES OF THE GOALS' VERIFIER: no cut of the index type, the library's own provers, each OOD seed
named by the environment. And the same at the library's written rounds' data, with no public file at
all.

Definitions.
  `objOwn Z`: `(filesAt Z).withProvers (filesAt Z).fixedMessageProvers`: by `objOwn_is_input` (from
    E2E/DescriptionTie.lean's `object_description`) it is the object of the input at which
    `VerifierAndGoals.verify`, at the IOP as written in Lean, calls the compiled verifier. Its index type is
    EVERY matrix of the full size's shape.
  (`filesWritten pp req runK runP dec …`, E2E/WholeViewAtFiles.lean: the library's three protocols
  of the full size at its written rounds' data, at ANY table pp of scales and policy and ANY three
  decisions.)

What is shown. In each: for every two indices, all bounds B that fit 44,040,191 | 62 | 62 | 62 | 64
table by table, and every environment within B: THE LAW OF THE ENVIRONMENT's OUTPUT IS THE SAME.
  `tables_own_named`: THE FORM TO QUOTE: at `objOwn Z`, Z one of the library's two named sets of
    public files: no premise but that the bounds fit and the environment keeps them; the environment
    names every OOD seed; the two indices are ANY two matrices. THAT IT HOLDS OUT OF RANGE IS ONLY
    BECAUSE THE PROVERS ARE PLACEHOLDERS: with the protocol's own provers the cut to the matrices in
    range comes back (by an argument outside Lean; no theorem here says so). (Of a cell the encoder
    reads the first coordinate alone: two matrices that differ outside the base field alone have one
    table and one OOD sample, so for such a pair the statement is idle, and it is as rich as "any
    two matrices over the base field". That two different indices never share table and OOD sample
    holds of the matrices in range: E2E/ObjectGuardsSeeded.lean, `tables_differ_own`.)
  `tables_own`: the same at every Z in scope.
  `tables_own_written`: the same at `filesWritten …`: no public file occurs.

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
- ONE OOD SEED A TABLE. Here it is any value of the configuration's type of OOD seeds (by that type
  its factor is never 0) that the environment names, as a function of what has been shown so far and
  of coins of its own, BEFORE that table's pads and encoding randomness are sampled. Of a seed that
  hangs on anything hidden (the randomness of its own or of another table, a prover's coins) nothing
  is said. In the format the seed is a hash value of the table's root, the public files' digest and
  the shape: it hangs on the table. That the two orders give near laws is stated nowhere here.
- One table's randomness is used under one set of public files alone. The same rows and pads under
  other public files would get another seed, and of two OOD samples on one table's pads this file
  says nothing.
- THE BUDGET IS A TABLE's WHOLE LIFE, AND nothing in Lean keeps count of it.
- Bare columns and OOD answers: no root, no salt, no authentication path, no commitment ID.
- Nothing on any program.
- What the statements speak of (the encoder, the OOD answers, the pads, the encoding randomness) is
  read by NO verifier; by a reading that is not machine-checked, the honest committer of the IOP as
  written in Lean is a placeholder. It is the protocol's as a field of the IOP as written in Lean;
  by the decoder's clause (from an honest table and its OOD sample the index decoder returns the
  index); and by agreeing with the format's pages, by reading alone, against no program's file.
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
are theorems: E2E/DescriptionTie.lean (here: `objOwn_is_input`).

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

Limits beside these. What E2E/ReadsAtWritten.lean, E2E/ReadsAtFiles.lean, E2E/TableHides.lean and
Hiop/Seeded/ rest on travels along.

`objOwn` fixes an object, and `tables_own`, `tables_own_named` and `tables_own_written` may be read
as results about a goal. That goal is not among this library's goals.

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
import E2E.WholeViewAtFiles
import E2E.WholeViewTablesSeeded
import E2E.DescriptionTie

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop Hiop.Seeded AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull claimsLedgerOnAt codingCells)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize numsRef)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope)
open scoped ENNReal

/-! ## 1. At three public files Z -/

/-- **The object in the types of the goals' verifier**: the three protocols at Z with the library's
own provers; every matrix is an index. -/
def objOwn (Z : PublicFiles) : HolographicProtocol FullSizeMatrix XF := (filesAt Z).withProvers (filesAt Z).fixedMessageProvers

/-- **`objOwn Z` is the object of the input at which the goals' verifier calls the compiled
verifier**, at the IOP as written in Lean, at every digest c and further reading m
(E2E/DescriptionTie.lean: `object_description`, `verify_calls`). -/
theorem objOwn_is_input (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    objectOf ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) = ⟨FullSizeMatrix, XF, objOwn Z⟩ :=
  object_description Z c m

/-- **The OOD samples and all opened columns of all tables that encode the index, over any copies,
links and batches within the budget, at OOD seeds named by the environment, do not depend on the
index**: at the very object in the types of the goals' verifier, for ANY two matrices. Nothing is
said of the protocol's messages, alone or jointly with the tables: at these provers they are fixed,
and no decision of a verifier is read. One OOD seed a table, named from what has been shown so far,
before that table's pads and encoding randomness are sampled. The budget is a table's whole life;
nothing in Lean keeps count of it. -/
theorem tables_own (Z : PublicFiles) (scope : InScope Z = true) (B : BoundsR)
    (fits : B.Fits 44040191 62 62 62 64) (i i' : FullSizeMatrix) (α : Type)
    (s₀ : (objOwn Z).OutOfDomainSeed) (E : (objOwn Z).Rec → EnvS (objOwn Z) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) (fun _ => True) 0 UsedR.zero) :
    (realHostS (objOwn Z) (ProversS.own (objOwn Z)) i).view s₀ E =
      (realHostS (objOwn Z) (ProversS.own (objOwn Z)) i').view s₀ E :=
  tables_seeded (filesAt Z) (AtPublicFiles.Reads.reads_filesAt_scope Z scope _) B fits i i' α s₀ E adm

/-- **THE FORM TO QUOTE: the same at the library's two named sets of public files**: no premise is
left but that the bounds fit and that the environment keeps them. That it holds of matrices out of
range is only because the provers are placeholders: with the protocol's own provers the cut to the
range comes back (by an argument outside Lean; no theorem here says so). All that the docstring of
`tables_own` and this file's head say goes with it. -/
theorem tables_own_named (Z : PublicFiles) (named : VerifierAndGoals.NamedFiles Z) (B : BoundsR)
    (fits : B.Fits 44040191 62 62 62 64) (i i' : FullSizeMatrix) (α : Type)
    (s₀ : (objOwn Z).OutOfDomainSeed) (E : (objOwn Z).Rec → EnvS (objOwn Z) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) (fun _ => True) 0 UsedR.zero) :
    (realHostS (objOwn Z) (ProversS.own (objOwn Z)) i).view s₀ E =
      (realHostS (objOwn Z) (ProversS.own (objOwn Z)) i').view s₀ E :=
  tables_seeded (filesAt Z) (AtPublicFiles.Reads.reads_filesAt_named Z named _) B fits i i' α s₀ E adm

/-! ## 2. At the written rounds' data: no public file -/

section Written
variable {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull) (depthReq : ℕ) (early : X → X)
  (salt : ℕ)

/-- **The same as `tables_own` at the written data, with no premise on any public file.** -/
theorem tables_own_written (B : BoundsR) (fits : B.Fits 44040191 62 62 62 64) (i i' : FullSizeMatrix)
    (α : Type)
    (s₀ : ((filesWritten pp req runK runP dec rK rP depthReq early salt).withProvers
      (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers).OutOfDomainSeed)
    (E : ((filesWritten pp req runK runP dec rK rP depthReq early salt).withProvers
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers).Rec →
      EnvS ((filesWritten pp req runK runP dec rK rP depthReq early salt).withProvers
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) (fun _ => True) 0 UsedR.zero) :
    (realHostS _ (ProversS.own ((filesWritten pp req runK runP dec rK rP depthReq early salt).withProvers
        (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers)) i).view s₀ E =
      (realHostS _ (ProversS.own ((filesWritten pp req runK runP dec rK rP depthReq early
        salt).withProvers (filesWritten pp req runK runP dec rK rP depthReq early salt).fixedMessageProvers))
        i').view s₀ E :=
  tables_seeded (filesWritten pp req runK runP dec rK rP depthReq early salt)
    (reads_filesWritten pp req runK runP dec rK rP depthReq early salt _) B fits i i' α s₀ E adm

end Written

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.objOwn_is_input
#print axioms AtPublicFiles.AtFiles.tables_own
#print axioms AtPublicFiles.AtFiles.tables_own_named
#print axioms AtPublicFiles.AtFiles.tables_own_written

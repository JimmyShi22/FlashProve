-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/ProofGround.lean: what a run of the compiled verifier of the proof file's slot is
handed beside the proof string, made WITHOUT A READING OF THE PROOF FILE: of the user's five files
and the entry file alone, at the small size. The hash O and the number of blocks that is asked for
are the caller's. The plan is the answer of the planner's twin at the hash over O (claimOf,
Johnson/RunOne/Letters.lean); no law here says that it is the program's plan.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

  recFormed   the record of a table, FORMED: the seeds are drawn under the table's name by
              `recordSeedsW`, the text of the program's routine with the hash as an argument, the
              program's own at the format's hash by `recordSeedsW_H`,
              OnBytes/Slice/RecordRead.lean, at the plan's own link; the answers are the table's
  tableFits   are the plan's three numbers of a table those at which the record is typed here
  publicOk    three of the program's own tests on the public values of a proof's first chain
              (fieldOk, cfgOk, bindOk)
  tiesOk      do the plan's values that are used side by side here fit each other: the plan's digest
              of the public files and the first and the shared chain's; the link's field, digest
              and table's shape, at which the record's seeds are drawn, and the shared chain's. The
              second chain's are not asked here.
  GroundC     the letters, the data and the three values beside them (each bound once), the number
              of blocks but one, the list cms, the instance
  groundC     these, of the six files; a refusal of its own is a sentence on the cause; claimOf's
              five and lettersAt's one pass as they are
  sameRec     are two records one, as the program's key of each is written

To be minded. The table (its root and answers) is the prover's: it is read off the entry file,
untested here: in a whole verifier the entry file's part hands it on. The seeds are nobody's word:
they are a function of the table's name, the plan and the hash. The commitment ID, the key file and
the entry's number are no inputs: a yes of a run over this ground says nothing on which commitment
the table belongs to.
recFormed never refuses for a short list: a missing seed, a short point and a missing answer are
filled (a factor that is 0 or missing becomes 1, the rest 0), and what is too long is cut (recOne,
OnBytes/K/ArmLetters.lean). groundC asks tableFits first, so that the plan draws as many as are
laid.
Where the makers' tests on the planner's dry runs fail, the data's three lists are empty: groundC
refuses there, and this stands for guardP (Johnson/RunOne/Closed.lean).

Not asked here, though the program's stage "request" asks it (requestRun, requestStage,
OnBytes/Model/VerifyStages.lean): that the entry's table's shape is admitted (IndexShape.ok, the
first clause of Key.tableOk; its clause on the link's digest follows here from cfgOk and tiesOk);
the accounting of the proof's plan against the bits that a call asks for, and, behind a yes, the
test on the work held: a parameter file whose plan is too weak gets the same ground as any other;
the comparison of the request's item with what the sub-proofs use (statementHeld); the conditions of
the standard parameter form, which enter the program's last line.

Limits. Definitions alone. That recFormed is the record in the key as the program's reader of the
proof file forms it is proved nowhere here: recFormed takes the field, the digest and the table's
shape from the plan's link, the program's reader from the proof's own chains; groundC asks that they
are the same (tiesOk). Nothing on soundness.


-/
import Johnson.RunOne.ProofAt
import Johnson.RunOne.ClosedGuard
import OnBytes.Tie.EntryAsked
import OnBytes.K.ArmLetters
import OnBytes.Slice.RecordRead
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne

open OnBytes OnBytes.Maker OnBytes.Flat
open _root_.Iop (Dig)
open _root_.Run (bytesToDig)

/-- **The record of a table, formed.** q: the plan's link. none: the seeds' routine returns nothing.
-/
def recFormed (O : ByteArray → ByteArray) (q : Params.Link) (t : Params.TableName) :
    Option RecSmall :=
  (OnBytes.Tie.seedsUnder
    (fun f name bits count => OnBytes.Slice.recordSeedsW (m := Id) (Fmt.HO O) f name bits count)
    q t).map (OnBytes.K.recOne OnBytes.Slice.srS.P.v 19 1 t)

/-- Are the plan's numbers of a table (rows' bits, a point's coordinates, answers) those at which
the record is typed here. -/
def tableFits (q : Params.Link) : Bool :=
  q.link.table.v == OnBytes.Slice.srS.P.v && q.link.table.cubeBits == 19 &&
    q.link.table.answers == 1

/-- The first chain's field is the one in which the program computes (readProof,
OnBytes/Proof/File.lean). -/
def fieldOk (c : Params.ProofChains) : Bool := c.first.given.plan.field == .two

/-- The digest of the public files is not 32 zero bytes (readProof, OnBytes/Proof/File.lean). It
tests the digest in the first chain's parameter bytes; the page and the proof string lay the plan's
field cfg (Johnson/RunOne/ProofAt.lean): groundC asks that the two are one (tiesOk). -/
def cfgOk (c : Params.ProofChains) : Bool := c.first.given.cfg != Fmt.zero32

/-- The format admits the binding tree's shape (bindingOk, OnBytes/Proof/Place.lean). -/
def bindOk (c : Params.ProofChains) : Bool := Proof.bindingOk c.first.binding

/-- Three of the program's own tests on the public values of a proof's first chain. Under the same
name of a refusal readProof has two more causes: the block's dry run fails (met in groundC, at the
sample, by the test on the empty lists), or the description returns nothing (not looked at here). -/
def publicOk (c : Params.ProofChains) : Bool := fieldOk c && cfgOk c && bindOk c

/-- Do the plan's values that are used side by side here fit each other. The page and the stored
table's salts are laid at the plan's digest of the public files, the program's at the chains' own
copy; the record's seeds are drawn at the link's field, digest and table's shape, the program's
reader of a proof file draws them at the shared chain's. So: the plan's digest, the shared chain's
and the link's are the first chain's (which cfgOk tests); the shared chain's field and the link's
are the one that fieldOk asks of the first chain; the link's table's shape is the shared chain's.
By reading all come out of one call of the planner; here it is asked. -/
def tiesOk (p : Model.Verify.Planned) : Bool :=
  decide (p.cfg = p.chains.proof.first.given.cfg) &&
    decide (p.chains.proof.shared.given.cfg = p.chains.proof.first.given.cfg) &&
    p.chains.proof.shared.given.plan.field == .two &&
    p.chains.link.given.plan.field == .two &&
    decide (p.chains.link.given.cfg = p.chains.proof.first.given.cfg) &&
    decide (p.chains.link.link.table = p.chains.proof.shared.lin.fold.index)

/-- A program's key as words. -/
def keyWords (k : TableKey) : List (UInt64 × UInt64 × UInt64) ×
    List (List (UInt64 × UInt64 × UInt64) × (UInt64 × UInt64 × UInt64)) :=
  (k.record.toList.map E.triple, k.seeds.map fun s => (s.z.map E.triple, s.beta.triple))

/-- Are two records one, as the program's key of each is written. -/
def sameRec (a b : RecSmall) : Bool :=
  keyWords (OnBytes.Slice.keyOf (fun β : OnBytes.Slice.NZ => β.val) a) ==
    keyWords (OnBytes.Slice.keyOf (fun β : OnBytes.Slice.NZ => β.val) b)

/-- What a run is handed beside the proof string. -/
structure GroundC where
  A : Letters
  /-- Ds, tF, tJ, rn (Johnson/RunOne/Closed.lean) at the letters' plan -/
  D : WholeD
  tF : FrontMsg (List E)
  tJ : _root_.Compile.Joined.JoinMsg (List E) ByteArray
  rn : Yp → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool
  Kn : ℕ
  cmsv : List (Dig 256)
  x : Yp

/-- **The ground of a run, of the user's five files and the entry file.** Kn: the number of blocks
but one that is asked for; the ground's is at least what the data's rounds need. -/
def groundC (O : ByteArray → ByteArray) (pol lay KL request y ent : ByteArray) (Kn : ℕ) :
    Except String GroundC := do
  let A ← lettersAt O pol lay KL request y ent
  if !(sizesOk A.p) then
    throw ("The parameter file describes a model of other sizes than the small example's. " ++
      "This verifier is written for these sizes alone.")
  if !(policyOk A.p) then
    throw ("The parameter file asks for an acceptance policy other than exact match. " ++
      "This verifier is written for exact match alone.")
  if !(publicOk A.p.chains.proof) then
    throw ("The public files are not admitted by the format: the field, the digest of the " ++
      "public files, or the shape of the binding tree is out of range.")
  if !(tableFits A.p.chains.link) then
    throw ("The parameter file describes a table of other sizes than the small example's. " ++
      "This verifier is written for these sizes alone.")
  if !(tiesOk A.p) then
    throw ("The plan's values do not fit each other: the digests of the public files, the " ++
      "fields or the table's shapes differ between the plan, the link's chain and the proof's " ++
      "chains.")
  let rc ← match recFormed O A.p.chains.link A.further with
    | some rc => pure rc
    | none => throw "No seeds could be drawn for the table that the entry file names."
  let x ← match xOfG request y rc with
    | some x => pure x
    | none => throw "The request file or the reply file is not well formed."
  let D := Ds A.p
  if D.ds₁.isEmpty || D.ds₂.isEmpty || D.ds₃.isEmpty then
    throw "The plan made of the three public files fails the tests that are made on its rounds."
  pure ⟨A, D, tF A.p, tJ A.p, rn A.p, knOf D Kn, cms (bytesToDig A.further.root) rc, x⟩

end Johnson.RunOne

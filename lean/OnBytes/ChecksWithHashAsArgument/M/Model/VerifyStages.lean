-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/VerifyStages.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the
program chooses the declarations that differ from the port's and turns names; it does not make the
turn over m. The definitions of OnBytes/Model/VerifyStages.lean that hash, or hand a hash on,
written once more over a monad m in which the hash is asked. The port's own file is untouched. What
does not hash is the port's own. The text written by hand is this project's authors' own rewriting
of the port's file. `requestRun` is typed by hand in this file. THE TWINS OF MODEL/ (Verify.lean,
VerifyChains.lean, VerifyStages.lean: sixteen definitions). ONE TIE TO THE PORT: at the identity
monad, `formatHashFastForm` and, for the request file's digest, `fun b => secondHashFunctionTree b`, each of the sixteen has the
value of the port's of the same name at all arguments (`namedT`: of `named`; `partCall`: with the
stage's run a letter on each side, the two related): the theorems whose names end in `_port`, and
`relX_namedT`, of OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean. The twins at another hash are
not tied to the port here, and the list below does not name them. Over another monad, or with
another function for the request file's digest, see the statements of
OnBytes/ChecksWithHashAsArgument/M/Model/SpineHom.lean and
SpineKeeps.lean. The list is not whole, and nothing of it is summed up here. That the text is the
port's with a letter for the hash is held by eye. That `hh` reaches every call of the format's hash
is no theorem. The second hash function's other calls are fixed in the text: no argument stands for
them.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.VerifyStages
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Key.File
import OnBytes.ChecksWithHashAsArgument.M.Key.Table
import OnBytes.ChecksWithHashAsArgument.M.Model.VerifyChains
import OnBytes.ChecksWithHashAsArgument.M.Params.Configure
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.RequestItem
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

namespace OnBytes.TwoPort.M.Model.Verify

open OnBytes.Model OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- `named` for a computation over m. -/
def namedT {m : Type → Type} [Monad m] {α : Type} (x : ExceptT String m α) : ExceptT Refused m α :=
  ExceptT.mk do
    let r ← x.run
    pure (named r)

/-- The steps that all stages share after the plans are made. cfg: the digest of the
configuration files. key: the key file. asked: the ID that the caller named, or the empty string.

The ID is formed from the digest of the caller's configuration files and from the first bytes of the
key file. A stage compares it with the caller's before it looks at anything else of key, entry,
request or proof. It needs the table's shape, so it cannot come before the plans. -/
def commonOf {m : Type → Type} [Monad m] (hh : HashM m) (X : Public) (cfg : ByteArray)
    (chains : Chains)
    (built : LinksH) (key : ByteArray) (asked : String) : ExceptT Refused m Common := do
  let first ←
    match Key.readTable chains.tableShape cfg key with
    | .ok x => pure x.1
    | .error e => checkerRefused e "key-refused" "internal-key-parameters"
  let idHex := Fmt.hex (← Key.commitmentId (m := m) hh chains.tableShape cfg first)
  named (refuseIf (!asked.isEmpty && asked != idHex) "model-statement")
  pure { X := X, chains := chains, built := built, first := first, idHex := idHex }

/-- The stage key: the accounting of the key's plan, then the check of the key file. -/
def keyStage {m : Type → Type} [Monad m] (hh : HashM m) (C : Common) (asked : Nat)
    (key : ByteArray) :
    ExceptT Refused m Found := do
  let a ← named (C.acct C.chains.made.key asked "key")
  match ← Key.check (m := m) hh C.chains.key key with
  | .error e => checkerRefused e "key-refused" "internal-key-parameters"
  | .ok _ =>
    named (workHeldH (Params.needsWork C.chains.made.key) a.work)
    pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
      lidbSealed 0, some a.acct, a.work)

/-- The stage leaf: the accounting of the entry's plan, then the check of the entry file against
the key's table. -/
def leafStage {m : Type → Type} [Monad m] (hh : HashM m) (C : Common) (asked : Nat)
    (entry : ByteArray) :
    ExceptT Refused m Found := do
  let a ← named (C.acct [C.chains.made.entry] asked "leaf")
  match ← Entry.check (m := m) hh C.chains.made.entryLink C.first entry with
  | .error e => checkerRefused e "entry-refused" "internal-entry-parameters"
  | .ok _ =>
    named (workHeldH (Params.needsWork [C.chains.made.entry]) a.work)
    pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
      lidbSealed 0, some a.acct, a.work)

/-- The stage request up to the verdict on the proof file. r: the files of the call. entry: the
entry file. The order is that of runStage: the request's form; the entry's table, for its form
alone; the accounting of the proof's plan; the conditions of the standard parameter form; the proof
file. Two steps before the proof file are this program's own: the statement that the first chain
binds is formed from the files' bytes, and it is compared with what the sub-proofs use. -/
def requestRun {m : Type → Type} [Monad m] (hh : HashM m) (hr : ByteArray → m (Option ByteArray))
    (C : Common) (o : Options) (r : Read)
    (entry : ByteArray) : ExceptT String m RequestRun := do
  let X := C.X
  refuseIf (r.request.size % 4 != 0 || r.y.size % 4 != 0) "statement-required"
  let so ← Head.stFromCall (words32 r.request) (words32 r.y) X.T
  let cov ← Head.coveredOf so X.T X.P.h.V
  let made := C.chains.made
  let further ← entryTable C.chains.link entry
  let a ← C.acct made.proof o.bits "request"
  let whole := acctWhole made.sized.set (some (made.key ++ [made.entry] ++ made.proof))
  let form := servedForm (servedOf C o r.layout.isSome so cov)
  let item ←
    match ← Proof.requestItem (m := m) hr r.pol r.KL r.request with
    | some w => pure w
    | none => throw "internal-request-item"
  statementHeld X item
  -- the links as built, each with the check that knows the request
  let links := C.built.links.zipWith (fun b l => { b with run := l.run }) (← linksOf X cov)
  -- one value holds the first chain's shape, layout and codes: the one whose bytes are hashed
  let c := C.chains.proof
  pure { verdict := ← Proof.check (m := m) hh c further r.entry item r.request (ofNat so.y)
           (runLinksH links c.first X.layers.wsLay) r.proof,
         form := form, whole := whole, work := a.work }

/-- The stage request: `requestRun`, and the stage's end from the verdict on the proof file. -/
def requestStage {m : Type → Type} [Monad m] (hh : HashM m) (hr : ByteArray → m (Option ByteArray))
    (C : Common) (o : Options) (r : Read)
    (entry : ByteArray) : ExceptT Refused m Found := do
  let x ← namedT (requestRun hh hr C o r entry)
  match x.verdict with
  | .refused e => throw { name := proofRefusalName e, why := some e.check }
  | .accepted =>
    named (workHeldH (Params.needsWork C.chains.made.proof) x.work)
    let set := C.X.P.settings
    pure (lastLine (!C.X.p4) (askedBelowBar o.bits) x.form set.lidb set.nminH, x.whole, x.work)

end OnBytes.TwoPort.M.Model.Verify

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/ProofPre.lean: the proof file's part of a reading of a call's files that asks the
oracle, as a function of the public digests, the further table and the files.

OnBytes/Tie/ProofAsked.lean has the asking half of a proof file's typing (`typedPR`) at letters: the
three chains' parameters, the table, the copy's number, the request's item, the first chain's block.
In the program these follow from the three public files, the request's and the reply's files, and
ONE hash: the digest of the public files. Here they are written as functions of that digest, handed
in, and of the files; and every query at a PUBLIC string is answered by a table made of the public
digests, and not asked. Definitions, statements and proofs.

Main names:
  (`plannedAt`: the planner's text with the digest of the public files as an argument:
    OnBytes/Tie/ChainsAtCfg.lean.) `planned_some`: the program's planner, at a layout file, is
    `plannedAt` at the program's own digest. By definition.
  `CallAt`, `callAt pol KL lay cfg request y`: what the reading of a proof file takes, from the plan
    at cfg and the request's and the reply's files: the plan, the own statement, the request's item,
    the first chain's block. The steps are those of the program's request stage that make a value,
    in its order; its further tests (the files' sizes, the entry's table, the accounting, that the
    statement is held) are not made: `callAt` may return where the program refuses. None asks the
    oracle; the request's item is made with the second hash function, a fixed function.
  `PubD`: the four public digests: of the public files; of the three chains' parameter bytes.
  `strCfg`, `strPar`: the strings of the format's two calls with the number 169.
  `tabP pol lay KL c d rest`: the table: d's four digests at the four strings at the chains c;
  `rest` elsewhere.
  `preP Pt rest pol KL lay d further request y copy proof asm`: THE TERM: `callAt` at d's first
    digest; then `typedPR` with every query at a string that has Pt answered by `tabP` (`pinP`,
    OnBytes/Tie/Decl/PinPred.lean). Pt: the property "a public string": a letter.
  `preP_off`: it asks no string that has Pt: at every d and all files. NO HYPOTHESIS.
  `preP_noCoin`, `preP_none`, `preP_det`, `preP_asks`: from `typedPR`'s laws.
  `preP_program`: at the oracle made from the format's hash, if d's first digest is the program's
    and the table holds that oracle's own values at every string that has Pt, under the named
    premise of OnBytes/Tie/ProofAsked.lean: where the plain steps and the program's reading of the
    proof file return, the term makes asm of the program's own reading. From the program's yes:
OnBytes/Tie/Decl/ProofPrePort.lean.
Limits: those of OnBytes/Tie/ProofAsked.lean. asm is a letter.
The further table is an argument: in a reading of all files it comes out of the entry file's
reading.
WHAT THE PIN BY A PROPERTY DOES NOT GIVE. `preP_off` holds whatever the reading would ask.
Not shown: that the strings with Pt which the reading asks are the three strings of the chains'
parameter bytes at d's first digest. Were there another, it would be answered by `rest`, which is
fixed before a function is drawn (meant: the format's oracle's own value): under a drawn function
the reading's chains and the arm's would then part, the term would say yes all but never, and a
bound on it would say next to nothing. Nor is it shown that the reading's three calls with the
number 169 are at these bytes at all.
`preP_asks` has its number at one (d, files): that ONE number holds at every digest and every
request is not shown: it wants that the chains' rounds do not hang on the digest, and that the first
block's dry run states the same rounds at every request. In `preP_program` the premise on d's first
digest follows from the premise on the table where the string of the public files has Pt; both are
asked. The request's item is not asked of the oracle: the drawn function is not the only hash in the
term.

-/
import OnBytes.Tie.ProofAsked
import OnBytes.Tie.Decl.PinPred
import OnBytes.Tie.ChainsAtCfg
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort
open OnBytes.Params (TableName ProofChains)
open OnBytes.Proof (FirstEnd ProofRead)
open OnBytes.Model OnBytes.Model.Verify
open _root_.Iop (Dig)
open _root_.Run (bytesToBits digToBytes)

/-- The program's planner, at a layout file, is `plannedAt` at the program's own digest. -/
theorem planned_some (pol KL lay : ByteArray) :
    planned pol KL (some lay) = plannedAt pol KL (some lay) (configuration pol lay KL) := rfl

/-- What the reading of a proof file takes. `item`: the value of the item "request", which the
program makes of the parameter file, the scale file and the request file. `words`: the request
file's own bytes. Both are strings of bytes: the types do not tell them apart. -/
structure CallAt where
  pl : Planned
  so : Head.StOwn
  item : ByteArray
  words : ByteArray
  block : Blk FirstEnd

/-- From the plan at cfg and the request's and the reply's files. -/
def callAt (pol KL lay cfg request y : ByteArray) : Option CallAt :=
  match plannedAt pol KL (some lay) cfg with
  | .error _ => none
  | .ok pl =>
  match Head.stFromCall (words32 request) (words32 y) pl.X.T with
  | .error _ => none
  | .ok so =>
  match Head.coveredOf so pl.X.T pl.X.P.h.V with
  | .error _ => none
  | .ok cov =>
  match Proof.requestItem pol KL request with
  | none => none
  | some item =>
  match linksOf pl.X cov with
  | .error _ => none
  | .ok links =>
    some ⟨pl, so, item, request, Proof.firstBlock pl.chains.proof.first
      (Stages.runLinksH (pl.built.links.zipWith (fun b l => { b with run := l.run }) links)
        pl.chains.proof.first pl.X.layers.wsLay) (Model.ofNat so.y)⟩

/-- The four public digests. -/
structure PubD where
  cfg : Dig 256
  first : Dig 256
  shared : Dig 256
  second : Dig 256

/-- The string of the call that hashes the three public files: number 169, index 2. -/
def strCfg (pol lay KL : ByteArray) : List Bool :=
  bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [pol, lay, KL]))

/-- The string of the call that hashes parameter bytes: number 169, index 1. -/
def strPar (params : ByteArray) : List Bool := bytesToBits (digestStr params)

/-- The table: d's four digests at the four strings; `rest` elsewhere. Where two of the four strings
are one, the earlier in this order stands. -/
def tabP (pol lay KL : ByteArray) (c : ProofChains) (d : PubD) (rest : List Bool → Dig 256) :
    List Bool → Dig 256 := fun s =>
  if s = strCfg pol lay KL then d.cfg
  else if s = strPar c.first.given.bytes then d.first
  else if s = strPar c.shared.given.bytes then d.shared
  else if s = strPar c.second.given.bytes then d.second
  else rest s

variable {Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt] (rest : List Bool → Dig 256)
  (pol KL lay : ByteArray) (d : PubD) (further : TableName) (request y : ByteArray) (copy : Nat)
  (proof : ByteArray) (asm : CallAt → ProofRead → Option Out)

/-- THE TERM. copy: the number of the stored copy. -/
def preP : Rom.OComp (Rom.rom 256) (Option Out) :=
  match callAt pol KL lay (digToBytes d.cfg) request y with
  | none => .pure none
  | some a =>
    pinP Pt (tabP pol lay KL a.pl.chains.proof d rest)
      (typedPR (asm a) a.pl.chains.proof further copy a.item a.words a.block proof)

/-- **It asks no public string.** NO HYPOTHESIS. -/
theorem preP_off : (preP Pt rest pol KL lay d further request y copy proof asm).AsksIn
    fun _ (s : List Bool) => ¬ Pt s := by
  unfold preP
  cases callAt pol KL lay (digToBytes d.cfg) request y with
  | none => trivial
  | some a => exact asksIn_pinP _ _ _

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem preP_noCoin : (preP Pt rest pol KL lay d further request y copy proof asm).NoCoin := by
  unfold preP
  cases callAt pol KL lay (digToBytes d.cfg) request y with
  | none => trivial
  | some a => exact noCoin_pinP _ _ _ (typedPR_noCoin _ _ _ _ _ _ _ _)

/-- Where the plain steps refuse it asks nothing. -/
theorem preP_none (ha : callAt pol KL lay (digToBytes d.cfg) request y = none) :
    preP Pt rest pol KL lay d further request y copy proof asm = .pure none := by
  unfold preP
  rw [ha]

/-- Its value at every family. -/
theorem preP_det (g : Rom.Fam (Rom.rom 256)) (a : CallAt)
    (ha : callAt pol KL lay (digToBytes d.cfg) request y = some a) :
    (preP Pt rest pol KL lay d further request y copy proof asm).det g =
      (askedPAt (Run.oB (overP Pt (tabP pol lay KL a.pl.chains.proof d rest) g ()))
        a.pl.chains.proof further copy a.item a.words a.block proof).bind (asm a) := by
  unfold preP
  rw [ha]
  show (pinP _ _ _).det g = _
  rw [det_pinP, typedPR_det]

open OnBytes.TwoPort.M.Asks in
/-- The asking half's number, at this d and these files. -/
theorem preP_asks {N1 N2 N3 : Nat} (a : CallAt)
    (ha : callAt pol KL lay (digToBytes d.cfg) request y = some a)
    (h1 : FirstBelow a.pl.chains.proof further copy a.item a.words a.block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic a.pl.chains.proof further) N2)
    (h3 : ∀ x first, a.block.dryRun (OnBytes.Proof.firstStart a.pl.chains.proof.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic a.pl.chains.proof further) x.2 first N3) :
    (preP Pt rest pol KL lay d further request y copy proof asm).QueryBound
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic a.pl.chains.proof further) N2 N3) * 2) := by
  unfold preP
  rw [ha]
  exact queryBound_pinP _ _ _ _ (typedPR_asks _ _ _ _ _ _ _ _ h1 h2 h3).2

/-- **The tie's half.** At the oracle made from the format's hash; d's first digest is the program's
digest of the public files (hc); the table holds that oracle's own values at every public string
(hT); the named premise (h); the program's own reading returns r (hr). -/
theorem preP_program (a : CallAt)
    (hc : digToBytes d.cfg = configuration pol lay KL)
    (ha : callAt pol KL lay (configuration pol lay KL) request y = some a)
    (hT : ∀ x, Pt x → tabP pol lay KL a.pl.chains.proof d rest x = Run.oBits () x)
    (h : ProofTwinAtO a.pl.chains.proof further copy a.item a.words a.block proof) (r : ProofRead)
    (hr : (OnBytes.Proof.readProof a.pl.chains.proof further copy a.item a.words a.block
      proof).fromStart = .ok r) :
    (preP Pt rest pol KL lay d further request y copy proof asm).det Run.oBits = asm a r := by
  unfold preP
  rw [hc, ha]
  show (pinP _ _ _).det Run.oBits = _
  rw [det_pinP_of_eq _ _ _ hT]
  exact typedPR_program _ _ _ _ _ _ _ _ h r hr

end OnBytes.Tie

#print axioms OnBytes.Tie.preP_off
#print axioms OnBytes.Tie.preP_det
#print axioms OnBytes.Tie.preP_asks
#print axioms OnBytes.Tie.preP_program

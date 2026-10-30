-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CollidesAt.lean: "the key file of this call shows a collision of the format's
hash" and "the proof file of this call shows one" as two written propositions on the call's files;
and that where the verifier program has said yes, if three tests on the plain data pass, either the
six parts of the typing return or the file shows a collision.

Definitions, statements and proofs. `KeyCollidesB` and `ProofCollidesB`
(OnBytes/Maker/Page/CollidesBytes.lean) speak of chains' parameters, a table, a file and a place.
Here these come from the call's files by the program's own functions. What the two say: the
program's reader reads the file to its end, and two entries out of the lists as read, at one
position (of one tree by the data's number, or among the stored table's rows), give two different
strings of bytes to which the format's hash gives one answer, under one number, label, index and
start. They say no more.

Main names:
  `keyCollidesAtH h F table`, `proofCollidesAtH h F further`: with the hash of the last clause as a
    letter h. The reading in them is the program's, at `Fmt.formatHash`, whatever h is.
  `keyCollidesAt F o table further`, `proofCollidesAt F o table further`: the two propositions, at
    `Fmt.formatHash`. The options o are not read; of the two tables each reads one.
  `port_key_or`, `port_proof_or`: at the files to which the program has said yes.
Under "there is" in the two propositions: the plan, fixed by the planner's equation at the three
public files; the place behind the table, by `Key.readTable`'s equation; the request's own data, the
covered part, the request's item and the links, each by its own equation; then the letters of
`KeyCollidesB` or `ProofCollidesB`.
Limits: that a file meets one of the two at `Fmt.formatHash` asks for two different strings with one answer
of this library's BLAKE2b; no such file is known. How hard one is to make is not said. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.GoodCollidesBP

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-! ## The two propositions -/

/-- The key file of these files shows a collision of the hash h. -/
def keyCollidesAtH (h : HId) (F : K.Files) (table : Params.TableName) : Prop :=
  ∃ (p : Model.Verify.Planned) (j : ℕ),
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      KeyCollidesB h p.chains.key table F.key j

/-- **The key file of this call shows a collision of the format's hash.** -/
def keyCollidesAt (F : K.Files) (_o : Model.Verify.Options) (table _further : Params.TableName) :
    Prop :=
  keyCollidesAtH Fmt.formatHash F table

/-- The proof file of these files shows a collision of the hash h. -/
def proofCollidesAtH (h : HId) (F : K.Files) (further : Params.TableName) : Prop :=
  ∃ (p : Model.Verify.Planned) (so : Model.Head.StOwn) (cov : Model.Head.Covered)
    (links : Array Model.Stages.LinkH) (item : ByteArray),
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      ProofCollidesB h p.chains.proof further F.entry item F.request (blockAt p links so.y) F.proof

/-- **The proof file of this call shows a collision of the format's hash.** -/
def proofCollidesAt (F : K.Files) (_o : Model.Verify.Options) (_table further : Params.TableName) :
    Prop :=
  proofCollidesAtH Fmt.formatHash F further

/-! ## Where the program has said yes -/

/-- **A key file.** d: the fixed reading of F's key file; key₀: a fixed key at which the three
lists R were made. -/
theorem port_key_or (F : K.Files) (o : Model.Verify.Options) (id : String)
    (table further : Params.TableName) (h : K.PortYesAt F id table further)
    (p : Model.Verify.Planned) (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (d : ChainsData) (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d))
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
        d.r = true ∨ keyCollidesAt F o table further := by
  obtain ⟨j, ht, hc⟩ := port_returns_or_collidesB F id table further h p hp d hd key₀ h0 hf R hR C
    a cfg hok hB hsalts
  exact hc.imp (fun x => x) fun c => ⟨p, j, hp, ht, c⟩

/-- **A proof file.** d: the fixed reading of F's proof file. -/
theorem port_proof_or (F : K.Files) (o : Model.Verify.Options) (id : String)
    (table further : Params.TableName) (h : K.PortYesAt F id table further)
    (p : Model.Verify.Planned) (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (so : Model.Head.StOwn)
    (hso : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y)
      p.X.T = .ok so)
    (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (item : ByteArray) (hitem : Proof.requestItem F.pol F.KL F.request = some item)
    (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
    (d : ChainsData)
    (hd : readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
      some (further, d))
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds)
    (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.proof.first.given.plan.salt cfg
        d.r = true ∨ proofCollidesAt F o table further :=
  (portP_returns_or_collidesB p so cov links hl key₀ h0 hf R hR C a cfg hok hB hsalts F id table
    further h hp hso hcov item hitem d hd).imp (fun x => x)
    fun c => ⟨p, so, cov, links, item, hp, hso, hcov, hl, hitem, c⟩

end OnBytes.Maker.Page

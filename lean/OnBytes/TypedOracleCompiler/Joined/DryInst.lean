-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/DryInst.lean: a proof file's protocol does not hang on the instance at which its
dry runs are made, from one hypothesis by name on the first chain's dry runs.

Statements on the makers of a proof file's protocol. Nothing on soundness.


`proofIOR` (OnBytes/Maker/Files.lean) takes its rounds from the dry runs of the program's blocks at
one instance z₀, and runs the program's decision at every instance on views of these rounds. Where
the dry runs at another instance state other rounds, what that decision says is not shown here. What
is shown of the dry runs: they do not hang on the table's key among keys that are alike
(OnBytes/Maker/FilesFree.lean), nor on the reply (`plannedFirstFree`,
OnBytes/Flat/LinksFreeAll.lean, under its premise hV); the third list hangs on the end of the first
dry run through four numbers, the statement and the book (OnBytes/Flat/LinksDry.lean). This file
takes as a hypothesis by name what is stated there: `DryAlike` of the first chain's dry runs at two
requests (`FirstFree`, `PlannedFirstFree`). hV: at an X that Verify.publicOf returns the two numbers
are one (`publicOf_V`, OnBytes/Flat/CoveredJoin.lean); no statement lays that in front of
`plannedFirstFree`. This file draws from it what a description needs.

Main names:
  `dry3_of_alike`: the three lists are the same at two ends of a first dry run with the same rounds
    that are alike.
  `dryProof_of_dryAlike`, `dryProof_of_firstFree`: so the three lists of a proof file are the same
    (or there are none on both sides).
  `proofIOR_of_eq`: the protocol reads the instance at which it was made through the three lists
    alone: from the bare equation of the lists.
  `dryProof_free_inst`, `proofIOR_free_inst`: the equation, and so the protocol, from `KeyAlike` and
    `DryAlike`.
  `dryProof_planned`: the three lists at the makers' `blockAt` (OnBytes/Maker/GoodProof.lean) at two
    requests that `Head.coveredOf` and `Verify.linksOf` take, under `PlannedFirstFree`.

What is asked, by name: `DryAlike` | `FirstFree` | `PlannedFirstFree`: premises; not shown here.
`KeyAlike` of the two records' keys.

Limits: ONE HYPOTHESIS IS MOVED, NONE IS PAID: `DryAlike`'s first clause IS "the first chain's
rounds are the same". What is added is carriage: through `dry3`, `dryProof` and `proofIOR`. The
hypothesis is enough; that no less would do is not said. NOTHING SAYS THAT A DRY RUN RETURNS AT ANY
REAL SIZE, nor that the makers' tests pass there. Where both dry runs fail (`dryProof` = none), or
the tests on the lists fail (`okAt` = false), the equations hold between two protocols at empty
data, which accept nothing (`proofIOR_guard`, OnBytes/Maker/Files.lean).

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.LinksDry
import OnBytes.Maker.FilesFree
import OnBytes.Maker.GoodProof

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open OnBytes Iop _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Flat OnBytes.TwoLaws
open OnBytes.Params (Rounds)

/-- **The three lists of rounds are the same at two ends of a first dry run that are alike and come
with the same rounds.** -/
theorem dry3_of_alike (p : Proof.TailPublic) (key : TableKey) {x x' : Rounds × Proof.FirstEnd}
    (h1 : x.1 = x'.1) (h2 : FirstEnd.Alike x.2 x'.2) :
    Three.dry3 p key x = Three.dry3 p key x' := by
  obtain ⟨a2, a3, a4⟩ := h2
  unfold Three.dry3
  have e : ∀ first : ChainRead, Proof.secondStart p x.2 first = Proof.secondStart p x'.2 first := by
    intro first
    unfold Proof.secondStart
    rw [a2, a3]
  simp only [h1, e, secondBlock_rounds_alike p.lin a4]

/-- **The three lists of a proof file are the same at two first blocks whose dry runs are
alike.** -/
theorem dryProof_of_dryAlike (c : Params.ProofChains) (key : TableKey)
    {b b' : Blk Proof.FirstEnd}
    (h : DryAlike (b.dryRun (Proof.firstStart c.first)) (b'.dryRun (Proof.firstStart c.first))) :
    dryProof c key b = dryProof c key b' := by
  unfold dryProof
  revert h
  cases b.dryRun (Proof.firstStart c.first) <;> cases b'.dryRun (Proof.firstStart c.first) <;>
    intro h
  · rfl
  · exact h.elim
  · exact h.elim
  · exact dry3_of_alike _ key h.1 h.2

/-- The same from the hypothesis on the links of two requests, at any two replies. -/
theorem dryProof_of_firstFree (c : Params.ProofChains) (key : TableKey)
    {links links' : Blk Proof.LinksResult} (h : FirstFree c.first links links') (reply reply' : E) :
    dryProof c key (Proof.firstBlock c.first links reply) =
      dryProof c key (Proof.firstBlock c.first links' reply') :=
  dryProof_of_dryAlike c key (h reply reply' _)

/-- **A proof file's protocol reads the instance at which it was made through the three lists of
rounds alone.** Where the lists are none on both sides, or fail the makers' tests, both protocols
stand at empty data. -/
theorem proofIOR_of_eq (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (z z' : X × R)
    (hE : dryProof c (key z.2) (block z.1) = dryProof c (key z'.2) (block z'.1)) :
    proofIOR C a tF tJ t3 silent key c block z = proofIOR C a tF tJ t3 silent key c block z' := by
  unfold proofIOR
  rw [hE]

/-- The equation, from the two hypotheses by name. -/
theorem dryProof_free_inst {X R : Type} (key : R → TableKey) (c : Params.ProofChains)
    (block : X → Blk Proof.FirstEnd) (z z' : X × R) (hk : KeyAlike (key z.2) (key z'.2))
    (hb : DryAlike ((block z.1).dryRun (Proof.firstStart c.first))
      ((block z'.1).dryRun (Proof.firstStart c.first))) :
    dryProof c (key z.2) (block z.1) = dryProof c (key z'.2) (block z'.1) := by
  rw [dryProof_keyAlike hk c (block z.1), dryProof_of_dryAlike c (key z'.2) hb]

/-- **A proof file's protocol is the same at two instances with records at which it is made**, if
the two records' keys are alike and the first chain's dry runs at the two instances are alike; THE
FIXED MESSAGES tF, tJ, t3 OF THE SILENT ROUNDS BEING THE SAME. The three files' record writes tF and
tJ of the record (OnBytes/Flat/FilesAt.lean): so there another record is another protocol, and this
statement carries the instance alone (OnBytes/TypedOracleCompiler/Joined/DryFiles.lean [not in this library]). -/
theorem proofIOR_free_inst (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (z z' : X × R)
    (hk : KeyAlike (key z.2) (key z'.2))
    (hb : DryAlike ((block z.1).dryRun (Proof.firstStart c.first))
      ((block z'.1).dryRun (Proof.firstStart c.first))) :
    proofIOR C a tF tJ t3 silent key c block z = proofIOR C a tF tJ t3 silent key c block z' :=
  proofIOR_of_eq C a tF tJ t3 silent key c block z z' (dryProof_free_inst key c block z z' hk hb)

/-- **The three lists at the makers' `blockAt`** (OnBytes/Maker/GoodProof.lean: `Proof.firstBlock`
at the links as built, each with the check of `Verify.linksOf`'s link, and the reply), at two
requests that `Head.coveredOf` and `Verify.linksOf` take. -/
theorem dryProof_planned (p : Model.Verify.Planned) (h : PlannedFirstFree p) (key : TableKey)
    {so so' : Model.Head.StOwn} {cov cov' : Model.Head.Covered}
    {links links' : Array Model.Stages.LinkH}
    (h1 : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (h2 : Model.Head.coveredOf so' p.X.T p.X.P.h.V = .ok cov')
    (h3 : Model.Verify.linksOf p.X cov = .ok links)
    (h4 : Model.Verify.linksOf p.X cov' = .ok links') (y y' : ℕ) :
    dryProof p.chains.proof key (blockAt p links y) =
      dryProof p.chains.proof key (blockAt p links' y') :=
  dryProof_of_firstFree p.chains.proof key (h so so' cov cov' links links' h1 h2 h3 h4) _ _

end TypedOracleCompiler.Joined

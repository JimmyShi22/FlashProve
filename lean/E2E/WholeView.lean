-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WholeView.lean: the library's theorem on the view of a whole object (`Hiop.rec_hvzk_whole`,
Hiop/RecWhole.lean; proof Hiop/RecWholeProof.lean) applied at the object of E2E/ObjectAtFiles.lean:
the three protocols from which `VerifierAndGoals.verify` is compiled, with their proof of work in the rounds,
the index type cut to the matrices in range. A CONDITIONAL theorem: for ANY provers that meet a
short list of premises. No prover of the protocol is written here, and none is shown to meet the
list.

Definitions.
  `ProversFit F P Ryes zT zL zO`: what is asked of provers P of three protocols F:
    `ext`: the committed table that each prover holds is the encoder's (three equations);
    `hidden`: the interface's `HidingR` at the cut object: for each of the three protocols ONE
      simulator, which is given the instance (with the OOD samples), the verifier's randomness and
      the tables' symbols where the verifier reads, and whose output has EXACTLY the law of the
      honest output (over the prover's coins, at every fixed index in range, pads, encoding
      randomness and OOD seed), outside a set of verifier's randomness of probability at most zT,
      zL, and zO for each shown request of a batch. For a batch the law is the JOINT one of all
      shown requests.
What is shown.
  `whole_of_good`, `whole_of_fit`: for any three protocols F over the full size's configuration:
    from `ReadsR` at numbers b, qT, qpar, qch, qon and the premises on P: the library's `HVZKWholeR`
    of the cut object, with the library's simulator `simWholeR` and error `B.err zT zL zO`, for all
    bounds B that fit the numbers. The first takes the three simulators by name, the second takes
    `ProversFit`.
  (At `objAt Z P`, with the numbers written out and without the premise on reads:
  E2E/WholeViewAtFiles.lean, `whole_atFiles`: 44,040,191 columns that a committed table hides beside
  its OOD sample; at most 62 columns read by the key file's verifier; 62 and 62 by the link's
  verifier in the first table and in the copy; 64 by one batch.)

WHAT `HVZKWholeR` SAYS (Hiop/RecWhole.lean; its head says more). An experiment, not one transcript.
A first table of the index is made and its OOD sample shown. Then an environment asks, step by step
and as it likes within the bounds B, for further tables (each with its OOD sample), runs of the key
file's protocol, of the link, of batches (of which it sees the requests that it names), and single
symbols of tables. The claim: what it sees when the index is i is within `B.err`, in total
variation, of what it sees when a simulator answers that has no access to i. i ranges over the
matrices in range.

Limits. WHERE THESE THEOREMS HOLD FOR A SILLY REASON, OR SAY LESS THAN THEIR NAME.
- `ReadsR` is a PREMISE here. E2E/ReadsAtFiles.lean proves it at every Z in scope, and
  E2E/WholeViewAtFiles.lean has the form without that premise. Where the IOP's own test on the
  public files rejects, all three decisions reject everything and two of the three protocols have no
  rounds' data.
- THE PREMISES ASK NO ACCEPTANCE. Provers that send fixed messages meet `ProversFit` at zT = zL = zO
  = 0 (E2E/WholeViewTables.lean); so do provers whose abort sets hold everything (every output is
  "none"). At such provers the conclusion says nothing about the protocol's messages. It is worth
  the name of the library's property only beside a statement that THE SAME provers are accepted,
  with small error. With proof of work in the rounds that statement cannot be the interface's
  `CompleteR` (an argument; no theorem here says so): its clauses ask acceptance at all verifier's
  randomness outside a small set, and a verifier that tests proof of work rejects wherever a test
  bit is 1.
- An interactive prover that sends a fixed nonce is rejected by these verifiers unless all test bits
  are 0. The search for a nonce belongs to the compiled prover, of which nothing is said here.
- At zT, zL, zO ≥ 1 the premise `hidden` holds of all provers, and the error is no bound.
  `B.err` grows with the numbers of runs: (all runs of the key file's protocol) zT + (all links) zL
  + (all batches) (shown requests) zO.
- Ryes is a free letter. All requests of a batch, the hidden ones too, must be in Ryes with the
  index. At the empty relation no batch is allowed. A wider Ryes asks more of the simulators.
- `B.Fits` is asked TABLE BY TABLE. Bounds of the protocol's course fit (one run of the key file's
  protocol on the first table; one link for each copy; batches on copies alone): up to 710,324
  copies and 688,127 batches a copy, by arithmetic that no theorem here states. Bounds that lay a
  run of the key file's protocol, a link AND 688,127 batches on one table do not fit.
- Where the verifier's randomness lies in the abort set the view is that randomness and "none": what
  an interactive prover had sent before it broke off is not in the view (the library's declared
  limit).
- The experiment plays ONE honest prover of a batch on every copy. The proof file's first message
  holds the copy's number, which this IOP's verifier does not test.
- ONE OOD SEED A TABLE, sampled by the host uniformly, afresh for each table together with that
  table's pads and encoding randomness: so independently of ALL that is hidden (every table's pads
  and encoding randomness, the provers' coins) and of all that has been shown. In the format the
  seed is a hash value of the table's root, the public files' digest and the shape: it hangs on the
  table; nothing here covers that. (With seeds named by the environment, at the placeholder provers:
  E2E/WholeViewTablesSeeded.lean.) One table's randomness is used under one set of public files
  alone. The same rows and pads under other public files would get another seed, and of two OOD
  samples on one table's pads this file says nothing.
- The budget is a table's whole life; nothing in Lean keeps count of it.
- Not at this level: roots, salts, authentication paths, the hash function, nonces found by search.
- `objAt Z P` is another term than the object in the verifier's types (E2E/ObjectAtFiles.lean,
  Limits).
- Honest-verifier: the verifier's randomness is uniform. Simulators' running times are not modelled.

`ProversFit` names what is to be proved of provers: it may be read as a goal. It is not among this
library's goals.

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


-/
import E2E.ObjectAtFiles
import Hiop.RecWholeProof

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files)
open scoped ENNReal

section General
variable {X : Type} {pp : Inst.Model.ScalesAndPolicy} {req : X → Inst.Model.Instance Inst.Model.ppref}

/-- **What is asked of provers P of three protocols F**: they hold the encoder's tables, and each of
the three runs has a simulator in the interface's exact form, at the indices in range. A member, at
provers that send fixed messages: `fit_silent`, E2E/WholeViewTables.lean. No member is known at
provers that are ever accepted. -/
structure ProversFit (F : Files (ConfAt pp req)) (P : F.Provers) (Ryes : Ix → X → Prop)
    (zT zL zO : ℝ≥0∞) : Prop where
  ext : ExtR (cutObj F P)
  hidden : (cutObj F P).HidingR Ryes zT zL zO

/-- The library's theorem at the cut object, the three simulators given by name. -/
theorem whole_of_good (F : Files (ConfAt pp req)) (P : F.Provers) (Ryes : Ix → X → Prop)
    {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞} (ext : ExtR (cutObj F P))
    (reads : (cutObj F P).ReadsR b qT qpar qch qon) (Sm : SimsR (cutObj F P))
    (good : Sm.Good Ryes zT zL zO) (B : BoundsR) (fits : B.Fits b qT qpar qch qon) (i₀ : Ix) :
    HVZKWholeR (cutObj F P) Ryes B (simWholeR (cutObj F P) Sm i₀) (B.err zT zL zO) :=
  rec_hvzk_whole Ix X (cutObj F P) Ryes b qT qpar qch qon zT zL zO (wired_cutObj F P ext) reads Sm
    good B fits i₀

/-- The same from `ProversFit`: one triple of simulators for all bounds and all i₀. -/
theorem whole_of_fit (F : Files (ConfAt pp req)) (P : F.Provers) (Ryes : Ix → X → Prop)
    {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞} (reads : (cutObj F P).ReadsR b qT qpar qch qon)
    (fit : ProversFit F P Ryes zT zL zO) :
    ∃ Sm : SimsR (cutObj F P), ∀ B : BoundsR, B.Fits b qT qpar qch qon → ∀ i₀ : Ix,
      HVZKWholeR (cutObj F P) Ryes B (simWholeR (cutObj F P) Sm i₀) (B.err zT zL zO) :=
  rec_hvzk_whole_hiding Ix X (cutObj F P) Ryes b qT qpar qch qon zT zL zO
    (wired_cutObj F P fit.ext) reads fit.hidden

end General

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.whole_of_good
#print axioms AtPublicFiles.AtFiles.whole_of_fit

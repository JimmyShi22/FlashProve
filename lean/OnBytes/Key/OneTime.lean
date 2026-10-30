-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/OneTime.lean: the first chain of a key file, the one-time chain.

A key file comes with a commitment. It says two things of the table under its root: the entries of
the table's matrix lie in their ranges, and the table is close to one code word. The file holds
three chains. This file has the first.

The course of the one-time chain.
 1. The prover sends the index-mask message, an oracle message of mask rows only. It is sampled.
 2. The block WF (OnBytes/Iop/Wf.lean): the multiplicities, the lookups, and a proximity test of its
    own. It leaves pending rows: linear claims on the matrix, one for each part of a lookup.
 3. These rows are joined into one (OnBytes/Iop/Batt.lean) if there are several. Then comes the
    first part of the test for linear constraints on the committed table (OnBytes/Iop/Lin.lean).
 4. The round SEAL. Its digest is the chain's seal, on which the two later chains build.

Main definitions: `Key.admitted`, `Key.oneTime`, `Key.startOf`, `Key.oneTimeDecides`.
C++ counterpart: the part on the one-time chain of check_key_under() in blocks/frame/check_key.h.

Not claimed here: soundness or hiding. No theorem is stated here.
-/
import OnBytes.Key.Fixed
import OnBytes.Params.Chains
import OnBytes.Proof.Tail

namespace OnBytes.Key

open OnBytes.Params (OneTime KeyChains)

/-- The public values in the parameter bytes of a key's one-time chain fit together
(`Key.fixedOk`). -/
def admitted (p : OneTime) : Bool := fixedOk p.codes p.lin p.indexMasks p.ranges p.binding

/-- The one-time chain on the verifier's side. Its last round is SEAL. Returns what the block of the
file's second chain starts from (`Proof.FirstEnd`). The shared chain's block takes nothing of it:
that chain hangs on this one through the seal only. -/
def oneTime (p : OneTime) : Blk Proof.FirstEnd := do
  let ids ← sendVerify #[p.indexMasks]
  let masks ← Blk.get ids[0]?
  let left ← Wf.verify p.ranges p.lin masks
  let first ← memberFirstVerify p.lin masks left.pending
  Proof.firstEnd first

/-- What the one-time chain's blocks start from: the rounds of the given plan, the plan's number of
answers to a sample, and the codes. -/
def startOf (p : OneTime) : Start where
  entries := p.given.rounds
  samples := p.given.plan.samples
  st := { codes := p.codes }

/-- The decision of the one-time chain on a view: its blocks succeed and use up all rounds. -/
def oneTimeDecides (p : OneTime) (v : Fmt.View) : Bool :=
  Blk.decides (do let _ ← oneTime p) (startOf p) v

end OnBytes.Key

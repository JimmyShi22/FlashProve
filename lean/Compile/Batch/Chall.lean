-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Chall.lean: definitions for the real experiment with batches: which requests of a
batch are the adversary's own, and the reply to a batch. Definitions only.

For the scheme of Compile/Batch/Star.lean and the calls of Compile/Batch/SpecGlue.lean (one call for
a batch; the reply is the list of the proofs of the adversary's own requests).

  `ownFlag b`, `reqs b`  which requests of a batch are the adversary's own; the instances of all
                         requests
  `hasOwn b`  is any request the adversary's own
  `replyOf b πs`  the reply to a batch, from the proofs that the prover's program returns

Notation: `pw ivk (keyOf isk)` (the head of Compile/Batch/PubChall.lean): pw: an arbitrary function
IVK → WKey → V, for an arbitrary type V; `keyOf isk` (Compile/Batch/Mirror.lean): a `WKey`; `b`: a
`Gen.Batch X Unit` (ZKCP/Gen.lean): a batch as the environment names it: for each slot the instance,
the witness, and whether the slot is the adversary's own.

Limits. This file defines neither the experiment nor a challenger. Definitions elsewhere: the real
experiment as a world, for any scheme: `realW` (Compile/Batch/SpecGlue.lean); a challenger: `VCBP`
(Compile/Batch/PubChall.lean), whose reply to the first setup is pw ivk (keyOf isk), for an
arbitrary function pw.
-/
import Compile.Batch.Star
import Compile.Batch.SpecGlue
import Compile.Step1_life2_Virt

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.GlueB (GCall ownPf)
open Compile.Life2 (virt)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the replies of the experiment: the verification key, or the proofs of the adversary's own
requests -/
abbrev BIn (lam : ℕ) (L : BatchProtocol I X) : Type := GlueB.GIn (IVK lam L) (Prf lam L)

/-- is request number a of the batch the adversary's own -/
def ownFlag (b : Gen.Batch X Unit) : ℕ → Bool := fun a => match b[a]? with
  | some s => s.2.2
  | none => false

/-- the instances of all requests of the batch -/
def reqs (b : Gen.Batch X Unit) : List X := b.pairs.map Prod.fst

/-- is any request of the batch the adversary's own -/
def hasOwn (b : Gen.Batch X Unit) : Bool := b.any fun s => s.2.2

/-- the reply to a batch: of the proofs that the prover's program returns, truncated or padded to
one for each request, those of the adversary's own requests -/
def replyOf (b : Gen.Batch X Unit) (πs : List (Prf lam L)) : BIn lam L :=
  .inr (ownPf b (fitLen ⟨0, default, none, none⟩ b.pairs.length πs).val)

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)


end Compile.Batch

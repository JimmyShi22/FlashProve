-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastV.lean: ONE DEFINITION, CUT OUT OF LastAt.lean,
UNTURNED: `vAt Z N₁`: where the handed own group's two members sit and which shapes they have, off
the plan: the index masks' seat N₁.index with the shape of the first notice of the sized proof's
request.atStart; W's seat N₁.w with the shape (p14At Z).S.w.
-/
import Johnson.LLT25R.LastOwedCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

/-- **Where the handed own group's two members sit, and their shapes: off the plan.** -/
def vAt (Z : ProofFile.Pub) (N₁ : Numbers) : VerifiableInference.Desc.Last.OwnSeats :=
  ⟨N₁.index, N₁.w, (Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default,
      (p14At Z).S.w⟩

end LLT25

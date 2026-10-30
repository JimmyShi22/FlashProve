-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MergeAtBatch.lean: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF
THE HEAD's SEGMENT's BATCHING THE MERGE's CONDITION `MergeBare`
(Johnson/Desc/K11/Live/BareStatement.lean) HOLDS. UNDER THE SCOPE, THE FILES READ AND IM.Open. One
lemma; none of the library's goals. No prover stands in it; nothing on completeness, soundness or
hiding.

  **`mergeBare_at_batch`**   the merge is the last hearing block in front of that border (346), so
      nothing is to be carried: LinkJoin.back_of (Johnson/Desc/First/Link/Law/StretchBack.lean) at
      that one block, as LinkJoin.back_k11 calls it, with IM.k11_of (Johnson/IMR/K11Seat.lean) and
      `headMergeBareBehind` (Johnson/Desc/K11/Live/Bare.lean)
Limits. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K11.Live.Bare
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **At every state reached in front of the head's segment's batching the merge's condition
holds.** The merge is the last hearing block in front of that border: nothing is to be carried. -/
theorem mergeBare_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s)) : Johnson.Desc.First.ForkMerge.Live.MergeBare s := by
  obtain ⟨Lk, b, e1, e2, e4, -⟩ := IM.k11_of hS hR O
  obtain ⟨s₀, -, hm⟩ := LinkJoin.back_of
    (R := fun _ s' => Johnson.Desc.First.ForkMerge.Live.MergeBare s') hS hR O (l := 24) (i := 8)
    (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s₁ rs _ s₂ hd => Johnson.Desc.First.ForkMerge.Live.headMergeBareBehind _ s₁ s₂ rs hd) h
  exact hm

end

end P1K8

#print axioms P1K8.mergeBare_at_batch

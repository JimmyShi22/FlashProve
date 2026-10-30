-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimIs.lean: the proof of `HeadClaimIsAtHead`
(Honest/K11/ClaimIsStatement.lean), to the letter. A lemma; none of the library's goals.

How: calls. Whatever a fold over the first k sub-protocols of a list returns is reached at k
(`reach_of_fold`, Johnson/Top/H0/Walk/Reach.lean): at the list with the test in front that is the
library's `RchAt`, by its own text. That 346 is a border of the chain: member number 346 is there
(`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean). Then `headClaimAsked` (ClaimAsked.lean
of this folder).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimAsked
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.K13.Honest (HeadClaimIs)
open Johnson.Desc.First.Walk.Tied (RchAt reach_of_fold)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open P5J (F0T)

/-- **The law on the head's claim, at the first chain's own list, from the four ties.** -/
theorem headClaimIsAtHead : HeadClaimIsAtHead := by
  intro H Z D r Zp Np cF xP Bs link claims h hB hcl hties x rs cols sj c o claim hfold hf hrep ho
    hoc
  have hb : 346 ≤ (cF.blocksInOrder.map below).length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF xP h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    rw [List.length_map]
    omega
  have hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 346 ((x.pub, sj), ()) :=
    reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 346 hb sj rs _ cols c hfold
  have e := headClaimAsked H Z D r Zp Np cF xP Bs Unit () x _ sj o claim h hB hr hf hrep ho hoc
    (hties x rs cols sj c hfold hf hrep)
  rw [hcl, e]

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headClaimIsAtHead

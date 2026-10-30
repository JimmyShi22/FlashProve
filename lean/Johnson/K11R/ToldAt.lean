-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/ToldAt.lean: THE MERGE's SUB-PROTOCOL TELLS OF NO TREE: in the list of what each
sub-protocol of the proof file's first chain tells (`P5J.At.told cF`, Johnson/P5J/LettersAt.lean),
the entry at number 346 is the empty list; so the table's numbers of trees and of oracle messages
behind the merge are those in front. Theorems with their proofs.

Why. The table's numbers of trees and of oracle messages at a border are counted off that list
(`Numbers.withTold`). That the merge of the claims on the committed table adds nothing to either
count is asked by the merge's second tie at these numbers.

How. In the goals' scope, what `ProofFile.onlineDescription` returns can be opened into the chain's own making
(`LaidAt.opened`, Johnson/P5J/LaidOpens.lean). There: sub-protocol number 8 in front of the batching
of segment 24 is the maker's, alone (`IM.k11_of`, K11Seat.lean); it stands at number 14 * 24 + 8 + 2
= 346 of the flat list (`IM.hear_at_flat`, FlatIx.lean; `IM.flatIx_scope`, FlatScope.lean); the
guards around it leave the field oracles (`IM.alone_oracles`, SeatForm.lean); the maker's field is
the kind's (`blkAt_fields`, Johnson/Top/H0/MergeLaw/LotIs.lean); and the kind's tells nothing
(`merge_tells_nothing`, Johnson/Desc/Sound/MgAt/K11Tells.lean). The two equations on the numbers:
`k11_withTold` (the same file) at that entry. (The four files named without a folder lie at
Johnson/IMR/.)

Main names:
  `merge_at_346`: in scope, at what `IM.Open` names: number 346 of the flat list tells nothing.
  `told_at_merge`: the entry at number 346 of `P5J.At.told cF` is the empty list, under the
    structure `P5J.AtMg` at the second hash function.
  `htr_hms_atN`: the two equations at the composed meaning's own numbers (`P5J.At.N Zp cF`), from
    that entry. `htr_hms_at`: the same under `P5J.AtMg`.

Limits. The full size alone. Of the five fields of `P5J.AtMg` three are spent: `scope`, `reads` and
`laid`; `plan` and `pubOne` are asked and not spent. The wider structure `P5J.AtMgA` is not named
here, so that the file stands over either form of it; the two statements under that structure are
ToldAtA.lean's [not in this library]. A member of the structure is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on what
the sub-protocol decides. Nothing on soundness.

-/
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.P5J.AtMg
import Johnson.P5J.LettersAt
import Johnson.Top.H0.MergeLaw.LotIs
import Johnson.Desc.Sound.MgAt.K11Tells
import Johnson.Desc.Sound.MgAt.K11Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11
open VerifiableInference.Desc (Block Chain FileDescription Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (linksFull_is)
open VerifiableInference.Desc.Sound.MgAt (merge_tells_nothing k11_withTold mergeAt behindAt)
open ProofFile (Cl)

/-- **In scope, at what `IM.Open` names: number 346 of the first chain's flat list tells nothing.**
-/
theorem merge_at_346 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[346]? = some b ∧ b.oracles.flatten = [] := by
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have e : IM.flatIx c 24 8 = 346 := IM.flatIx_scope hS hR O (by decide) 8
  have h3 := IM.hear_at_flat e1 e2
  rw [e] at h3
  refine ⟨b, h3, ?_⟩
  rw [IM.alone_oracles hla, (blkAt_fields Z Bs.G₀).2.2.2.2.2.2.1]
  exact merge_tells_nothing _

/-- **In the list of what each sub-protocol of the first chain tells, the entry at number 346, the
merge's, is the empty list.** -/
theorem told_at_merge {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : (P5J.At.told cF)[346]? = some [] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, hb, he⟩ := merge_at_346 h.scope h.reads O
  rw [P5J.At.told_is, List.getElem?_map, hb, Option.map_some, he]

/-- **The table's numbers of trees and of oracle messages behind the merge are those in front**, at
the composed meaning's own numbers: from that entry of the list. -/
theorem htr_hms_atN (Zp : ProofFile.Pub) (cF : Chain P5J.TS Cl) (hT : (P5J.At.told cF)[346]? = some []) :
    (P5J.At.N Zp cF).treesAt (some behindAt) = (P5J.At.N Zp cF).treesAt (some mergeAt) ∧
      (P5J.At.N Zp cF).msgsAt (some behindAt) = (P5J.At.N Zp cF).msgsAt (some mergeAt) := by
  unfold P5J.At.N P5J.At.ps
  rw [← linksFull_is]
  exact k11_withTold _ _ hT

/-- The same two equations under the structure `P5J.AtMg`. -/
theorem htr_hms_at {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    (P5J.At.N Zp cF).treesAt (some behindAt) = (P5J.At.N Zp cF).treesAt (some mergeAt) ∧
      (P5J.At.N Zp cF).msgsAt (some behindAt) = (P5J.At.N Zp cF).msgsAt (some mergeAt) :=
  htr_hms_atN Zp cF (told_at_merge h)

end K11

#print axioms K11.merge_at_346
#print axioms K11.told_at_merge
#print axioms K11.htr_hms_atN
#print axioms K11.htr_hms_at

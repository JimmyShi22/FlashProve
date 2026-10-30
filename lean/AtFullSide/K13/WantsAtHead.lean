-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/WantsAtHead.lean: kind K13, the members' batching, AND THE MAKER OF THE BOOK OF
COINS: UNDER THE LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis), AT THE LIBRARY's WRITTEN LIST OF THE
FIRST CHAIN's SENDINGS: what two of the maker's own calls return AT THE HEAD's DESCRIPTION:
`ownerOf` for the index masks' message returns the written owner; `linksWants` returns there;
whatever it returns, the next free entry that it hands on is 13. Three statements with their proofs;
no definition. PUBLIC DATA ALONE: descriptions, the sendings' notices, addresses, numbers. THE FULL
SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_idx_at_head`: **the owner.** `k13_linksWants_returns_at_head`: **`linksWants`
returns**, at the written owner: so the next statement is not idle. `k13_h3_at_head`: **the number
13**: the premise h3 of `k13_hS_of_whole` (Johnson/Desc/ProofFile/Honest/K13/StretchAtHead.lean), to
the letter, at p0 := the written sendings.

How. NOTHING IS EVALUATED HERE: TWO CLOSED FACTS AT THE WRITTEN DESCRIPTION WP ARE CARRIED TO THE
HEAD's. The facts, by Lean's kernel: `rawIdx_written` (AtFullSide/K14/RawFactsWritten.lean) and
`rawLinksNext_written` with `rawLinksNext` (AtFullSide/K14/RawLinksNext.lean: the test that is
evaluated there rejects where `linksWants` errs: so its yes gives the return too). The carrying:
under h the head's description is alike to WP (`planAlike_at_head`, Honest/K14/WrittenAtHead.lean);
the makers' calls return the same at lists that are alike (`ownerOf_alike`, Honest/BookAlike.lean;
`linksWants_alike`, `mergesByName_alike`, `linksIn_alike`, Honest/BookAlikeRows.lean; the library's
`alike₂_rounds`).

Limits. CONDITIONAL ON h: that h can be met is not shown here. AT THE WRITTEN SENDINGS
`proofSendsFull.1`: that a maker is handed these is not said here. The closed facts' own limits
bind: WP's values were printed by Lean's evaluator; the sendings are found by their labels, which
rest on one print; AT THE LIST `mergesByName`: THE MAKER's GUESS which masked sumchecks are merges,
by the sub-protocols' kinds and counts; compared with no program. THAT THE MAKER `bookWhole` RETURNS
ANYWHERE IS NOT SAID. A book's number is a claim on a sender's text: that the sender's text has its
mask entries where the owner's base says is not said here. Evaluations in Lean's kernel beneath,
which no independent checker has replayed.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawLinksNext
import Johnson.Desc.ProofFile.Honest.BookAlikeRows
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open ProofFile.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain alike₂_rounds)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open ProofFile.Honest.K14 (planAlike_at_head)
open AtFullSide.K14 (rawIdxW rawIdx_written rawLinksNext rawLinksNextIs rawLinksNext_written)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD, AT THE WRITTEN SENDINGS: THE MAKER's OWNER OF THE INDEX MASKS' MESSAGE IS THE
WRITTEN ONE.** CONDITIONAL on h. -/
theorem k13_idx_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ownerOf indexMaskRun cF.blocksInOrder proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
      isIndexMaskMsg = some rawIdxW := by
  have A := planAlike_at_head h
  have e : ownerOf indexMaskRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
      isIndexMaskMsg = some rawIdxW := by
    rw [← ownerOf_alike A.first, ← alike₂_rounds _ _ A.second]
    exact rawIdx_written
  exact e

/-- **UNDER THE HEAD, AT THE WRITTEN SENDINGS: `linksWants` RETURNS**, at the maker's own arguments,
at the written owner. What it returns is bound by that equation alone; its second component:
`k13_h3_at_head`. CONDITIONAL on h. -/
theorem k13_linksWants_returns_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ∃ a, linksWants cF.blocksInOrder proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) rawIdxW
      (mergesByName cF.blocksInOrder).ends (cF.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a := by
  have A := planAlike_at_head h
  have w := rawLinksNext_written
  unfold rawLinksNextIs at w
  split at w
  · rename_i a ha
    refine ⟨a, ?_⟩
    show linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) rawIdxW
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
        .ok a
    rw [← linksWants_alike A.first, ← mergesByName_alike A.first, ← linksIn_alike A.first,
      ← alike₂_rounds _ _ A.second]
    exact ha
  · cases w

/-- **h3, UNDER THE HEAD, AT THE WRITTEN SENDINGS**: whatever `linksWants` returns at the maker's
own arguments, the next free entry is 13. CONDITIONAL on h. -/
theorem k13_h3_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ∀ idx a, ownerOf indexMaskRun cF.blocksInOrder proofSendsFull.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx →
      linksWants cF.blocksInOrder proofSendsFull.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
        (mergesByName cF.blocksInOrder).ends (cF.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a →
      a.2 = 13 := by
  intro idx a hi ha
  have A := planAlike_at_head h
  obtain rfl : rawIdxW = idx := Option.some.inj ((k13_idx_at_head h).symm.trans hi)
  have e : linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) rawIdxW
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
        .ok a := ha
  rw [← linksWants_alike A.first, ← mergesByName_alike A.first, ← linksIn_alike A.first,
    ← alike₂_rounds _ _ A.second] at e
  exact rawLinksNext a e

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_idx_at_head
#print axioms AtFullSide.K13.k13_linksWants_returns_at_head
#print axioms AtFullSide.K13.k13_h3_at_head

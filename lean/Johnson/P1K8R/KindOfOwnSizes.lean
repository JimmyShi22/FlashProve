-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/KindOfOwnSizes.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS:
THE KIND'S FIELD OF THE TABLE, AT ANY FILLING AND AT THE CLOSED VALUE `h.free`, FROM THE HEAD AND
ONE CLOSED TEST: IN ONE FILE, EACH FIELD OF THE FROZEN NAMED CONDITION BY ONE CALL. NO SOUNDNESS.

`h.K8Cond 𝔏` (Johnson/Goal/Skeleton/Kinds/K8Bridge.lean) is four closed tests and, at each of the 25
links, `K8LeftT`'s nine fields (Johnson/P1K8R/TightAt.lean). Here each is had by a call. "With 14":
the call spends the head's field on the entry tests' accept (fourteen rows). The block beneath
`digits` also spends the head's handed-in field `k3`, which no entry test asks.
  THE FOUR TESTS. the names' door: `P5J.namesDoorB_at_head` (with 14); the plan fits, the sizes of
    the trees' list: `LT28.K8Tests.planFitsAllB_of_public`, `gtSizesAllB_of_public`; THE ARRAYS'
    SIZES (`ProofFile.smallSizesOwnB`): LEFT: THE ONE PREMISE BESIDE THE HEAD.
  piece: `k08_piece_at_row`.   blind: `blind_from_head` (with 14).   link: `ToldDesc.link_there`.
  small: `K8Q35.small_at` (with 14).   groupAt: by the make.   near: `IM.k08_near_at` (with 14).
  digits: `k08_digits_from_ahead` at `Q38.digAhead_of_fold` (with 14).   fold: `k08_fold_field`.
  alike, first half: `alike_first_at` at `K8Q42.nums_at_head` and `k8Rows_at_head` (both with 14).
  alike, second half: `K8Q33.cellsIn_at_draw` at `K8Q42.cellsPlan_at_head` (with 14).
  The facts along "reached" that five of these take: `P5J.atMgR_of_head`'s field (with 14).
  `k08_cond_head_of_ownSizes`: **under the head, at any filling 𝔏 whose three lists are the flat
    lists', a yes of `smallSizesOwnB` at the blank ground gives `h.K8Cond 𝔏`.**
  `k08_kind_head_of_ownSizes`: **and so `h.Kind 𝔏 K8`** (`P5J.k08_kind_all`).
  `k08_cond_of_ownSizes`, `k08_kind_of_ownSizes`: the two at `h.free`, whose three equations are
    its own.
Limits. The premise is had by evaluation at the release's public files alone.
(Where this and lean/THEOREM.md differ, the page holds.) That the head
can be met is its owners' to show. WHAT THE FIELD `alike` IS WORTH (that no early cell is read off
the table of zeros) IS NOT IN THE CONDITION: it is said beside, in Johnson/P1K8R/EarlyArraysHaveMessagesAtDraw.lean,
under two closed tests. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.Goal.Skeleton.Kinds.K8Bridge
import Johnson.P5J.FreeAll
import Johnson.P5J.StartAtHead
import Johnson.Desc.Sound.K8Tests.GtSizesOfPublic
import Johnson.HB.LLHARD.K8NamesDoorAtHead
import Johnson.HB.LLHARD.Q38J.DigAhead
import Johnson.IMR.NearAtDraw
import Johnson.ToldDescR.LinkThere
import Johnson.K8Q33R.CellsInAtDraw
import Johnson.K8Q35R.MatsAtHead
import Johnson.K8Q42R.CellsPlanAtHead
import Johnson.K8Q42R.NumsAtHead
import Johnson.P1K8R.BlindFromHead
import Johnson.P1K8R.DigitsFromAhead
import Johnson.P1K8R.ShareAtDraw
import Johnson.P1K8R.RowsAtHead

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FROZEN NAMED CONDITION AT ANY FILLING, FROM THE HEAD AND ONE CLOSED TEST.** -/
theorem k08_cond_head_of_ownSizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hO : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) :
    h.K8Cond 𝔏 := by
  have hU : ∀ k a, h.rchU k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a :=
    fun _ _ u => u.1.1
  obtain ⟨L₀, A⟩ := P5J.atMgR_of_head h h.rchU hU
  obtain ⟨rows, hrows, h1, hSh⟩ := k8Rows_at_head h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨P5J.namesDoorB_at_head h, LT28.K8Tests.planFitsAllB_of_public h.pubOne,
    LT28.K8Tests.gtSizesAllB_of_public h.pubOne, hO, n0At Zp, fun G l Xl q hG hl e3 hq => ?_⟩
  have hnear := IM.k08_near_at h hG hl e3
  obtain ⟨Lk, eLk, -⟩ := ToldDesc.link_there h.scope h.reads O l hl
  exact
    { piece := k08_piece_at_row h 𝔏 q₁ q₂ q₃ hG hl e3 hq
      blind := blind_from_head h 𝔏 q₁ q₂ q₃ hl hq
      link := ⟨Lk, eLk⟩
      small := K8Q35.small_at h A.listed hG hl e3 hU A.fold
      digits := k08_digits_from_ahead h hG hl e3 hU
        (Q38.digAhead_of_fold h hG hl e3 hU A.fold hnear)
      groupAt := rfl
      near := hnear
      fold := k08_fold_field h hG hl e3 hU
      alike := fun z a tl L ha hr hm ht hL =>
        ⟨alike_first_at h A.fold hU hG hl e3 (K8Q42.nums_at_head h A.listed hG hl e3) hrows h1
          (rowsShaped_at Zp hSh) z a tl L hr hm ht hL,
        K8Q33.cellsIn_at_draw h hl A.fold (K8Q42.cellsPlan_at_head h A.listed hl)
          z a tl L ha hr hm ht hL⟩ }

/-- **THE KIND's FIELD OF THE TABLE AT ANY FILLING.** -/
theorem k08_kind_head_of_ownSizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hO : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) :
    h.Kind 𝔏 KindName.K8 :=
  P5J.k08_kind_all h 𝔏 q₁ q₂ q₃ (k08_cond_head_of_ownSizes h 𝔏 q₁ q₂ q₃ hO)

/-- The condition at the closed value. -/
theorem k08_cond_of_ownSizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hO : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) :
    h.K8Cond h.free :=
  k08_cond_head_of_ownSizes h h.free h.free_q₁ h.free_q₂ h.free_q₃ hO

/-- The kind's field at the closed value. -/
theorem k08_kind_of_ownSizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hO : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) :
    h.Kind h.free KindName.K8 :=
  k08_kind_head_of_ownSizes h h.free h.free_q₁ h.free_q₂ h.free_q₃ hO

end P1K8T

#print axioms P1K8T.k08_cond_head_of_ownSizes
#print axioms P1K8T.k08_kind_head_of_ownSizes
#print axioms P1K8T.k08_cond_of_ownSizes
#print axioms P1K8T.k08_kind_of_ownSizes

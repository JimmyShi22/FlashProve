-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LightHangsOnSized.lean: THE KIND's LIGHT TEST ON A FILLING
(`ownLaidLight`, LaidLight.lean of this folder), AT THE SWITCHES' OWN DATA JOINED TO THE SHARED
SENDING's (`withSwitchData` S (`K1.lotData` S): Honest/K2/OwnData.lean, Honest/K1/LotData.lean),
HANGS ON THE PUBLIC INSTANCE THROUGH ONE Bool ALONE: THE SIZES' TEST ON THE COVERED POSITIONS OF ITS
REQUEST. SO ITS YES AT ONE INSTANCE WHOSE Bool HOLDS IS ITS YES AT EVERY SUCH INSTANCE, AND HANDS
THE KIND's PUBLIC TEST `publicOk` (Honest/K2/Sim.lean) THERE. By the writers of the merge of the
claims on the weights (sub-protocol K11). PUBLIC DATA ALONE. One definition (a test). Lemmas; none
of the library's goals.

  `ownSeated` Z G p       A PUBLIC TEST: each own message of the switch's own sending has a seat
                          among the switches' (`switchSeat`). The list is `ownLaidLight`'s own
  `ownSeated_gives`       its yes, in the form of the first clause of the second premise of
                          `publicOk_with` (PublicAtJoined.lean of this folder)
  `ownSeated_bites`       THE TEST CAN SAY NO: at a place of another kind than K2 it says yes only
                          where there is no own message to ask about
  `ownSeated_false`       so there, where there is one, it says no. THE TOOTH IS GENERAL: no closed
                          place at which the test says no is written here
  `joined_lays_congr`     where the Bool is the same at ξ and ξ₀: the joined data lay an element at
                          the same places
  `light_congr`           under the test: SO THE LIGHT TEST SAYS THE SAME AT ξ AND ξ₀
  `publicOk_of_light_at`  under the test · the Bool holds at ξ and at ξ₀ · the light test's yes at
                          ξ₀ ⊢ `publicOk` at ξ

How. The instance reaches the joined data in one term alone, `u3RowsOf` Z G ξ, behind three joins by
address; a join's field lays is the second filling's wherever the first is not asked:
`u3Rows_lays_congr` (U3LaysOfSized.lean of this folder). The light test reads of a filling its field
lays (`arraysLaidLight_lays`, PublicAtJoined.lean) and, at the switch's own sending alone,
`RowData.readyAt`: at a seat that is the switches' own data's, which reads no instance
(`with_own_ready`, Honest/K2/OwnData.lean); over the list's members by the library's
`P5T.all_congr_mem` (Johnson/P5T/MembersPlain.lean).

NEAR. `publicOk_with` (PublicAtJoined.lean): it splits the test at ONE instance into the two
fillings' shares; this file compares TWO instances.

WHAT IT IS NOT. ONE WAY: a no of the light test says nothing of `publicOk`. That the light test says
yes at any instance is not said; nor that the test `ownSeated` does at any place; nor that the Bool
holds at any instance (CovOfAtStart.lean of this folder has that from the description's test on the
instance, under the head). Stated at the joined term, not at the frame's authors' `widerRows`
(Honest/AtPureWider.lean), which unfolds to it. Nothing on whether the data in front are ready:
`publicOk` does not ask it.

IT STANDS OVER FILES THAT ARE NOT IN THIS LIBRARY: the files named above of Honest/K1/ and
Johnson/HonestTrace/, other groups of authors'.

Limits. Congruences. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.U3LaysOfSized
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtJoined
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.P5T.MembersPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (covOf u3RowsOf)

/-- **A PUBLIC TEST**: each own message of the switch's own sending has a seat. -/
def ownSeated (Z : Pub) (G : Ground) (p : SwitchPlace) : Bool :=
  (p.others.toList.take (p.others.size - 1)).zipIdx.all fun n =>
    (switchSeat Z G (p.ownAddr n.2)).isSome

/-- Its yes. -/
theorem ownSeated_gives {Z : Pub} {G : Ground} {p : SwitchPlace} (h : ownSeated Z G p = true) :
    ∀ n ∈ (p.others.toList.take (p.others.size - 1)).zipIdx,
      (switchSeat Z G (p.ownAddr n.2)).isSome = true :=
  List.all_eq_true.1 h

/-- **The test can say no**: at a place of another kind its yes leaves no own message. -/
theorem ownSeated_bites {Z : Pub} {G : Ground} {p : SwitchPlace} (hk : p.place.kind ≠ .K2)
    (h : ownSeated Z G p = true) : (p.others.toList.take (p.others.size - 1)).zipIdx = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun n hn => ?_
  have t := ownSeated_gives h n hn
  rw [switchSeat_none Z G (p.ownAddr n.2) hk] at t
  cases t

/-- So at a place of another kind with an own message to ask about the test says no. -/
theorem ownSeated_false {Z : Pub} {G : Ground} {p : SwitchPlace} (hk : p.place.kind ≠ .K2)
    (hn : (p.others.toList.take (p.others.size - 1)).zipIdx ≠ []) : ownSeated Z G p = false :=
  Bool.eq_false_iff.2 fun h => hn (ownSeated_bites hk h)

variable {Z : Pub} {G : Ground} {ξ ξ₀ : ProofFile.Inst}

/-- **The joined data lay an element at the same places.** -/
theorem joined_lays_congr (S : Sz)
    (h : ((covOf Z G ξ).toOption.getD default).sized G.W.hS.T =
      ((covOf Z G ξ₀).toOption.getD default).sized G.W.hS.T) :
    (withSwitchData S (K1.lotData S) Z G ξ).lays =
      (withSwitchData S (K1.lotData S) Z G ξ₀).lays := by
  unfold withSwitchData K1.lotData K1.lotFill RowData.join u3RowsOf
  dsimp only
  rw [u3Rows_lays_congr h]

/-- **The light test says the same at the two instances.** -/
theorem light_congr (S : Sz) {p : SwitchPlace} (hs : ownSeated Z G p = true)
    (h : ((covOf Z G ξ).toOption.getD default).sized G.W.hS.T =
      ((covOf Z G ξ₀).toOption.getD default).sized G.W.hS.T)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) :
    ownLaidLight (withSwitchData S (K1.lotData S) Z G ξ) lay p segs =
      ownLaidLight (withSwitchData S (K1.lotData S) Z G ξ₀) lay p segs := by
  have e : arraysLaidLight (withSwitchData S (K1.lotData S) Z G ξ) =
      arraysLaidLight (withSwitchData S (K1.lotData S) Z G ξ₀) := by
    funext lay' codes s seg m a
    exact arraysLaidLight_lays (congrFun (joined_lays_congr S h) a) lay' codes s seg m
  unfold ownLaidLight
  rw [e]
  refine congrArg (fun b => _ && b) (P5T.all_congr_mem _ _ _ fun n hn => ?_)
  dsimp only
  rw [with_own_ready S (K1.lotData S) Z G ξ [] _ (ownSeated_gives hs n hn),
    with_own_ready S (K1.lotData S) Z G ξ₀ [] _ (ownSeated_gives hs n hn)]

/-- **The light test's yes at one instance hands the public test at every instance whose Bool
holds.** -/
theorem publicOk_of_light_at (S : Sz) {p : SwitchPlace} (hs : ownSeated Z G p = true)
    (hb : ((covOf Z G ξ).toOption.getD default).sized G.W.hS.T = true)
    (hb₀ : ((covOf Z G ξ₀).toOption.getD default).sized G.W.hS.T = true)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (hl : ownLaidLight (withSwitchData S (K1.lotData S) Z G ξ₀) lay p segs = true) :
    publicOk (withSwitchData S (K1.lotData S) Z G) lay p segs ξ = true :=
  publicOk_of_light _ lay p segs ξ ((light_congr S hs (hb.trans hb₀.symm) lay segs).trans hl)

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.ownSeated
#print axioms ProofFile.Honest.K2.Law.ownSeated_gives
#print axioms ProofFile.Honest.K2.Law.ownSeated_bites
#print axioms ProofFile.Honest.K2.Law.ownSeated_false
#print axioms ProofFile.Honest.K2.Law.joined_lays_congr
#print axioms ProofFile.Honest.K2.Law.light_congr
#print axioms ProofFile.Honest.K2.Law.publicOk_of_light_at

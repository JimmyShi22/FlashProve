-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicOkAtJoined.lean: AT THE SWITCHES' OWN DATA JOINED TO THE
SHARED SENDING's (`K2.withSwitchData` S (`K1.lotData` S) Z G): THE CODE SWITCH's PUBLIC TEST
`K2.publicOk` IS THE SAME AT TWO INSTANCES AT WHICH ONE Bool IS THE SAME: THE SIZES' TEST ON THE
COVERED POSITIONS OF THE REQUEST. AN EQUATION AT `K2.publicOk` ITSELF, AT TWO INSTANCES AND ONE
FILLING. Three theorems; no definition.

  `mem_zipIdx_of_lt`      a list's member with its number is a member of the numbered list
  `own_length`            the switch's own sending but its last has p.others.size - 1 members
  `publicOk_joined_congr` hs: `K2.Law.ownSeated` Z G p = true; h: the Bool is the same at ξ and ξ₀
                          ⊢ `K2.publicOk` at ξ is `K2.publicOk` at ξ₀

By: `publicOk_of_lays_at` (PublicOkReadsAt.lean); its hl and ho from `K2.Law.joined_lays_congr`, its
hr from `K2.Law.ownSeated_gives` (both Honest/K2/Law/LightHangsOnSized.lean) and `K2.with_own_ready`
(Honest/K2/OwnData.lean). `K2.Law.light_congr`, in that file, says the like of the kind's light
test, whose yes gives `K2.publicOk`'s and whose no means nothing: this one goes both ways.

Limits. TWO INSTANCES AT ONE FILLING: nothing on two fillings. A DEFAULT STANDS IN THE STATEMENT:
where `covOf` returns an error at an instance, the Bool is asked at the default covered positions: h
then compares that. That the test says yes at any instance is not said; nor that the Bool holds at
any; nor that `K2.Law.ownSeated` does at any place (`ownSeated_at_head`,
Honest/K2/Law/OwnSeatedAtHead.lean, has that under the head and the opening). Stated at the joined
term, not at `widerRows` (Honest/AtPureWider.lean), which unfolds to it. All limits of
PublicOkReadsAt.lean and LightHangsOnSized.lean hold.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkReadsAt
import Johnson.Desc.ProofFile.Honest.K2.Law.LightHangsOnSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (covOf)

/-- A list's member with its number is a member of the numbered list. -/
theorem mem_zipIdx_of_lt {α : Type} (l : List α) {n : Nat} (h : n < l.length) :
    (l[n], n) ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  exact List.getElem?_eq_getElem h

/-- The own sending but its last has p.others.size - 1 members. -/
theorem own_length (p : K2.SwitchPlace) :
    (p.others.toList.take (p.others.size - 1)).length = p.others.size - 1 := by
  rw [List.length_take, Array.length_toList]
  omega

/-- **THE PUBLIC TEST AT THE JOINED DATA IS THE SAME AT TWO INSTANCES AT WHICH THE Bool IS.**
CONDITIONAL: hs, h. -/
theorem publicOk_joined_congr {Z : Pub} {G : Ground} {ξ ξ₀ : ProofFile.Inst} (S : Sz)
    {p : K2.SwitchPlace} (hs : K2.Law.ownSeated Z G p = true)
    (h : ((covOf Z G ξ).toOption.getD default).sized G.W.hS.T =
      ((covOf Z G ξ₀).toOption.getD default).sized G.W.hS.T)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) :
    K2.publicOk (K2.withSwitchData S (K1.lotData S) Z G) lay p segs ξ =
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Z G) lay p segs ξ₀ := by
  have e := K2.Law.joined_lays_congr S h
  refine publicOk_of_lays_at _ _ lay p segs ξ ξ₀ (fun _ _ a _ _ => congrFun e a)
    (fun n _ => congrFun e (p.ownAddr n)) fun n hn => ?_
  have hn' : n < (p.others.toList.take (p.others.size - 1)).length := by
    rw [own_length]
    exact hn
  have hseat : (K2.switchSeat Z G (p.ownAddr n)).isSome = true :=
    K2.Law.ownSeated_gives hs _ (mem_zipIdx_of_lt _ hn')
  rw [K2.with_own_ready S (K1.lotData S) Z G ξ [] _ hseat,
    K2.with_own_ready S (K1.lotData S) Z G ξ₀ [] _ hseat]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mem_zipIdx_of_lt
#print axioms ProofFile.Honest.K5.own_length
#print axioms ProofFile.Honest.K5.publicOk_joined_congr

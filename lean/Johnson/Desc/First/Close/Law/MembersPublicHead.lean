-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MembersPublicHead.lean (kind K10): THE MEMBERS OF THE HEAD's LINK's GROUP (l = 24), IN THEIR ORDER, AS A PUBLIC
LIST OF NUMBERS: the like of MembersPublic.lean (beside this file), which stands at 1 ≤ l < 24. A definition with code, a statement
and its proof: calls of flags_head_named (Johnson/IMR/FlagsHeadNamed.lean), size_at_table
(Johnson/IMR/FlagsNamed.lean) and flat_358 (Johnson/IMR/EndFive.lean).

What is said.
  `membersPubHead N sh`: the list, off the table's numbers N (msgsAt at the places 339, 342, 344 of the written list: in front of the
    head's link's switch and of its two later sendings) and the request's shape sh.
  `members_public_head`: **in scope, under the opening at OnBytes.secondHashFunction and F.planOk, at the cuts 340 + n, 5 ≤ n ≤ 10 (n = 10: in front
    of the closing kind's own sub-protocol): there are the open link L, of number 24, and the group G at number 24, and
    G.members.toList = membersPubHead N sh**, at N := N₀.withTold placesW (toldOf c.blocksInOrder), N₀ free, sh := Z.first.shape.

Limits. At a fold from the start that returns: that one returns is shown of no proof. o := OnBytes.secondHashFunction alone. IT DOES NOT SAY THAT THIS LIST
IS `membersPub N sh 24` (whose counts are read at the places 338, 341, 343), NOR THAT IT IS (membersOf lo).map ‹the plan's numbering›: each
is a closed fact, to be evaluated. Nothing on soundness.

-/
import Johnson.IMR.FlagsHeadNamed
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- **The members of the head's link's group, in their order, off public numbers.** -/
def membersPubHead (N : Numbers) (sh : Params.ReqShape) : List Nat :=
  [N.msgsAt IM.placesW[339]?] ++
    (List.range (K2.targetAt sh 24).kept.size).map (· + (N.msgsAt IM.placesW[339]? + 1)) ++
    ((List.range (Meaning.K2.msgsAt sh 24 0)).map
        (· + (N.msgsAt IM.placesW[339]? + (1 + (K2.targetAt sh 24).kept.size))) ++
      (List.range (Meaning.K2.msgsAt sh 24 1)).map (· + N.msgsAt IM.placesW[342]?) ++
      (List.range (Meaning.K2.msgsAt sh 24 2)).map (· + N.msgsAt IM.placesW[344]?))

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE ORDER OF THE HEAD's LINK's GROUP's MEMBERS IS PUBLIC.** -/
theorem members_public_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List Col} {n : Nat} (h5 : 5 ≤ n)
    (hn : n ≤ 10) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = 24 ∧ t.st.groups[24]? = some G ∧
      G.members.toList =
        membersPubHead (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape := by
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, L, G, f₀, f₃, f₅, hL, e2, hG, em, ek, eo⟩ :=
    Meaning.K2.flags_head_named hS hR O h5 hn g
  have hlen := Meaning.K2.flat_358 hS O
  have s0 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 339) (by omega) f₀
  have s3 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 342) (by omega) f₃
  have s5 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 344) (by omega) f₅
  refine ⟨L, G, hL, e2, hG, ?_⟩
  unfold membersPubHead
  rw [← s0, ← s3, ← s5, em, ek, eo]
  simp [Array.toList_append, Array.toList_map, Array.toList_range]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.members_public_head

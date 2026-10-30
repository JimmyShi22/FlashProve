-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MembersPublic.lean (kind K10): THE MEMBERS OF A LINK's GROUP, IN THEIR
ORDER, AS A PUBLIC LIST OF NUMBERS: at the cuts of the first chain's fold in front of the closing
of a
link l, 1 ≤ l < 24. A definition with code, a statement and its proof: calls of
flags_named and size_at_table (Johnson/IMR/FlagsNamed.lean) and flat_358 (Johnson/IMR/EndFive.lean).

Why. What K10's law asks of the statement in front (`RowAsks`, HRowAtFa.lean) has ONE letter "no"
(member of the written list ↦ its number in the statement). Its payers hold two terms: one reads the
state's group's own list of members (noOf lo G.members.toList), one is public (the place of the
member's seat in the plan's list). To lay them on one another one must know THE ORDER of G.members.
The table's promise compares sets; "in order" and "tidy" say nothing on it.
flags_named
does: the switch's message, the kept copies, the three sendings' messages, each a range off a count
of oracle messages at a cut of the same fold; its size_at_table says each such count in the table's
own words.

What is said.
  `membersPub N sh l`: the list, off the table's numbers N (msgsAt at the places 14 l + 2, + 5, + 7
    of the written list) and the request's shape sh (how many kept copies; how many messages a
    sending).
  `members_public`: **in scope, under the opening at OnBytes.secondHashFunction and F.planOk, at the cuts
    14 l + 8 + n, n ≤ 4 (n = 4: in front of the closing kind's own sub-protocol): there are the open
    link L, of number l, and the group G at number l, and G.members.toList = membersPub N sh l**, at
    N := N₀.withTold placesW (toldOf c.blocksInOrder), N₀ free, sh := Z.first.shape.

Limits. 1 ≤ l < 24: THE FIRST LINK AND THE HEAD's ARE NOT HERE. At a fold from the start that
returns:
that one returns is shown of no proof. o := OnBytes.secondHashFunction alone. IT DOES NOT YET SAY THAT THIS
LIST IS
(membersOf lo).map ‹the public numbering›: that is a closed fact a link, to be evaluated. Nothing on
soundness.

-/
import Johnson.IMR.FlagsNamed
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- **The members of link l's group, in their order, off public numbers.** -/
def membersPub (N : Numbers) (sh : Params.ReqShape) (l : Nat) : List Nat :=
  [N.msgsAt IM.placesW[14 * l + 2]?] ++
    (List.range (K2.targetAt sh l).kept.size).map (· + (N.msgsAt IM.placesW[14 * l + 2]? + 1)) ++
    ((List.range (Meaning.K2.msgsAt sh l 0)).map
        (· + (N.msgsAt IM.placesW[14 * l + 2]? + (1 + (K2.targetAt sh l).kept.size))) ++
      (List.range (Meaning.K2.msgsAt sh l 1)).map (· + N.msgsAt IM.placesW[14 * l + 5]?) ++
      (List.range (Meaning.K2.msgsAt sh l 2)).map (· + N.msgsAt IM.placesW[14 * l + 7]?))

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE ORDER OF A GROUP's MEMBERS IS PUBLIC.** -/
theorem members_public (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List Col} {n : Nat} (hn : n ≤ 4) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = l ∧ t.st.groups[l]? = some G ∧
      G.members.toList =
        membersPub (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape l := by
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, L, G, f₀, f₃, f₅, hL, e2, hG, em, ek, eo⟩ :=
    Meaning.K2.flags_named hS hR O h1 h24 hn g
  have hlen := Meaning.K2.flat_358 hS O
  have s0 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 14 * l + 2) (by omega) f₀
  have s3 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 14 * l + 5) (by omega) f₃
  have s5 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 14 * l + 7) (by omega) f₅
  refine ⟨L, G, hL, e2, hG, ?_⟩
  unfold membersPub
  rw [← s0, ← s3, ← s5, em, ek, eo]
  simp [Array.toList_append, Array.toList_map, Array.toList_range]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.members_public

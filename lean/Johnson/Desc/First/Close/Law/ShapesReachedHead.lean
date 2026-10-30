-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ShapesReachedHead.lean (kind K10): `ShapesAre` AT A REACHED STATE IN FRONT OF THE CLOSING KIND's OWN SUB-PROTOCOL OF THE HEAD's LINK (l = 24; the number 350), AT
WHATEVER NUMBERING no THAT MEETS TWO NAMED PREMISES: the like of ShapesReached.lean (beside this file), which stands at 1 ≤ l < 24. Statements and proofs: calls.

What is said.
  `kept_at_head`: THE CLAUSE «kept»: at the cuts 340 + n, 5 ≤ n ≤ 10: the open link, its frame's group 24, the group G: G.kept.toList = (membersOf lo).map (kbAt shapeFull 24 lo).
  `shapesAre_at_fold_head`: THE JOIN, AT A FOLD: with hT3 (the public list `membersPubHead` is (membersOf lo).map no) and hH4 (the members' shapes at no).
  `shapesAre_reached_head`: **the same at a state reached at 350.**
BY: `members_public_head` (MembersPublicHead.lean) · `flags_at_head` (Johnson/LPFK10R/HeadLinkJoins.lean) with the first half of the kernel fact `joiners_full` ·
`members_head` (Johnson/IMR/HeadMembers.lean).

Limits. hsh, hT3, hH4 are premises. In scope; o := OnBytes.secondHashFunction. At a fold that returns: that one returns is shown of no proof. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.MembersPublicHead
import Johnson.Desc.First.Close.Law.ShapesReached
import Johnson.LPFK10R.HeadLinkJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE CLAUSE "kept", AT THE HEAD's LINK.** -/
theorem kept_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List Col}
    {n : Nat} (h5 : 5 ≤ n) (hn : n ≤ 10) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.check.frame.group = 24 ∧
      t.st.groups[24]? = some G ∧
      G.kept.toList = (membersOf (linksFullLit.getD 24 [])).map
        (kbAt shapeFull 24 (linksFullLit.getD 24 [])) := by
  obtain ⟨G, a1, -, a3⟩ := LPFK10.flags_at_head hS hR O hsh h5 hn g
  obtain ⟨L, G', -, b1, -, b3, b4, -, -, -⟩ := Meaning.K2.members_head hS hR O hn g
  obtain rfl : G = G' := Option.some.inj (a1.symm.trans b4)
  have hj := List.all_eq_true.1 joiners_full 24 (List.mem_range.2 (by omega))
  unfold joinersFit at hj
  rw [Bool.and_eq_true] at hj
  exact ⟨L, G, b1, b3, a1, a3.trans (of_decide_eq_true hj.1).symm⟩

/-- **THE JOIN, AT A FOLD.** -/
theorem shapesAre_at_fold_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List Col} {n : Nat} (h5 : 5 ≤ n) (hn : n ≤ 10) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (no : Fin (linksFullLit.getD 24 []).length → Nat)
    (hT3 : membersPubHead (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD 24 []),
      (t.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD 24 []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24 ∧
      t.st.groups[24]? = some G ∧
      ShapesAre t.st G (linksFullLit.getD 24 []) (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        no := by
  obtain ⟨L, G, hL, e2, hG, hm⟩ := members_public_head hS hR O hF N₀ h5 hn g
  obtain ⟨L', G', hL', e3, hG', hk⟩ := kept_at_head hS hR O hsh h5 hn g
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  rw [hsh] at hm
  exact ⟨L, G, hL, e2, e3, hG, ⟨hm.trans hT3, hk, hH4⟩⟩

/-- **THE SAME AT A REACHED STATE IN FRONT OF THE CLOSING KIND's OWN SUB-PROTOCOL.** -/
theorem shapesAre_reached_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 350 (z, s))
    (no : Fin (linksFullLit.getD 24 []).length → Nat)
    (hT3 : membersPubHead (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD 24 []),
      (s.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD 24 []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), s.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24 ∧
      s.st.groups[24]? = some G ∧
      ShapesAre s.st G (linksFullLit.getD 24 []) (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        no := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact shapesAre_at_fold_head hS hR O hF hsh N₀ (n := 10) (by omega) (Nat.le_refl 10) f no hT3
    hH4

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.kept_at_head
#print axioms VerifiableInference.Desc.First.Close.shapesAre_at_fold_head
#print axioms VerifiableInference.Desc.First.Close.shapesAre_reached_head

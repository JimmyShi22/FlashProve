-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ShapesReached.lean (kind K10): `ShapesAre` (LayoutOfShapes.lean, beside
this file: the group's members, in order, are the written list's under a numbering "no"; its flags
are the written ones; each member has the written shape) AT A REACHED STATE IN FRONT OF THE CLOSING
KIND's OWN SUB-PROTOCOL OF A LINK l, 1 ≤ l < 24, AT ANY NUMBERING no THAT MEETS TWO NAMED PREMISES.
Statements and proofs: calls.

Why. Four debts of K10's law hang on this one sentence at the PUBLIC numbering of the plan. What lay
stood at a numbering read off the state's own group, and at "a fold from the start returns t".

What is said. lo := the l-th written list; kb := the written flags (kbAt shapeFull l lo).
  `k10_at_twelve`: at l < 24 the place number 14 l + 12 of the written list of places is of the
    kind K10 (the kernel fact k10_place_w, its index computed).
  `kept_at_cut`: **the clause "kept"**, at the cuts 14 l + 8 + n, n ≤ 4: G.kept.toList =
    (membersOf lo).map kb: by flags_at (Johnson/IMR/FlagsAt.lean), through flags_at_cut
    (Johnson/LPFK10R/ShapesAtCut.lean), and the first half of the
    kernel fact joiners_full. IT NAMES NO NUMBERING AND TAKES NO PREMISE ON SHAPES.
  `shapesAre_at_fold`: **the join, at a fold**: members from members_public (MembersPublic.lean) and
    hT3; kept from kept_at_cut; shape is hH4.
  `shapesAre_reached`: **the same AT A REACHED STATE**: Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z)
    (14 l + 12) (z, s): what is reached is the end of a fold (Johnson/Top/H0/Walk/Reach.lean).

THE TWO PREMISES THAT ARE LEFT.
  hT3  membersPub N shapeFull l = (membersOf lo).map no: CLOSED once N's told part is: a fact a
link:
       NOT EVALUATED: IT CAN BE FALSE.
  hH4  every member's message, at its number no i, has the written shape: on the state.
BESIDE: in scope · the opening at OnBytes.secondHashFunction · F.planOk · hsh : Z.first.shape = shapeFull.

Limits. 1 ≤ l < 24. o := OnBytes.secondHashFunction alone. That no parts the list's members is not said here.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.MembersPublic
import Johnson.LPFK10R.ShapesAtCut
import Johnson.LPFK10R.CloseShare
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

/-- At l < 24 the closing kind's own sub-protocol stands at the number 14 l + 12. -/
theorem k10_at_twelve {l : Nat} (hl : l < 24) :
    ∃ p, LPFK10.PW[14 * l + 12]? = some p ∧ p.kind = KindName.K10 := by
  obtain ⟨p, hp, hk⟩ := LPFK10.k10_place_w (l := l) (by omega)
  have e : 14 * l + LPFK10.nA l + 5 = 14 * l + 12 := by
    have : LPFK10.nA l = 7 := if_neg (by omega)
    omega
  rw [e] at hp
  exact ⟨p, hp, hk⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE CLAUSE "kept".** -/
theorem kept_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List Col} {n : Nat} (hn : n ≤ 4) {t : S} {r : List Fmt.RoundView}
    {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.check.frame.group = l ∧
      t.st.groups[l]? = some G ∧
      G.kept.toList = (membersOf (linksFullLit.getD l [])).map
        (kbAt shapeFull l (linksFullLit.getD l [])) := by
  obtain ⟨L, G, a1, -, a3, a4, -, a6⟩ := LPFK10.flags_at_cut hS hR O hsh h1 h24 hn g
  have hj := List.all_eq_true.1 joiners_full l (List.mem_range.2 (by omega))
  unfold joinersFit at hj
  rw [Bool.and_eq_true] at hj
  exact ⟨L, G, a1, a3, a4, a6.trans (of_decide_eq_true hj.1).symm⟩

/-- **THE JOIN, AT A FOLD.** -/
theorem shapesAre_at_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List Col} {n : Nat} (hn : n ≤ 4) {t : S}
    {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (no : Fin (linksFullLit.getD l []).length → Nat)
    (hT3 : membersPub (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD l []),
      (t.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD l []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = l ∧ L.check.frame.group = l ∧
      t.st.groups[l]? = some G ∧
      ShapesAre t.st G (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) no := by
  obtain ⟨L, G, hL, e2, hG, hm⟩ := members_public hS hR O hF N₀ h1 h24 hn g
  obtain ⟨L', G', hL', e3, hG', hk⟩ := kept_at_cut hS hR O hsh h1 h24 hn g
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  rw [hsh] at hm
  exact ⟨L, G, hL, e2, e3, hG, ⟨hm.trans hT3, hk, hH4⟩⟩

/-- **THE SAME AT A REACHED STATE IN FRONT OF THE CLOSING KIND's OWN SUB-PROTOCOL.** -/
theorem shapesAre_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 12) (z, s))
    (no : Fin (linksFullLit.getD l []).length → Nat)
    (hT3 : membersPub (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD l []),
      (s.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD l []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), s.link? = some L ∧ L.link = l ∧ L.check.frame.group = l ∧
      s.st.groups[l]? = some G ∧
      ShapesAre s.st G (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) no := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  have e : 14 * l + 12 = 14 * l + 8 + 4 := by omega
  rw [e] at f
  exact shapesAre_at_fold hS hR O hF hsh N₀ h1 h24 (Nat.le_refl 4) f no hT3 hH4

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_at_twelve
#print axioms VerifiableInference.Desc.First.Close.kept_at_cut
#print axioms VerifiableInference.Desc.First.Close.shapesAre_at_fold
#print axioms VerifiableInference.Desc.First.Close.shapesAre_reached

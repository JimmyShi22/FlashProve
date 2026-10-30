-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/ReplyHears.lean: FOR THE ROW token_carried_to_start: THE HALF "BEHIND" OF K7's ROW: WHERE THE NEXT TOKEN's BLOCK's DECISION GOES ON, A TOKEN's NUMBER BELOW THE VOCABULARY's SIZE IS HEARD BEHIND IT: at the block as it rides, and at "any block, and then it" (the piece at
"H:1" is a joined block). Stated UNFOLDED: each top is, by definition, Block.Hears h ok b (Desc/Sound/RepOfLeaves.lean: := ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, h s' = some x ∧ ok x) at h := fun s => (S.heard s).map tokOf, ok := (· < W.hS.V): NO TWIN OF THAT NAME IS DECLARED HERE.
  behind_andThen   general: a sentence on the record behind every yes of q holds behind every yes of p.andThen name q.      reply_hears | joined_hears   the two tops at (S.heard ·).map tokOf.      ofNat_token   a token of a vocabulary below the prime is ofNat of its own number.
  joined_hearsTok  **THE LETTER AS ASKED**: under W.hS.V ≤ ppref.V: behind every yes of front.andThen name (Reply.blockOf W l), for every front: First.S.heardTok? (Johnson/Desc/First/HeardAsked.lean:39-40), WRITTEN OUT, is some y, y < ppref.V: by definition «(front.andThen name (Reply.blockOf W l)).Hears
                   (fun s => s.heardTok?) (· < ppref.V)». IN THE FILES OF THE PROOF FILE's DESCRIPTION (namespace ProofFile) THE PIECE AT "H:1" IS front.andThen "H:1" (P4.k7Core G), k7Core G := Reply.blockOf G.W (G.built.size - 1), a Block S Unit (read in other versions of two files [these versions are not in this library]; in this library: Johnson/Desc/ProofFile/Lots/H1.lean: h1Own · Johnson/Desc/ProofFile/Lot/K6K7.lean: k7Core) [by reading]: so getS is the identity there.
EVERY LETTER UNDER "THERE IS": y: pinned by the equation beside it. UNDER "FOR ALL": front, name: any.
WHAT IT IS NOT. heardTok? AND Block.Hears ARE WRITTEN OUT, NOT IMPORTED: that the written text is theirs is held by reading alone: whoever joins says "exact joined_hearsTok …" and Lean holds it · W.hS.V ≤ ppref.V is a premise (under FullH W.hS an equation) · THE HALF "IN FRONT" (nothing heard in front of the JOINED block) IS NOT
HAD: Law/K07MeansHeard.lean's heard_front_none speaks of K7's own block; in front of the joined block the
first half may still empty the seat: its user asks it of the table's promise. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K07MeansHeard
import Inst.Model.Program

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- A sentence on the record behind every yes of a block's decision holds behind every yes of "any block, and then that block". -/
theorem behind_andThen {S' Cl : Type} (name : String) (p q : Block S' Cl) (P : S' → Prop)
    (hq : ∀ s rs gs s', q.decide s rs gs = .ok s' → P s') :
    ∀ s rs gs s', (p.andThen name q).decide s rs gs = .ok s' → P s' := by
  intro s rs gs s' h
  have h' : ((p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s1 =>
      q.decide s1 (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  cases hp : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    exact hq s1 _ _ s' h'

/-- **BEHIND EVERY YES OF THE NEXT TOKEN's BLOCK AS IT RIDES: A TOKEN IS HEARD, AND ITS NUMBER IS BELOW THE VOCABULARY's SIZE.** -/
theorem reply_hears (W : OnBytes.Model.Verify.Public) (l : Nat) :
    ∀ s rs gs s', (Reply.blockOf W l).decide s rs gs = .ok s' →
      ∃ y, (S.heard s').map OnBytes.Desc.Reply.tokOf = some y ∧ y < W.hS.V := by
  intro s rs gs s' hd
  obtain ⟨x, hx, ht⟩ := heard_behind_some l W.hS.V (s := s) (rs := rs) (gs := gs) hd
  refine ⟨OnBytes.Desc.Reply.tokOf x, by rw [hx]; rfl, ?_⟩
  simp only [OnBytes.Desc.Reply.isToken, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ht.2

/-- The same behind "any block, and then the next token's". -/
theorem joined_hears (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) :
    ∀ s rs gs s', (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok s' →
      ∃ y, (S.heard s').map OnBytes.Desc.Reply.tokOf = some y ∧ y < W.hS.V :=
  behind_andThen name front (Reply.blockOf W l) _ (reply_hears W l)

/-- A token of a vocabulary below the prime is the field's element of its own number. -/
theorem ofNat_token (V : Nat) (hV : V ≤ OnBytes.pW.toNat) (x : OnBytes.E)
    (ht : OnBytes.Desc.Reply.isToken V x = true) : OnBytes.Model.ofNat x.c0.toNat = x := by
  simp only [OnBytes.Desc.Reply.isToken, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
  obtain ⟨⟨h1, h2⟩, h0⟩ := ht
  obtain ⟨a, b, c⟩ := x
  simp only at h0 h1 h2
  subst h1
  subst h2
  unfold OnBytes.Model.ofNat OnBytes.Model.fOfNat OnBytes.ofF OnBytes.E.mk3
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h0 hV)]
  simp

/-- **THE LETTER THAT THE ROW token_carried_to_start ASKS, WITH First.S.heardTok? WRITTEN OUT** (Johnson/Desc/First/HeardAsked.lean:39-40: s.heard.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none): behind every yes of "any block, and then the next
token's block as it rides" a token's number below the reference's vocabulary is heard. -/
theorem joined_hearsTok (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (hV : W.hS.V ≤ Inst.Model.ppref.V) :
    ∀ s rs gs s', (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok s' →
      ∃ y, ((S.heard s').bind fun g =>
        if OnBytes.Model.ofNat g.c0.toNat == g then some g.c0.toNat else none) = some y ∧
        y < Inst.Model.ppref.V := by
  refine behind_andThen name front (Reply.blockOf W l) _ fun s rs gs s' hd => ?_
  obtain ⟨x, hx, ht⟩ := heard_behind_some l W.hS.V (s := s) (rs := rs) (gs := gs) hd
  have hp : W.hS.V ≤ OnBytes.pW.toNat := Nat.le_trans hV (by decide)
  have e := ofNat_token W.hS.V hp x ht
  have h0 : x.c0.toNat < W.hS.V := by
    simp only [OnBytes.Desc.Reply.isToken, Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ht.2
  refine ⟨x.c0.toNat, ?_, Nat.lt_of_lt_of_le h0 hV⟩
  rw [hx]
  show (if OnBytes.Model.ofNat x.c0.toNat == x then some x.c0.toNat else none) = _
  rw [e, if_pos (beq_self_eq_true _)]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.joined_hearsTok
#print axioms VerifiableInference.Desc.Kinds.Head.Law.behind_andThen
#print axioms VerifiableInference.Desc.Kinds.Head.Law.reply_hears
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joined_hears

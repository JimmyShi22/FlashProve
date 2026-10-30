-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadUnheard.lean: AT THE HEAD's LINK: WHO MAKES THE PREMISE hU OF
made_head (K2C/MadeLook.lean): in front of the code switch's place «H:2» the head's own part of the
state has the plan's state of the smallness test and nothing heard by the lookup on the calls. NO
BLOCK IMPORTS THIS FILE.

  HeadUnheard tl s   the state stands in the head's link, not yet opened; its state of the
                     smallness test is tl; nothing is heard by the lookup on the calls
  front_unheard      MADE behind an accept of "H.0.front" (K2C/Head.lean: headFrontQ tl)
  reply_unheard      KEPT by the next token's block as it is seated (by
                     reply_record, Kinds/Law/ReplyPins.lean: the state behind, written out)
  joined_unheard     so behind the two as one block, whatever stood in front: the form of «H:1»
                     (Johnson/Desc/ProofFile/Lots/H1.lean: h1Own), but for the guard around its
                     first half
  hU_of_unheard      HeadUnheard tl s · tl.heard = none ⟹ hU's body at s
  not_unheard_between   IT CAN FAIL: between two links it is false

IT FOLLOWS CLOSELY, IN FORM AND IN PROOF, NoTables · front_noTables · reply_noTables ·
joined_noTables (Johnson/Desc/Kinds/Law/TablesNotYet.lean),
at two other fields of the same part of the state.
Limits. That border 339 of the written list is reached by an accept of «H:1» alone is not shown
here: hU stands under a fence where it is spent. (Its kin for K2.HeadFresh at reached states:
fresh_reached, Tw/K2C/HeadFreshReached.lean: not read here.) The guard
around the first half of h1Own (Block.guarded) is not unfolded here: hfront is a premise of
joined_unheard. No soundness statement.

-/
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Desc.Kinds.Law.ReplyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Kinds (Reply.blockAt Reply.blockOf)

/-- In the head's link, not yet opened: the smallness test's state is tl, and the lookup on the
calls has heard nothing. -/
def HeadUnheard (tl : HTailF2) (s : S) : Prop :=
  ∃ a, s.here = .head a ∧ a.opened = false ∧ a.tl = tl ∧ a.lookHeard = none

/-- **MADE** behind an accept of the step that enters the head's link. -/
theorem front_unheard {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    HeadUnheard tl s' := by
  unfold headFrontQ at h
  split at h
  · cases h
  · rename_i hb
    split at h
    · cases h
    · cases hx : _root_.Tw.K2.firstFront s.st s.check.frame with
      | error e => rw [hx] at h; cases h
      | ok x =>
        rw [hx] at h
        cases he : s.enterHead? tl with
        | error e => rw [he] at h; cases h
        | ok s₁ =>
          rw [he] at h
          have hat : s.atBetween = true := by simpa using hb
          have e1 : s₁ = s.enterHead tl := by
            unfold S.enterHead? S.unmarked at he
            split at he
            · exact (Except.ok.inj he).symm
            · cases he
          have e2 : ∃ a, s₁.here = .head a ∧ a.opened = false ∧ a.tl = tl ∧
              a.lookHeard = none := by
            rw [e1]
            unfold S.enterHead
            rw [if_pos hat]
            exact ⟨_, rfl, rfl, rfl, rfl⟩
          obtain ⟨a, e2, h1, h2, h3⟩ := e2
          have h' : (match s₁.here with
            | .head a => Except.ok { s₁ with st := x.st, here := .head { a with fr := x.f } }
            | _ => Except.error "B3: the record has not entered the head's link") = .ok s' := h
          rw [e2] at h'
          obtain rfl := Except.ok.inj h'
          exact ⟨_, rfl, h1, h2, h3⟩

/-- **KEPT** by the next token's block as it is seated. -/
theorem reply_unheard (l V : Nat) {tl : HTailF2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s')
    (Z : HeadUnheard tl s) : HeadUnheard tl s' := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record l V hd
  exact Z

/-- So behind the two as one block, whatever stood in front. -/
theorem joined_unheard (W : Verify.Public) (l : Nat) (name : String) (tl : HTailF2)
    (front : Block S Unit)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → HeadUnheard tl s1) :
    ∀ s rs gs s', (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok s' →
      HeadUnheard tl s' := by
  intro s rs gs s' h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok s' := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    exact reply_unheard l W.hS.V h' (hfront _ _ _ _ hp)

/-- **hU's body** (K2C/MadeLook.lean: made_head). -/
theorem hU_of_unheard {tl : HTailF2} {s : S} (Z : HeadUnheard tl s) (hh : tl.heard = none) :
    ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none := by
  obtain ⟨b, hb, _, h2, h3⟩ := Z
  intro a ha
  rw [hb] at ha
  injection ha with ha
  subst ha
  exact ⟨h2 ▸ hh, h3⟩

/-- **It can fail**: between two links. -/
theorem not_unheard_between (tl : HTailF2) {s : S} (h : s.here = .between) :
    ¬ HeadUnheard tl s := by
  rintro ⟨a, ha, _⟩
  rw [h] at ha
  cases ha

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.front_unheard
#print axioms VerifiableInference.Desc.First.K2.reply_unheard
#print axioms VerifiableInference.Desc.First.K2.joined_unheard
#print axioms VerifiableInference.Desc.First.K2.hU_of_unheard
#print axioms VerifiableInference.Desc.First.K2.not_unheard_between

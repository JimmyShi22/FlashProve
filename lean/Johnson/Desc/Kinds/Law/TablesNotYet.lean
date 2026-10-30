-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TablesNotYet.lean.
WHAT IT DOES NOT SHOW. No soundness. THE CHAIN FROM THE HEAD's LINK's ENTRY TO THE BORDER BEHIND THE
OUTPUT HEAD's OWN BLOCK IS NOT WHOLE HERE: of the four places in front of that border this file has
the first (the entry and the next token's block) and the fourth (the output head's own block); THAT
THE SECOND (the code switch, with the quiet step that opens the link) AND THE THIRD (the lookup on
the calls) KEEP "no tables" IS THEIR FILES' TO SHOW. A block of another lot that a chain joins
behind the first place is not covered either.
LETTERS. Under "there is" (NoTables): o: pinned by s.here = .head o.
OBJECT. The field t of the head's link's part of the carried record (Desc/First/State.lean:
HeadOwn): the table of the tables of reads, "none until the reads' quiet step lays them".
USER. Whoever says that at the border right behind the output head's own block the head's runs of
claims are silent (they refuse for want of t), so that a reader "where the run is silent" speaks.
WHAT IT IS. THE TABLES OF READS ARE NOT YET LAID: WHO MAKES THAT SENTENCE, AND TWO BLOCKS THAT KEEP
IT. NoTables s the record stands in the head's link, and t is none.
  front_noTables    MADE: behind a yes of the step that enters the head's link
                    (Top/H0/Tw/K2C/Head.lean: headFrontQ).
  reply_noTables    KEPT by the next token's block as it is seated.
  joined_noTables   so behind the two as one block, whatever stood in front.
  k6_noTables       KEPT by the output head's own block (Law/RowPromise.lean: decide_record).
  seated_noTables   the same at the block as a lot seats it, at its step.
Kin. setHeard_ok (Law/HeardAt.lean) and SamePlanes (Law/PlanesStay.lean) carry
"t is as it was" for other steps.
What makes "t = none" here is front_noTables,
behind a yes of headFrontQ.

-/
import Mathlib
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Desc.Kinds.Law.ReplyPins
import Johnson.Desc.Kinds.Law.SeatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim OpenedColumn)
open VerifiableInference.Desc.First (S)

/-- The record stands in the head's link, and the tables of reads are not laid. -/
def NoTables (s : S) : Prop := ∃ o, s.here = .head o ∧ o.t = none

/-- **MADE** behind a yes of the step that enters the head's link. -/
theorem front_noTables {tl : HTailF2} {s s' : S}
    (h : VerifiableInference.Desc.First.K2.headFrontQ tl s = .ok s') : NoTables s' := by
  unfold VerifiableInference.Desc.First.K2.headFrontQ at h
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
          have e2 : ∃ a, s₁.here = .head a ∧ a.t = none := by
            rw [e1]
            unfold S.enterHead
            rw [if_pos hat]
            exact ⟨_, rfl, rfl⟩
          obtain ⟨a, e2, ht⟩ := e2
          have h' : (match s₁.here with
            | .head a => Except.ok { s₁ with st := x.st, here := .head { a with fr := x.f } }
            | _ => Except.error "B3: the record has not entered the head's link") = .ok s' := h
          rw [e2] at h'
          obtain rfl := Except.ok.inj h'
          exact ⟨_, rfl, ht⟩

/-- **KEPT** by the next token's block as it is seated. -/
theorem reply_noTables (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s')
    (Z : NoTables s) : NoTables s' := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Came.reply_record l V hd
  exact Z

/-- So behind the two as one block, whatever stood in front. -/
theorem joined_noTables (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → NoTables s1) :
    ∀ s rs gs s', (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok s' →
      NoTables s' := by
  intro s rs gs s' h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok s' := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    exact reply_noTables l W.hS.V h' (hfront _ _ _ _ hp)

/-- **KEPT** by the output head's own block. -/
theorem k6_noTables (h : Model.Head.Shape) (iU3 work l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (blockAt h iU3 work l).decide s rs gs = .ok s')
    (Z : NoTables s) : NoTables s' := by
  obtain ⟨a, F1, X, Q, ha, _, _, rfl⟩ := Came.decide_record h iU3 work l hd
  obtain ⟨o, ho, ht⟩ := Z
  rw [ha] at ho
  injection ho with ho
  exact ⟨_, rfl, by show a.t = none; rw [ho]; exact ht⟩

/-- The same at the block as a lot seats it, at its step. -/
theorem seated_noTables {W : Verify.Public} {l : Nat} {ms : List (Nat × Nat)} {b : Block S Claim}
    (h : seatedClaims W l ms = some b) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) (Z : NoTables s) : NoTables s' := by
  obtain ⟨bU, hU, hsU, _⟩ := seated_step h hs
  obtain ⟨gs, hd⟩ := Came.step_decide ft bU s rs cols s' n hsU
  unfold blockOf at hU
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hU
  exact k6_noTables _ _ _ _ hd Z

end VerifiableInference.Desc.Kinds.Head.Law

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Keeps.lean: WHAT AN ACCEPTING STEP OF THE FIRST CHAIN's MEMBER AT
«H:1» ⟨1, some 24, 1, .K7⟩ KEEPS AND TURNS: the clause of `Thread.keeps` at that member, its payer
from the member's own accepting step (the library's `StepYes`), and what readers of the state get of
it.

THE MEMBER IS THREE TEXTS IN A ROW. (i) The entry into the head's segment: `K2.headFrontQ`
(Johnson/Top/H0/Tw/K2C/Head.lean), without a round, guarded. (ii) The next token's sub-protocol:
`Reply.blockOf` (Johnson/Stored/ReplySeatAt.lean). The lot's own sub-protocol is these two joined
(`h1Own`, Johnson/Desc/ProofFile/Lots/H1.lean). (iii) The frame's «opened», joined behind the lot's
(`IM.Joined`), which at the head's segment hands the state on (`keepsOpened`,
Honest/Law/NoHouse/OpenedKeeps.lean).

  `K7Keeps V t m`          (ii): an equation on the whole state: the reply's seat, empty at an
                          unopened head, is laid with a token of V; nothing else turns
  `H1Keeps tl V s m`       (i) and (ii): no mark behind; the entry's clause is the text's own return
  `K7MemberKeeps tl V l s s'`   the member's: (i), (ii), (iii)
  `k7Keeps_of_decide`, `h1Keeps_of_decide`, `h1Keeps_of_step`, `k7MemberKeeps_of_step`   THE PAYERS
  `H1Keeps.reply` and the ten behind it   what readers get: the reply · the mark · the pile · the
      number of the index masks' message · the statement · that message's ledger · that no group
      gains it · where the chain stands

WHAT TURNS AT THE MEMBER: the statement gains one fresh group without a member (the entry); the
chain stands in the head's segment (the entry); the reply's seat is laid (the next token's). SO
NEITHER «the statement is as it was» NOR «what was put out is as it was» HOLDS ACROSS IT.

By calls of the library's `Came.reply_record` (Johnson/Desc/Kinds/Law/ReplyPins.lean), `h1Front`
(Kinds/Law/K6K7LotLeaves.lean), `headFrontQ_rest`, `headFrontQ_st` (Top/H0/Tw/K2C/FrontGroup.lean),
`stepYes_decide` (Top/H0/Walk/ReachInv.lean), and of `keeps_joined_opened`. None is one of the
library's goals.

Limits. One way only: from a yes. Nothing says that a yes can be had. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.OpenedKeeps
import Johnson.Desc.Kinds.Law.K6K7LotLeaves
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest headFrontQ_st withFresh)
open VerifiableInference.Desc.Kinds (Reply.blockAt Reply.blockOf)
open VerifiableInference.Desc.Kinds.Head.Law (h1Front)
open OnBytes.Desc.Reply (isToken)
open OnBytes.Model (HTailF2)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open ProofFile (Cl)

/-! ## 1 The clauses -/

/-- **The next token's own half.** t: behind the entry; m: behind the reply's round. -/
def K7Keeps (V : Nat) (t m : S) : Prop :=
  ∃ (o : HeadOwn) (x : OnBytes.E), t.here = .head o ∧ o.opened = false ∧ t.out.reply = none ∧
    isToken V x = true ∧ m = { t with out := { t.out with reply := some x } }

/-- **The lot's whole sub-protocol at «H:1».** -/
def H1Keeps (tl : HTailF2) (V : Nat) (s m : S) : Prop :=
  m.failed = none ∧ ∃ t, headFrontQ tl s = .ok t ∧ K7Keeps V t m

/-- **The member's clause.** l: the head's segment's number. -/
def K7MemberKeeps (tl : HTailF2) (V l : Nat) (s s' : S) : Prop :=
  ∃ m, H1Keeps tl V s m ∧ keepsOpened l m s'

/-! ## 2 The payers -/

theorem k7Keeps_of_decide (l V : Nat) {t m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (Reply.blockAt l V).decide t rs gs = .ok m) :
    K7Keeps V t m :=
  VerifiableInference.Desc.Kinds.Head.Law.Came.reply_record l V h

/-- From a return of the lot's own decision. -/
theorem h1Keeps_of_decide {G : Ground} {x : Block S Unit} (hx : x ∈ h1Own G) {s m : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : x.decide s rs gs = .ok m)
    (hm : m.failed = none) : H1Keeps G.W.H.tl G.W.hS.V s m := by
  unfold h1Own at hx
  obtain rfl := List.mem_singleton.1 hx
  generalize hf : (Block.guarded sameReply (fun _ => false)
    ({ (VerifiableInference.Desc.roundlessBlock "H:1" 1 (some (G.built.size - 1)) 1
        (headFrontQ G.W.H.tl) : Block S Unit) with place := (P4.k7Core G).place })) = front at h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind
      fun s1 => (P4.k7Core G).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings)) =
        .ok m := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e =>
    rw [hp] at h'
    cases h'
  | ok t =>
    rw [hp] at h'
    rw [← hf] at hp
    exact ⟨hm, t, h1Front _ _ _ _ _ _ _ _ _ _ hp, k7Keeps_of_decide _ _ h'⟩

/-- **From the lot's own sub-protocol's accepting step.** -/
theorem h1Keeps_of_step {G : Ground} {x : Block S Unit} (hx : x ∈ h1Own G) {ft : Nat} {s m : S}
    (h : StepYes ft (x.retype : Block S Cl) s m) (hm : m.failed = none) :
    H1Keeps G.W.H.tl G.W.hS.V s m := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  exact h1Keeps_of_decide hx (show x.decide s rs gs = .ok m from e) hm

/-- **FROM THE WHOLE MEMBER's ACCEPTING STEP.** -/
theorem k7MemberKeeps_of_step {Z : Pub} {G : Ground} {l : Nat} {b : Block S Cl} {a : Place}
    {x : Block S Unit} (hx : x ∈ h1Own G) (hj : IM.Joined Z l b x.retype a) {ft : Nat} {s s' : S}
    (h : StepYes ft b s s') : K7MemberKeeps G.W.H.tl G.W.hS.V l s s' :=
  keeps_joined_opened hj ft (H1Keeps G.W.H.tl G.W.hS.V)
    (fun _ _ g gm => h1Keeps_of_step hx g gm) s s' h

/-! ## 3 What readers get -/

section
variable {tl : HTailF2} {V l : Nat} {s m s' : S}

/-- A token is laid into the reply's seat, where none lay. -/
theorem H1Keeps.reply (h : H1Keeps tl V s m) :
    s.out.reply = none ∧ ∃ x, isToken V x = true ∧ m.out.reply = some x := by
  obtain ⟨-, t, ht, o, x, -, -, hn, hx, rfl⟩ := h
  rw [(headFrontQ_rest ht).2.2.2.2.2.1] at hn
  exact ⟨hn, x, hx, rfl⟩

/-- What was put out, but for the reply's seat. -/
theorem H1Keeps.out (h : H1Keeps tl V s m) : ∃ x, m.out = { s.out with reply := some x } := by
  obtain ⟨-, t, ht, o, x, -, -, -, -, rfl⟩ := h
  exact ⟨x, by rw [← (headFrontQ_rest ht).2.2.2.2.2.1]⟩

/-- The statement: one fresh group more. -/
theorem H1Keeps.st (h : H1Keeps tl V s m) :
    m.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode := by
  obtain ⟨-, t, ht, o, x, -, -, -, -, rfl⟩ := h
  exact (headFrontQ_st ht : t.st = _)

/-- The chain stands in the head's segment, not yet opened. -/
theorem H1Keeps.here (h : H1Keeps tl V s m) : ∃ o, m.here = .head o ∧ o.opened = false := by
  obtain ⟨-, t, -, o, x, ho, hop, -, -, rfl⟩ := h
  exact ⟨o, ho, hop⟩

theorem K7MemberKeeps.mark (h : K7MemberKeeps tl V l s s') : s'.failed = none := by
  obtain ⟨m, -, h2⟩ := h
  exact h2.1

theorem K7MemberKeeps.reply (h : K7MemberKeeps tl V l s s') :
    s.out.reply = none ∧ ∃ x, isToken V x = true ∧ s'.out.reply = some x := by
  obtain ⟨m, h1, h2⟩ := h
  obtain ⟨hn, x, hx, e⟩ := h1.reply
  exact ⟨hn, x, hx, by rw [keepsOpened_reply h2, e]⟩

/-- The pile is as it was. -/
theorem K7MemberKeeps.pending (h : K7MemberKeeps tl V l s s') :
    s'.out.pending = s.out.pending := by
  obtain ⟨m, h1, h2⟩ := h
  obtain ⟨x, e⟩ := h1.out
  rw [keepsOpened_pending h2, e]

/-- The statement: one fresh group more. -/
theorem K7MemberKeeps.st (h : K7MemberKeeps tl V l s s') :
    s'.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode := by
  obtain ⟨m, h1, h2⟩ := h
  rw [keepsOpened_st h2, h1.st]

/-- The number of the index masks' message is as it was: at every segment but the first. -/
theorem K7MemberKeeps.indexMasks (h : K7MemberKeeps tl V l s s') (hl : l ≠ 0) :
    s'.out.indexMasks = s.out.indexMasks := by
  obtain ⟨m, h1, h2⟩ := h
  obtain ⟨x, e⟩ := h1.out
  rw [keepsOpened_out h2 hl, e]

/-- **HOW THE ROOM PASSES, 1**: that message's ledger is as it was. -/
theorem K7MemberKeeps.ledger (h : K7MemberKeeps tl V l s s') (hl : l ≠ 0) :
    Johnson.Desc.First.Walk.Law.ledgerAt s' = Johnson.Desc.First.Walk.Law.ledgerAt s := by
  unfold Johnson.Desc.First.Walk.Law.ledgerAt
  rw [h.indexMasks hl, h.st]
  rfl

/-- **HOW THE ROOM PASSES, 2**: no group gains that message: the one fresh group has no member. -/
theorem K7MemberKeeps.outOfGroups (h : K7MemberKeeps tl V l s s') (hl : l ≠ 0)
    (ho : P1L20.outOfGroupsB s = true) : P1L20.outOfGroupsB s' = true := by
  rw [P1L20.outOfGroupsB_iff] at ho ⊢
  intro Gr hG
  rw [h.st] at hG
  rw [h.indexMasks hl]
  rcases Array.mem_push.1 hG with h1 | rfl
  · exact ho Gr h1
  · simp [VerifiableInference.Desc.First.K2.freshGroup]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.k7Keeps_of_decide
#print axioms ProofFile.Honest.h1Keeps_of_decide
#print axioms ProofFile.Honest.h1Keeps_of_step
#print axioms ProofFile.Honest.k7MemberKeeps_of_step
#print axioms ProofFile.Honest.H1Keeps.reply
#print axioms ProofFile.Honest.H1Keeps.out
#print axioms ProofFile.Honest.H1Keeps.st
#print axioms ProofFile.Honest.H1Keeps.here
#print axioms ProofFile.Honest.K7MemberKeeps.mark
#print axioms ProofFile.Honest.K7MemberKeeps.reply
#print axioms ProofFile.Honest.K7MemberKeeps.pending
#print axioms ProofFile.Honest.K7MemberKeeps.st
#print axioms ProofFile.Honest.K7MemberKeeps.indexMasks
#print axioms ProofFile.Honest.K7MemberKeeps.ledger
#print axioms ProofFile.Honest.K7MemberKeeps.outOfGroups

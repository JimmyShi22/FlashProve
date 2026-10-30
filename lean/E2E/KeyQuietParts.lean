--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyQuietParts.lean: THE STEPS WITHOUT A ROUND THAT ARE JOINED TO A SENDING OR TO THE BATCHING IN
THE KEY FILE's FIRST CHAIN RETURN, FROM NAMED CLAUSES ON THE STATE IN FRONT OF THEM, and what they
return. Four sub-protocols of that chain are made of a sending (or the batching) and such steps,
under one place: "idx.1.send", "msg.1.send", "batt.1.batt", "w.1.send". The steps have no part of a
prover. Statements and proofs, by unfolding. Steps of the verifier's: NOTHING IS SHOWN OF ANY
PROVER: no completeness, nothing on what a view shows.

What is shown.
  `newGroupP_some`: the ground's function for a new group returns, and what, where its list of named
    clauses holds.
  `Opens one s o x`: ALL THAT "the ranges' group" ASKS (behind the own message's sending), as
    clauses on the state s in front; o: the index-mask message; x: the lookups' own message. On
    public values and the carried codes: the parameters are admitted; the own message's answers are
    the written ones; the group's two codes are there and fit. On s: the index-mask message is
    there, sampled, with mask rows alone; the sending has left the own message's number, and it is
    the parameters'; that message is there, sampled, with the parameters' two codes where it has
    such rows.
  `stGrouped`, `stOpened`: the statement behind: one group more, at the next free number, with the
    own message as its one member.
  **`openRangesGroup_passes`**: under `Opens` the step returns: that statement; the group's number;
    the number of the first fold's mask where masks are sent ahead.
  `Piles keysOf one s o l`: ALL THAT "the rows on the table" ASKS (in front of the batching): no row
    is laid yet; a list of claims for each lookup; each list has a claim for each part, and each
    claim passes the three tests of E2E/KeyPasses.lean's `Passes`; the index-mask message has a
    ledger of mask entries, which has handed out just the lookups' entries.
  **`layPile_passes`**: under `Piles` the step returns a state that differs in the rows on the table
    alone.

The two other steps ask one thing each: "the index-mask message's number": the sending has left a
number; "what is announced": the state announces what the written rounds say. They are not restated.

Limits.
- `Opens` and `Piles` restate the steps' own tests, carried to the state in front where a step's
  later tests read what its earlier calls have written. That a run's states meet them is not shown.
- What rows `layPile` lays is not said here.
- A member of `Opens`: E2E/KeyFirstMembers.lean. A member of `Piles`: E2E/KeyPileMember.lean.


-/
import E2E.KeyPasses
import E2E.KeyTakeOver
import Johnson.Desc.Key.One

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Key (ChainState openRangesGroup layPile tableRowsOf)

theorem newGroupP_some {L : Type} (d : DState L) (code maskCode : Nat)
    (h : ok (newGroupL d.st code maskCode) = true) :
    newGroupP d code maskCode =
      some (d.st.groups.size,
        { d with st := VerifiableInference.Desc.Ground.withGroup d.st code maskCode }) := by
  unfold newGroupP
  rw [if_pos h]

/-! ## "The ranges' group" -/

/-- **All that the step asks**, on the state in front. o: the index-mask message; x: the lookups'
own message. -/
structure Opens {β : Type} (one : OneTime) (s : ChainState β) (o x : OnBytes.Oracle) : Prop where
  admitted : Wf.admitted s.d.st.codes one.ranges (Wf.matrixOf one.lin) = true
  idx : s.d.st.oracles[s.idx]? = some o
  idxForm : (o.sampled && o.shape.mainRows == 0) = true
  answers : (one.ranges.message.shape.answers == one.given.plan.samples) = true
  sent : s.sent[0]? = some one.ranges.messageId
  codes : ok (newGroupL s.d.st one.ranges.message.shape.code one.ranges.message.shape.maskCode) =
    true
  own : s.d.st.oracles[one.ranges.messageId]? = some x
  sampled : x.sampled = true
  mainCode : x.shape.mainRows = 0 ∨ x.shape.code = one.ranges.message.shape.code
  maskCode : x.shape.maskRows = 0 ∨ x.shape.maskCode = one.ranges.message.shape.maskCode

/-- The statement with the new group, which has no member. -/
def stGrouped {β : Type} (one : OneTime) (s : ChainState β) : Statement :=
  VerifiableInference.Desc.Ground.withGroup s.d.st one.ranges.message.shape.code
    one.ranges.message.shape.maskCode

/-- **The statement behind.** -/
def stOpened {β : Type} (one : OneTime) (s : ChainState β) : Statement :=
  withMessageInGroup (stGrouped one s) s.d.st.groups.size one.ranges.messageId false
    { code := one.ranges.message.shape.code, maskCode := one.ranges.message.shape.maskCode }

/-- **Under them the step returns.** -/
theorem openRangesGroup_passes {β : Type} (one : OneTime) (s : ChainState β)
    (o x : OnBytes.Oracle) (h : Opens one s o x) :
    openRangesGroup one s = .ok { s with
      d := { s.d with st := stOpened one s }, grp := s.d.st.groups.size
      rider := if one.ranges.choice.masksRide then s.sent[1]? else none } := by
  have e₁ : newGroupP s.d one.ranges.message.shape.code one.ranges.message.shape.maskCode =
      some (s.d.st.groups.size, { s.d with st := stGrouped one s }) :=
    newGroupP_some s.d _ _ h.codes
  have hG : (stGrouped one s).groups[s.d.st.groups.size]? =
      some { code := one.ranges.message.shape.code
             maskCode := one.ranges.message.shape.maskCode } := by
    show (s.d.st.groups.push _)[s.d.st.groups.size]? = _
    rw [Array.getElem?_push, if_pos rfl]
  have hx : (stGrouped one s).oracles[one.ranges.messageId]? = some x := h.own
  have hj : ok (joinL (stGrouped one s) s.d.st.groups.size one.ranges.messageId false) = true := by
    refine ok_of_all _ fun c hc => ?_
    unfold joinL at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, hG, hx] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact h.sampled
    · rfl
    · rcases h.mainCode with e | e
      · simp [has, e]
      · simp [has, e]
    · rcases h.maskCode with e | e
      · simp [has, e]
      · simp [has, e]
    · simp [has]
    · simp [has]
  have e₂ := joinP_some { s.d with st := stGrouped one s } s.d.st.groups.size
    one.ranges.messageId false _ hj hG
  have a1 : (one.ranges.messageId == one.ranges.messageId) = true := beq_self_eq_true _
  unfold openRangesGroup
  simp only [h.admitted, h.idx, h.idxForm, h.answers, h.sent, a1, e₁, e₂, named, need, bind,
    Except.bind, pure, Except.pure, if_true]
  rfl

/-! ## "The rows on the table" -/

/-- **All that the step asks.** o: the index-mask message; l: its ledger of mask entries. -/
structure Piles {β : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (s : ChainState β)
    (o : OnBytes.Oracle) (l : Ledger) : Prop where
  fresh : s.pile.isEmpty = true
  lists : one.ranges.lookups.length = (keysOf s.base).length
  parts : ∀ y ∈ zipT one.ranges.lookups (keysOf s.base), y.1.parts.length = y.2.length
  passes : ∀ y ∈ zipT one.ranges.lookups (keysOf s.base), ∀ z ∈ y.1.parts.zip y.2,
    Passes (Wf.matrixOf one.lin) z.1 z.2 = true
  idx : s.d.st.oracles[s.idx]? = some o
  ledger : o.ledger = some l
  count : (l.left + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) ==
    Send.freeMaskEntries o.shape.maskRows (s.d.st.codes.mask.getD o.shape.maskCode default).ell
      o.shape.answers) = true

/-- **Under them the step returns a state that differs in the rows on the table alone.** -/
theorem layPile_passes {β : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime)
    (s : ChainState β) (o : OnBytes.Oracle) (l : Ledger) (h : Piles keysOf one s o l) :
    ∃ rows, layPile keysOf one s = .ok { s with pile := rows } := by
  have hr : ((zipT one.ranges.lookups (keysOf s.base)).mapM fun y =>
      tableRowsOf (Wf.matrixOf one.lin) y.1 y.2).isSome = true :=
    mapM_isSome _ _ fun y hy =>
      tableRowsOf_of_passes (Wf.matrixOf one.lin) y.1 y.2 (h.parts y hy) (h.passes y hy)
  obtain ⟨rows, hrows⟩ := Option.isSome_iff_exists.1 hr
  have a2 : (one.ranges.lookups.length == (keysOf s.base).length) = true := beq_iff_eq.2 h.lists
  refine ⟨rows.flatten, ?_⟩
  unfold layPile
  simp only [h.fresh, a2, hrows, h.idx, h.ledger, h.count, named, need, bind, Except.bind, pure,
    Except.pure, if_true]

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.newGroupP_some
#print axioms AtPublicFiles.AtFiles.openRangesGroup_passes
#print axioms AtPublicFiles.AtFiles.layPile_passes

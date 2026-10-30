-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LedgerAt.lean: THE LEDGER ACROSS AN ACCEPT OF THE PIECE OF THE IOP AS
WRITTEN IN LEAN THAT
HOLDS THE OUTPUT HEAD'S SEATED CONSTANT: it is a later one, with as many slots; so two things that
the head's bill asks behind the sub-protocol.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  later_at_piece: the ledger behind an accept of the piece is later than the ledger in front (by

      blockAt_later, through Law/K6RecordAt.lean's below_yes_seated).
  lookHeard_behind: what the lookup heard is left as it was (lookHeard_leaves).
  fork_behind: behind an accept a ledger is open.
  ledgerB_behind: the table's files' test ledgerB accepts behind the sub-protocol, where K6After
      holds:
      THE PUBLIC ITEM "ledger 24" IS KEPT.
  freeAbove_behind: those files' test freeAboveB n accepts behind the sub-protocol where it and
      ledgerB
      accept in front: THE PUBLIC ITEM "freeAbove 24" IS KEPT (Law/GrowsAt.lean:
      blockOf_freeAbove: the hearings fill slots in order from the next free number).
  mf_le_behind: the ledger's list of factors behind the sub-protocol is as long as the ledger in
      front has
      slots, and it has as many slots: so, where the ledger in front has the plan's number of slots
      (the public item
      "freeAbove 24", which the promise's table asks in front of this sub-protocol, says so at the
          composed
      filling): RecordRest's clause on the ledger's length.

Every letter under "there is": fork_behind: F1: pinned by the verifier's state.
What it does not say. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6RecordAt
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.GrowsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Frame MsgT)

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **A later ledger.** -/
theorem later_at_piece (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    Later ((seatAt Wp.hS (readsOf Wp)).ledger a.1.2) ((seatAt Wp.hS (readsOf Wp)).ledger b.1.2) :=
        by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp h6
  have hr : readsOf Wp = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  rw [hr]
  exact blockAt_later Wp.hS iU3 _ l a.1.2 b.1.2 rs gs hd'

/-- **What the lookup heard is left as it was.** -/
theorem lookHeard_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    b.1.2.lookHeard? = a.1.2.lookHeard? := by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  obtain ⟨iU3, _, hbb⟩ := Option.map_eq_some_iff.mp h6
  subst hbb
  exact Came.lookHeard_leaves Wp.hS iU3 _ l a.1.2 rs gs b.1.2 hd'

/-- **Behind an accept a ledger is open.** -/
theorem fork_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    ∃ F1, b.1.2.fork? = some F1 := by
  obtain ⟨o, F1, X, Q, _, ho, _, e⟩ := k6_behind H a b τ h
  refine ⟨F1, ?_⟩
  rw [e]
  show (if o.opened then some F1 else none) = some F1
  rw [ho]
  rfl

/-- **The public item "ledger" is kept.** -/
theorem ledgerB_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hA : K6After Wp b.1.2) : First.ledgerB b.1.2 = true := by
  obtain ⟨F1, hF⟩ := fork_behind H a b τ h
  have hW : WellLaid ((seatAt Wp.hS (readsOf Wp)).ledger b.1.2) := hA.2.1
  have e : (seatAt Wp.hS (readsOf Wp)).ledger b.1.2 = F1 := by
    show b.1.2.fork?.getD {} = F1
    rw [hF]
    rfl
  rw [e] at hW
  unfold First.ledgerB
  rw [hF]
  show (F1.vp.size == F1.ns && F1.mf.size == F1.ns && F1.gotF.size == F1.ns) = true
  rw [hW.1, hW.2.1, hW.2.2]
  simp

/-- **The public item "freeAbove" is kept.** -/
theorem freeAbove_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) (n : ℕ)
    (hL : First.ledgerB a.1.2 = true) (hf : First.freeAboveB n a.1.2 = true) :
    First.freeAboveB n b.1.2 = true := by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  exact (blockOf_freeAbove Wp l b6 h6 n a.1.2 b.1.2 rs gs hd' hL hf).2

/-- **The ledger's length behind the sub-protocol.** -/
theorem mf_le_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hA : K6After Wp b.1.2) (F : Fork) (hF : a.1.2.fork? = some F) (aK : K9.Part)
    (hK : K9.segAt? b.1.2 = some aK) : aK.F.mf.size = F.ns ∧ aK.F.ns = F.ns := by
  obtain ⟨F1, hF1⟩ := fork_behind H a b τ h
  have hL := later_at_piece H a b τ h
  have hW : WellLaid ((seatAt Wp.hS (readsOf Wp)).ledger b.1.2) := hA.2.1
  have e1 : (seatAt Wp.hS (readsOf Wp)).ledger b.1.2 = F1 := by
    show b.1.2.fork?.getD {} = F1
    rw [hF1]
    rfl
  have e0 : (seatAt Wp.hS (readsOf Wp)).ledger a.1.2 = F := by
    show a.1.2.fork?.getD {} = F
    rw [hF]
    rfl
  rw [e1] at hW hL
  rw [e0] at hL
  have eK : aK.F = F1 := by
    unfold K9.segAt? at hK
    rw [hF1] at hK
    cases hl : b.1.2.link? with
    | none =>
      rw [hl] at hK
      cases hK
    | some L =>
      rw [hl] at hK
      cases ht : b.1.2.tl? with
      | none =>
        rw [ht] at hK
        cases hK
      | some tl =>
        rw [ht] at hK
        have := Option.some.inj hK
        rw [← this]
  rw [eK, hW.2.2, hL.ns]
  exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.later_at_piece
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fork_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.lookHeard_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.ledgerB_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.mf_le_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.freeAbove_behind

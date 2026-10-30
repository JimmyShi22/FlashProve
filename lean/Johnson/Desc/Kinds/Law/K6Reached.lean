-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Reached.lean: WHAT THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS TAKES OF THE
VERIFIER'S STATE IN FRONT OF THESE ROUNDS FROM "REACHED" ALONE: one structure, a field a fact; and,
for the three sub-protocols that stand in front of these rounds in the head's segment, one lemma
each ON ONE ACCEPT: the first makes the structure, the two others keep it. Statements and proofs.

Why. Two facts on the state in front of these rounds are said by no clause of the table's promise at
that border (no public test that is open there reads the two fields of the head's part of the
state). They hold because the step that enters the head's segment lays both fields empty and nothing
in front of these rounds writes them. Only this kind's laws spend them: so they are this kind's own
lemma over the condition "reached", and stand in no list that other authors share.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold).
  K6Reached s      noTab: the state stands in the head's segment, and the tables of the reads are
      not laid (noTablesB s = true) · wo: the merge has not laid its end value (K9.mergeOf s =
      none).
  noMerge_front    behind an accept of the step that enters the head's segment: K9.mergeOf = none.
  **made_H1**      behind an accept of the segment's first sub-protocol (any front that accepts only
      as that step does, then the reply's sub-protocol): K6Reached.
  **kept_H2**      an accept of the second (the code switch, then the quiet step that opens the
      segment) keeps it.
  **kept_H3**      an accept of the third (the lookup argument on the head's calls, in the form with
      the hearing exchanged, where its test on the list of rounds accepts) keeps it.
The half on the tables is other files': Law/TablesNotYet.lean,
Law/TablesNotYetCalls.lean, Johnson/Top/H0/Tw/K2C/HeadRest.lean: called.

Every letter under "there is": none in the tops.
What it does not say. NOTHING ON "REACHED": no lemma here names it: that a reached state at the
border in front of these rounds is the outcome of three such accepts is another file's. Nothing on
soundness.
-/
import Johnson.Desc.Kinds.Law.HeadRidesSays
import Johnson.Desc.Kinds.Law.TablesNotYetCalls
import Johnson.Desc.Kinds.Law.ReplyRest
import Johnson.Top.H0.Tw.K2C.HeadRest
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (headFrontQ codeSwitchKind headOpened P2 HeadPar placeH2_rest
  placeH2_noTables)
open VerifiableInference.OnPublicFiles (TurnsCalls k3_calls_turns)

/-- **What is taken from "reached" alone.** -/
structure K6Reached (s : S) : Prop where
  /-- the state stands in the head's segment, and the tables of the reads are not laid -/
  noTab : noTablesB s = true
  /-- the merge has not laid its end value -/
  wo : K9.mergeOf s = none

/-- The reader of the merge's end value reads where the chain stands alone. -/
theorem mergeOf_here {s t : S} (h : t.here = s.here) : K9.mergeOf t = K9.mergeOf s := by
  unfold K9.mergeOf
  rw [h]

/-- **MADE** behind an accept of the step that enters the head's segment. -/
theorem noMerge_front {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    K9.mergeOf s' = none := by
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
          have e2 : ∃ a, s₁.here = .head a ∧ a.wo = none := by
            rw [e1]
            unfold S.enterHead
            rw [if_pos hat]
            exact ⟨_, rfl, rfl⟩
          obtain ⟨a, e2, hw⟩ := e2
          have h' : (match s₁.here with
            | .head a => Except.ok { s₁ with st := x.st, here := .head { a with fr := x.f } }
            | _ => Except.error "B3: the record has not entered the head's link") = .ok s' := h
          rw [e2] at h'
          obtain rfl := Except.ok.inj h'
          show (a.wo.map (·.sFv)) = none
          rw [hw]
          rfl

/-- **MADE by the segment's first sub-protocol.** -/
theorem made_H1 (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      K6Reached t := by
  intro s rs gs t h
  obtain ⟨s0, h0, _, _, _, _, _, _, hh, _⟩ := place_rest W l name front tl hfront s rs gs t h
  exact ⟨(noTablesB_iff t).2 (joined_noTables W l name front
      (fun s rs gs s1 e => front_noTables (hfront s rs gs s1 e)) s rs gs t h),
    (mergeOf_here hh).trans (noMerge_front h0)⟩

/-- **KEPT by the second.** -/
theorem kept_H2 {p : P2} {n : String} {HP : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place HP)).decide s rs gs = .ok s')
    (Z : K6Reached s) : K6Reached s' := by
  obtain ⟨o, ho, ht⟩ := (noTablesB_iff s).1 Z.noTab
  obtain ⟨b, hb, _, _, _, _, _, hw, _⟩ := placeH2_rest h ho
  refine ⟨(noTablesB_iff s').2 (placeH2_noTables h ⟨o, ho, ht⟩), ?_⟩
  have e := Z.wo
  unfold K9.mergeOf at e ⊢
  rw [ho] at e
  rw [hb]
  show (b.wo.map (·.sFv)) = none
  rw [hw]
  exact e

/-- **KEPT by the third.** -/
theorem kept_H3 {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64)))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before p guests).planOk =
      true)
    (h : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs
      cols = .ok s') (Z : K6Reached s) : K6Reached s' := by
  have hd := Desc.K3.Law.blockVia_decide hplan h
  refine ⟨(noTablesB_iff s').2 (calls_noTables claim piece laid before p guests s s' rs cols hd
    ((noTablesB_iff s).1 Z.noTab)), ?_⟩
  obtain ⟨o, ho, _⟩ := (noTablesB_iff s).1 Z.noTab
  have e := Z.wo
  unfold K9.mergeOf at e ⊢
  rw [ho] at e
  rcases (k3_calls_turns claim piece laid before p guests s s' rs cols hd).part with
    ⟨a, _, _, ha, _⟩ | ⟨a, _, _, ha, _⟩ | ⟨a, F, g, ha, _, x', hs'⟩
  · rw [ho] at ha
    cases ha
  · rw [ho] at ha
    cases ha
  · rw [ho] at ha
    cases ha
    rw [hs']
    exact e

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.made_H1
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.kept_H2
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.kept_H3
